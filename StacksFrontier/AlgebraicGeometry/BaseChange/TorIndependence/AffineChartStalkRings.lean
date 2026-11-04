module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChart
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedTildeStalk
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkCohomologyMap
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkLocalizationCriterion

/-!
# The stalk rings of a Cartesian affine-open chart are localizations of its coordinate rings

This module is the bookkeeping that identifies the abstract ring-theoretic localizations
appearing in the affine reduction of Stacks 0DJ8 with the geometric stalks of the schemes.

Two independent statements are proved.

*The germ map of an affine scheme is a localization.* For `A` a commutative ring and `y` a point
of `Spec A`, the germ map `A ⟶ 𝒪_{Spec A, y}` of
`StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedTildeStalk` exhibits the local
ring as the localization of `A` at the prime `y` names. Consequently the germ map is flat, and a
map of `A`-modules localizes at `y` to its base change along the germ map: a statement about
`LocalizedModule y.asIdeal.primeCompl` can be read as one about `𝒪_{Spec A, y} ⊗_A -`, which is
the ring the pointwise map of Stacks 0DJ7 is stated over.

*A chart's stalk maps are the stalk maps of its ring maps.* For a Cartesian affine-open chart
`ch` of a base-change square of schemes and a point `y` of `Spec 𝒪_{X'}(U')`, the four local
rings of the square of schemes at the four images of `y` are identified, by the stalk maps of the
chart's three open immersions, with the four local rings of `Spec` of the chart's coordinate
rings; under those identifications the four stalk maps of the square of schemes are the four
stalk maps of `Spec` of `ch.a`, `ch.b`, `ch.c`, `ch.d`. Composed with the germ naturality of
`AlgebraicGeometry.specGermRingHom_stalkMap`, this says that the four germ maps
`ch.R ⟶ 𝒪_{Spec ch.R, ·}`, `ch.A ⟶ 𝒪_{Spec ch.A, ·}`, `ch.R' ⟶ 𝒪_{Spec ch.R', ·}`,
`ch.A' ⟶ 𝒪_{Spec ch.A', y}` carry the chart's square of rings to the square of stalk rings.

## Main definitions

* `AlgebraicGeometry.BaseChangeChart.stalkCompA'`,
  `AlgebraicGeometry.BaseChangeChart.stalkCompA`,
  `AlgebraicGeometry.BaseChangeChart.stalkCompR'`,
  `AlgebraicGeometry.BaseChangeChart.stalkCompR`: the four comparison maps from the local rings
  of `X'`, `X`, `S'`, `S` to the local rings of the spectra of the chart's coordinate rings. Each
  is an isomorphism: `isIso_stalkCompA'` and friends.

## Main results

* `AlgebraicGeometry.specGermRingHom_eq_toStalk`: the germ map is Mathlib's
  `AlgebraicGeometry.StructureSheaf.toStalk`.
* `AlgebraicGeometry.isLocalization_atPrime_specGermRingHom`: **the germ map is the localization
  at the prime of the point.** `𝒪_{Spec A, y}` is the localization of `A` at `y.asIdeal`.
* `AlgebraicGeometry.flat_specGermRingHom`: the germ map is flat.
* `AlgebraicGeometry.isLocalizedModule_tensorProduct_mk_specGermRingHom`: `𝒪_{Spec A, y} ⊗_A M`
  is the localization of `M` at `y`.
* `AlgebraicGeometry.isLocalizedModule_map_specGermRingHom_eq_lTensor`: the localized map of a
  linear map, computed in `𝒪_{Spec A, y} ⊗_A -`, is the base change of that map.
* `AlgebraicGeometry.bijective_localizedModule_map_iff_bijective_lTensor`: **the replacement
  statement.** The localization of a map of `A`-modules at `y` is bijective exactly when the map
  base-changed along the germ map is bijective.
* `AlgebraicGeometry.specGermRingHom_stalkMap`: **the germ maps are natural.** The stalk map of
  `Spec φ` carries the germ map of the source ring to the germ map of the target ring composed
  with `φ`.
* `AlgebraicGeometry.stalkCongr_hom_comp`: two specialization isomorphisms of stalks compose to
  the specialization isomorphism of the composite equality of points.
* `AlgebraicGeometry.stalkMap_comp_stalkMap_of_comm`: the stalk maps of a commutative square of
  schemes commute, at a point of the initial corner.
* `AlgebraicGeometry.BaseChangeChart.stalkCompA_stalkMap_g'`,
  `AlgebraicGeometry.BaseChangeChart.stalkCompR'_stalkMap_f'`,
  `AlgebraicGeometry.BaseChangeChart.stalkCompR_stalkMap_f`,
  `AlgebraicGeometry.BaseChangeChart.stalkCompR_baseStalkMap`: **the four compatibilities.** The
  four stalk maps `g'.stalkMap`, `f'.stalkMap`, `f.stalkMap` and `baseStalkMap` of the square of
  schemes correspond, under the four comparison isomorphisms, to the stalk maps of `Spec ch.c`,
  `Spec ch.d`, `Spec ch.a` and the base stalk map of the Spec square.

## Implementation notes

The germ map of `DerivedTildeStalk` is the inverse of the global sections isomorphism followed by
the germ at `y`, while Mathlib's localization statement is over `StructureSheaf.toStalk`, the
structure map of `A` into the stalk followed by the germ. `Scheme.ΓSpecIso_inv` makes the first
factor of the two the same map, so the two germ maps are equal by `rfl`; everything else here is
read off that.

Points of `Spec A` are taken as `PrimeSpectrum A` rather than as `↥(Spec A)` in the localization
half. The two are the same type, but `y.asIdeal.IsPrime` is only found by instance search for the
first spelling, `Spec.topObj` being a plain definition; a consumer holding a point of `↥(Spec A)`
may pass it unchanged. In the chart half the spelling is reversed — `↥(Spec ·)`, because that is
what `Scheme.Hom.germ_stalkMap` and the `Scheme.Hom.stalkMap` lemmas unify against.

The four comparison maps carry a `TopCat.Presheaf.stalkCongr` factor: the chart's squares
`wU'U`, `wU'V'`, `wU`, `wV'` make the two images of a point agree only propositionally, exactly
as `AlgebraicGeometry.baseStalkMap` does for the square of schemes. The compatibilities for
`ch.c` and for `ch.d` are bare instances of one lemma, `stalkMap_comp_stalkMap_of_comm`; the ones
for `ch.a` and for `ch.b` are the two whose statement mentions a corner reached by two different
routes, so they additionally move a `stalkCongr` factor across a stalk map with
`Scheme.Hom.stalkMap_congr_point` and then merge the specialization maps with
`stalkCongr_hom_comp`.

`stalkCongr_hom_comp` is stated rather than `TopCat.Presheaf.stalkSpecializes_comp` used
directly: `x ⤳ y` unfolds to `nhds x ≤ nhds y` only at default transparency, so a `rewrite`
whose pattern is a composite of `stalkSpecializes` maps reports the motive as ill-typed, while
the same rewrite keyed on `stalkCongr` — whose argument is an `Inseparable` term as written —
goes through.

No tag attribute is placed in this file. Nothing here is a clause of Stacks 0DJ8 or of Stacks
0DJ7: it is the dictionary between the ring-theoretic and the geometric readings of their
statements, and the mathematical content it uses — the stalk of the structure sheaf is a
localization, Stacks 01HR — is Mathlib's.

## References

* [Stacks Project, Tag 01HR](https://stacks.math.columbia.edu/tag/01HR)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### The germ map of an affine scheme is the localization at the prime of the point -/

section Localization

variable (A : CommRingCat.{u}) (y : PrimeSpectrum (A : Type u))

/-- **The germ map is Mathlib's `StructureSheaf.toStalk`.** Both are the structure map of `A`
into the global sections of `Spec A` followed by the germ at `y`: the inverse of the global
sections isomorphism of Stacks 01HR *is* that structure map, by `Scheme.ΓSpecIso_inv`. -/
theorem specGermRingHom_eq_toStalk : specGermRingHom A y = (StructureSheaf.toStalk A y).hom := rfl

/-- **The germ map exhibits the local ring as the localization at the prime of the point.** For
`y` a point of `Spec A`, the germ map `A ⟶ 𝒪_{Spec A, y}` makes `𝒪_{Spec A, y}` the localization
of `A` at `y.asIdeal`. This is Mathlib's
`AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`, read over
`AlgebraicGeometry.specGermRingHom`. -/
theorem isLocalization_atPrime_specGermRingHom :
    letI := (specGermRingHom A y).toAlgebra
    IsLocalization.AtPrime (ToType ((Spec A).presheaf.stalk y)) y.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk (R := (A : Type u)) y

/-- **The germ map is flat**, being a localization. -/
theorem flat_specGermRingHom : RingHom.Flat (specGermRingHom A y) := by
  let := (specGermRingHom A y).toAlgebra
  have := isLocalization_atPrime_specGermRingHom A y
  exact RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat (ToType ((Spec A).presheaf.stalk y)) y.asIdeal.primeCompl)

variable {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- **`𝒪_{Spec A, y} ⊗_A M` is the localization of `M` at `y`.** The local ring is a localization
of `A`, and base change along a localization of rings is a localization of modules. -/
theorem isLocalizedModule_tensorProduct_mk_specGermRingHom :
    letI := (specGermRingHom A y).toAlgebra
    IsLocalizedModule y.asIdeal.primeCompl
      (TensorProduct.mk (A : Type u) (ToType ((Spec A).presheaf.stalk y)) M 1) := by
  let := (specGermRingHom A y).toAlgebra
  have := isLocalization_atPrime_specGermRingHom A y
  infer_instance

/-- **The localized map is the base-changed map.** Localizing `F : M →ₗ[A] N` at `y` inside the
base changes `𝒪_{Spec A, y} ⊗_A -` gives `𝒪_{Spec A, y} ⊗_A F`: both carry `1 ⊗ m` to
`1 ⊗ F m`, and a map out of a localization is determined by its values on the localization
map. -/
theorem isLocalizedModule_map_specGermRingHom_eq_lTensor (F : M →ₗ[A] N) :
    letI := (specGermRingHom A y).toAlgebra
    letI := isLocalization_atPrime_specGermRingHom A y
    IsLocalizedModule.map y.asIdeal.primeCompl
        (TensorProduct.mk (A : Type u) (ToType ((Spec A).presheaf.stalk y)) M 1)
        (TensorProduct.mk (A : Type u) (ToType ((Spec A).presheaf.stalk y)) N 1) F =
      LinearMap.lTensor (ToType ((Spec A).presheaf.stalk y)) F := by
  let := (specGermRingHom A y).toAlgebra
  have := isLocalization_atPrime_specGermRingHom A y
  refine IsLocalizedModule.linearMap_ext y.asIdeal.primeCompl
    (TensorProduct.mk (A : Type u) (ToType ((Spec A).presheaf.stalk y)) M 1)
    (TensorProduct.mk (A : Type u) (ToType ((Spec A).presheaf.stalk y)) N 1) ?_
  rw [IsLocalizedModule.map_comp]
  ext m
  simp

/-- **The localization of a map of `A`-modules at `y` is its base change along the germ map.**
For `F : M →ₗ[A] N` the localization `M_y → N_y` computed in `LocalizedModule` is bijective
exactly when `𝒪_{Spec A, y} ⊗_A F` is. This is what lets a criterion stated at
`LocalizedModule y.asIdeal.primeCompl` be read over the local ring `𝒪_{Spec A, y}`, which is the
ring the pointwise map of Stacks 0DJ7 is stated over. -/
theorem bijective_localizedModule_map_iff_bijective_lTensor (F : M →ₗ[A] N) :
    letI := (specGermRingHom A y).toAlgebra
    (Function.Bijective (LocalizedModule.map y.asIdeal.primeCompl F) ↔
      Function.Bijective (LinearMap.lTensor (ToType ((Spec A).presheaf.stalk y)) F)) := by
  let := (specGermRingHom A y).toAlgebra
  have := isLocalization_atPrime_specGermRingHom A y
  rw [Stacks.StalkLocalization.bijective_localizedModule_map_iff _ F
    (TensorProduct.mk (A : Type u) (ToType ((Spec A).presheaf.stalk y)) M 1)
    (TensorProduct.mk (A : Type u) (ToType ((Spec A).presheaf.stalk y)) N 1),
    isLocalizedModule_map_specGermRingHom_eq_lTensor A y F]

end Localization

/-! ### The germ maps are natural -/

/-- **The germ maps of two affine schemes are natural in the ring map.** For `φ : B ⟶ C` and `z`
a point of `Spec C`, the germ map of `B` at the image of `z` followed by the stalk map of
`Spec φ` is `φ` followed by the germ map of `C` at `z`. This is Mathlib's
`AlgebraicGeometry.stalkMap_toStalk` read over `AlgebraicGeometry.specGermRingHom`. -/
theorem specGermRingHom_stalkMap {B C : CommRingCat.{u}} (φ : B ⟶ C) (z : Spec C) :
    ((Spec.map φ).stalkMap z).hom.comp (specGermRingHom B (Spec.map φ z)) =
      (specGermRingHom C z).comp φ.hom :=
  congrArg CommRingCat.Hom.hom (stalkMap_toStalk φ z)

/-! ### The stalk square of a commutative square of schemes -/

/-- **Composing two specialization isomorphisms of stalks.** The isomorphism attached to an
equality of points composes with the one attached to the next. -/
theorem stalkCongr_hom_comp {T : TopCat.{u}} (F : T.Presheaf CommRingCat.{u}) {x y z : T}
    (e : Inseparable x y) (e' : Inseparable y z) :
    (F.stalkCongr e).hom ≫ (F.stalkCongr e').hom = (F.stalkCongr (e.trans e')).hom :=
  TopCat.Presheaf.stalkSpecializes_comp F e'.ge e.ge

/-- The two routes round a commutative square of schemes send a point to the same point. -/
private theorem apply_eq_of_comp_eq {W Y Z T : Scheme.{u}} (p : W ⟶ Y) (q : Y ⟶ T) (r : W ⟶ Z)
    (s : Z ⟶ T) (w : p ≫ q = r ≫ s) (z : W) : q (p z) = s (r z) := by
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun k : W ⟶ T => k z) w

/-- **The stalk maps of a commutative square of schemes commute.** For `p ≫ q = r ≫ s` and `z` a
point of the initial corner, going round one way and going round the other give the same ring map
out of the local ring at `q (p z)`, once that local ring is identified with the one at `s (r z)`
by the specialization isomorphism. -/
theorem stalkMap_comp_stalkMap_of_comm {W Y Z T : Scheme.{u}} (p : W ⟶ Y) (q : Y ⟶ T)
    (r : W ⟶ Z) (s : Z ⟶ T) (w : p ≫ q = r ≫ s) (z : W) :
    q.stalkMap (p z) ≫ p.stalkMap z =
      (T.presheaf.stalkCongr (.of_eq (show q (p z) = s (r z) by
        simpa only [Scheme.Hom.comp_apply] using congrArg (fun k : W ⟶ T => k z) w))).hom ≫
        s.stalkMap (r z) ≫ r.stalkMap z := by
  rw [← Scheme.Hom.stalkMap_comp, ← Scheme.Hom.stalkMap_comp,
    Scheme.Hom.stalkMap_congr_hom _ _ w z]
  rfl

/-! ### The four comparison isomorphisms of a chart, and the four compatibilities -/

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}
  (ch : BaseChangeChart f g f' g') (y : Spec ch.A')

/-- The image of `y` in `X` through `X'` is its image through `Spec ch.A`. -/
theorem apply_g'_incU' : g' (ch.incU' y) = ch.incU (Spec.map ch.c y) :=
  apply_eq_of_comp_eq _ _ _ _ ch.wU'U y

/-- The image of `y` in `S'` through `X'` is its image through `Spec ch.R'`. -/
theorem apply_f'_incU' : f' (ch.incU' y) = ch.incV' (Spec.map ch.d y) :=
  apply_eq_of_comp_eq _ _ _ _ ch.wU'V' y

/-- `U` maps into `V`, on points. -/
theorem apply_f_incU (z : Spec ch.A) : f (ch.incU z) = ch.incV (Spec.map ch.a z) :=
  apply_eq_of_comp_eq _ _ _ _ ch.wU z

/-- `V'` maps into `V`, on points. -/
theorem apply_g_incV' (z : Spec ch.R') : g (ch.incV' z) = ch.incV (Spec.map ch.b z) :=
  apply_eq_of_comp_eq _ _ _ _ ch.wV' z

/-- The image of `y` in `S` through `X'` and `X` is its image through `Spec ch.A` and
`Spec ch.R`. -/
theorem apply_f_g'_incU' :
    f (g' (ch.incU' y)) = ch.incV (Spec.map ch.a (Spec.map ch.c y)) := by
  rw [ch.apply_g'_incU' y, ch.apply_f_incU]

/-- The Spec of the chart's pushout square, as a commutative square of schemes. -/
theorem specW : Spec.map ch.c ≫ Spec.map ch.a = Spec.map ch.d ≫ Spec.map ch.b := by
  rw [← Spec.map_comp, ← Spec.map_comp, ch.isPushout.w]

/-- **The comparison at `U'`**: the stalk map of the open immersion `Spec 𝒪_{X'}(U') ⟶ X'`,
identifying `𝒪_{X', x'}` with `𝒪_{Spec ch.A', y}`. -/
def stalkCompA' : X'.presheaf.stalk (ch.incU' y) ⟶ (Spec ch.A').presheaf.stalk y :=
  ch.incU'.stalkMap y

/-- **The comparison at `U`**: `𝒪_{X, g' x'}` is `𝒪_{Spec ch.A, Spec(c) y}`, the two points
agreeing by `wU'U`. -/
def stalkCompA : X.presheaf.stalk (g' (ch.incU' y)) ⟶
    (Spec ch.A).presheaf.stalk (Spec.map ch.c y) :=
  (X.presheaf.stalkCongr (.of_eq (ch.apply_g'_incU' y))).hom ≫
    ch.incU.stalkMap (Spec.map ch.c y)

/-- **The comparison at `V'`**: `𝒪_{S', f' x'}` is `𝒪_{Spec ch.R', Spec(d) y}`, the two points
agreeing by `wU'V'`. -/
def stalkCompR' : S'.presheaf.stalk (f' (ch.incU' y)) ⟶
    (Spec ch.R').presheaf.stalk (Spec.map ch.d y) :=
  (S'.presheaf.stalkCongr (.of_eq (ch.apply_f'_incU' y))).hom ≫
    ch.incV'.stalkMap (Spec.map ch.d y)

/-- **The comparison at `V`**: `𝒪_{S, f (g' x')}` is `𝒪_{Spec ch.R, Spec(a) (Spec(c) y)}`, the
two points agreeing by `wU'U` and `wU`. -/
def stalkCompR : S.presheaf.stalk (f (g' (ch.incU' y))) ⟶
    (Spec ch.R).presheaf.stalk (Spec.map ch.a (Spec.map ch.c y)) :=
  (S.presheaf.stalkCongr (.of_eq (ch.apply_f_g'_incU' y))).hom ≫
    ch.incV.stalkMap (Spec.map ch.a (Spec.map ch.c y))

/-- The comparison at `U'` is an isomorphism: `U'` is an open of `X'` once the outer square is
cartesian, and the stalk map of an open immersion is an isomorphism. -/
theorem isIso_stalkCompA' (sq : IsPullback g' f' f g) : IsIso (ch.stalkCompA' y) := by
  have := ch.isOpenImmersion_incU' sq
  exact inferInstanceAs (IsIso (ch.incU'.stalkMap y))

/-- The comparison at `U` is an isomorphism. -/
theorem isIso_stalkCompA : IsIso (ch.stalkCompA y) := by
  have := ch.isOpenImmersion_incU
  exact inferInstanceAs (IsIso ((X.presheaf.stalkCongr _).hom ≫ _))

/-- The comparison at `V'` is an isomorphism. -/
theorem isIso_stalkCompR' : IsIso (ch.stalkCompR' y) := by
  have := ch.isOpenImmersion_incV'
  exact inferInstanceAs (IsIso ((S'.presheaf.stalkCongr _).hom ≫ _))

/-- The comparison at `V` is an isomorphism. -/
theorem isIso_stalkCompR : IsIso (ch.stalkCompR y) := by
  have := ch.isOpenImmersion_incV
  exact inferInstanceAs (IsIso ((S.presheaf.stalkCongr _).hom ≫ _))

/-- **The compatibility for `ch.c`.** The stalk map of `g' : X' ⟶ X` at `x'`, read through the
comparisons at `U` and at `U'`, is the stalk map of `Spec ch.c` at `y`. -/
theorem stalkCompA_stalkMap_g' :
    (ch.stalkCompA' y).hom.comp (g'.stalkMap (ch.incU' y)).hom =
      ((Spec.map ch.c).stalkMap y).hom.comp (ch.stalkCompA y).hom :=
  congrArg CommRingCat.Hom.hom
    (stalkMap_comp_stalkMap_of_comm ch.incU' g' (Spec.map ch.c) ch.incU ch.wU'U y)

/-- **The compatibility for `ch.d`.** The stalk map of `f' : X' ⟶ S'` at `x'`, read through the
comparisons at `V'` and at `U'`, is the stalk map of `Spec ch.d` at `y`. -/
theorem stalkCompR'_stalkMap_f' :
    (ch.stalkCompA' y).hom.comp (f'.stalkMap (ch.incU' y)).hom =
      ((Spec.map ch.d).stalkMap y).hom.comp (ch.stalkCompR' y).hom :=
  congrArg CommRingCat.Hom.hom
    (stalkMap_comp_stalkMap_of_comm ch.incU' f' (Spec.map ch.d) ch.incV' ch.wU'V' y)

/-- **The compatibility for `ch.a`.** The stalk map of `f : X ⟶ S` at `g' x'`, read through the
comparisons at `V` and at `U`, is the stalk map of `Spec ch.a` at `Spec(c) y`. -/
theorem stalkCompR_stalkMap_f :
    (ch.stalkCompA y).hom.comp (f.stalkMap (g' (ch.incU' y))).hom =
      ((Spec.map ch.a).stalkMap (Spec.map ch.c y)).hom.comp (ch.stalkCompR y).hom := by
  refine congrArg CommRingCat.Hom.hom (?_ :
    f.stalkMap (g' (ch.incU' y)) ≫ ch.stalkCompA y =
      ch.stalkCompR y ≫ (Spec.map ch.a).stalkMap (Spec.map ch.c y))
  dsimp only [stalkCompA, stalkCompR]
  simp only [Category.assoc]
  rw [Scheme.Hom.stalkMap_congr_point_assoc f (g' (ch.incU' y))
      (ch.incU (Spec.map ch.c y)) (ch.apply_g'_incU' y),
    stalkMap_comp_stalkMap_of_comm ch.incU f (Spec.map ch.a) ch.incV ch.wU
      (Spec.map ch.c y)]
  simp only [← Category.assoc]
  rw [stalkCongr_hom_comp]

/-- **The compatibility for `ch.b`.** The base stalk map of the square of schemes at `x'`, read
through the comparisons at `V` and at `V'`, is the base stalk map of the Spec of the chart's
pushout square at `y`. -/
theorem stalkCompR_baseStalkMap (w : g' ≫ f = f' ≫ g) :
    (ch.stalkCompR' y).hom.comp (baseStalkMap f g f' g' w (ch.incU' y)) =
      (baseStalkMap (Spec.map ch.a) (Spec.map ch.b) (Spec.map ch.d) (Spec.map ch.c)
        ch.specW y).comp (ch.stalkCompR y).hom := by
  have hsq : f (g' (ch.incU' y)) = g (f' (ch.incU' y)) :=
    apply_eq_of_comp_eq _ _ _ _ w _
  have hbase : Spec.map ch.a (Spec.map ch.c y) = Spec.map ch.b (Spec.map ch.d y) :=
    apply_eq_of_comp_eq _ _ _ _ ch.specW y
  refine congrArg CommRingCat.Hom.hom (?_ :
    (S.presheaf.stalkCongr (.of_eq hsq)).hom ≫
        g.stalkMap (f' (ch.incU' y)) ≫ ch.stalkCompR' y =
      ch.stalkCompR y ≫ ((Spec ch.R).presheaf.stalkCongr (.of_eq hbase)).hom ≫
        (Spec.map ch.b).stalkMap (Spec.map ch.d y))
  dsimp only [stalkCompR', stalkCompR]
  simp only [Category.assoc]
  rw [Scheme.Hom.stalkMap_congr_point_assoc g (f' (ch.incU' y))
      (ch.incV' (Spec.map ch.d y)) (ch.apply_f'_incU' y),
    stalkMap_comp_stalkMap_of_comm ch.incV' g (Spec.map ch.b) ch.incV ch.wV'
      (Spec.map ch.d y),
    Scheme.Hom.stalkMap_congr_point_assoc ch.incV (Spec.map ch.a (Spec.map ch.c y))
      (Spec.map ch.b (Spec.map ch.d y)) hbase]
  simp only [← Category.assoc]
  rw [stalkCongr_hom_comp, stalkCongr_hom_comp, stalkCongr_hom_comp]

end BaseChangeChart

end AlgebraicGeometry

end
