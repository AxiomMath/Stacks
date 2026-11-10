module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartStalkRings

/-!
# The four local rings of a chart, as localizations of its coordinate rings

Let `ch` be a Cartesian affine-open chart for a base-change square of schemes and `y` a point of
`Spec 𝒪_{X'}(U')`, with image `x'` in `X'`. The four local rings of the square of schemes at `x'`
— `𝒪_{S, f(g' x')}`, `𝒪_{X, g' x'}`, `𝒪_{S', f' x'}`, `𝒪_{X', x'}` — are identified with the
local rings of the spectra of the chart's coordinate rings by the comparisons
`AlgebraicGeometry.BaseChangeChart.stalkCompR`, `stalkCompA`, `stalkCompR'` and `stalkCompA'`.
Composing the germ maps with those identifications makes each of the four local rings of the
*schemes* a localization of the corresponding coordinate ring, and carries the chart's square of
rings to the square of stalk maps.

This is what puts the affine reduction of Stacks 0DJ8 and the pointwise condition (1) over one
and the same square of rings: the comparison of Stacks 065Z across the cube of localizations,
`RingTheory.TorIndependence.squareComparison_cube`, asks for exactly these four ring maps and
four compatibilities, and asks for them at the local rings of the schemes rather than at the
local rings of the spectra, which is where `AlgebraicGeometry.baseChangeCohomologyMap` lives.

## Main definitions

* `AlgebraicGeometry.BaseChangeChart.toStalkR`, `toStalkA`, `toStalkR'`, `toStalkA'`: the four
  ring maps `𝒪_S(V) → 𝒪_{S, f(g' x')}`, `𝒪_X(U) → 𝒪_{X, g' x'}`,
  `𝒪_{S'}(V') → 𝒪_{S', f' x'}`, `𝒪_{X'}(U') → 𝒪_{X', x'}`.

## Main results

* `AlgebraicGeometry.stalkCongr_specGermRingHom`: the germ maps of two inseparable points of
  `Spec A` agree through the specialization isomorphism.
* `AlgebraicGeometry.BaseChangeChart.toStalkA_a`, `toStalkA'_c`, `toStalkA'_d`, `toStalkR'_b`:
  the four compatibilities, saying that the four maps above carry the chart's square of
  coordinate rings to the square of stalk maps of the square of schemes.
* `AlgebraicGeometry.BaseChangeChart.isLocalization_toStalkR`,
  `isLocalization_toStalkA`, `isLocalization_toStalkR'`: three of the four maps exhibit the local
  ring of the scheme as the localization of the coordinate ring at the prime of the point. These
  are the localization hypotheses the source half of the cube consumes.
* `AlgebraicGeometry.BaseChangeChart.flat_toStalkA`, `flat_toStalkR'`: `𝒪_X(U) → 𝒪_{X, g' x'}`
  and `𝒪_{S'}(V') → 𝒪_{S', f' x'}` are flat, being such localizations.

## Implementation notes

The map at `U'` takes the inverse of the germ comparison as data — a ring map `ε'` and the two
equations inverting it — rather than as `CategoryTheory.inv`, matching
`AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso` and the hypothesis `hsource` of
`AlgebraicGeometry.baseChange_tfae_of_sourceBridge`; the other three comparisons are invertible
with no hypothesis on the chart, so those take their inverses from `CategoryTheory.inv`.

Each compatibility is proved by applying the comparison at `U'`, resp. at `U`, to both sides:
that comparison is injective, and after it the equation is the germ naturality of
`AlgebraicGeometry.specGermRingHom_stalkMap` together with one of the four compatibilities
`AlgebraicGeometry.BaseChangeChart.stalkCompR_stalkMap_f`, `stalkCompA_stalkMap_g'`,
`stalkCompR'_stalkMap_f'` and `stalkCompR_baseStalkMap`. The compatibility for `ch.b` needs in
addition that the germ maps of the two spellings of the point of `Spec 𝒪_S(V)` agree, which is
`stalkCongr_specGermRingHom`.

Nothing below is a clause of Stacks 0DJ8: this is the dictionary between the ring-theoretic and
the geometric readings of the square.

## References

* [Stacks Project, Tag 01HR](https://stacks.math.columbia.edu/tag/01HR)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Two elementary facts about isomorphisms of commutative rings -/

/-- An isomorphism of commutative rings is undone by its inverse, on elements. -/
public theorem commRingCatIso_inv_hom_apply {B C : CommRingCat.{u}} (ε : B ≅ C) (x : B) :
    ε.inv.hom (ε.hom.hom x) = x := by simp

/-- An isomorphism of commutative rings undoes its inverse, on elements. -/
public theorem commRingCatIso_hom_inv_apply {B C : CommRingCat.{u}} (ε : B ≅ C) (z : C) :
    ε.hom.hom (ε.inv.hom z) = z := by simp

/-- An isomorphism of commutative rings is injective on elements. -/
public theorem commRingCatIso_injective {B C : CommRingCat.{u}} (ε : B ≅ C) :
    Function.Injective (fun x : B => ε.hom.hom x) :=
  Function.LeftInverse.injective (commRingCatIso_inv_hom_apply ε)

/-! ### Germs and the specialization isomorphism -/

/-- **The germ maps of two inseparable points agree through the specialization isomorphism.**
The germ of a global section at `z`, carried along the specialization isomorphism of `z` and
`z'`, is its germ at `z'`. -/
public theorem stalkCongr_specGermRingHom (A : CommRingCat.{u}) {z z' : Spec A}
    (h : Inseparable z z') :
    (((Spec A).presheaf.stalkCongr h).hom).hom.comp (specGermRingHom A z) =
      specGermRingHom A z' := by
  have h0 : (((Spec A).presheaf.stalkCongr h).hom).hom.comp
      ((Spec A).presheaf.germ ⊤ z trivial).hom =
      ((Spec A).presheaf.germ ⊤ z' trivial).hom := by
    have hg := congrArg CommRingCat.Hom.hom
      (TopCat.Presheaf.germ_stalkSpecializes (Spec A).presheaf (U := ⊤) (y := z) trivial h.ge)
    simpa only [CommRingCat.hom_comp, TopCat.Presheaf.stalkCongr_hom] using hg
  dsimp only [specGermRingHom]
  rw [← RingHom.comp_assoc, h0]

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}
  (ch : BaseChangeChart f g f' g') (y : Spec ch.A')

/-! ### The four local rings of the schemes, as algebras over the coordinate rings -/

/-- The comparison at `U`, as an isomorphism. -/
public def stalkCompAIso : X.presheaf.stalk (g' (ch.incU' y)) ≅
    (Spec ch.A).presheaf.stalk (Spec.map ch.c y) :=
  haveI := ch.isIso_stalkCompA y
  asIso (ch.stalkCompA y)

/-- The comparison at `V'`, as an isomorphism. -/
public def stalkCompR'Iso : S'.presheaf.stalk (f' (ch.incU' y)) ≅
    (Spec ch.R').presheaf.stalk (Spec.map ch.d y) :=
  haveI := ch.isIso_stalkCompR' y
  asIso (ch.stalkCompR' y)

/-- The comparison at `V`, as an isomorphism. -/
public def stalkCompRIso : S.presheaf.stalk (f (g' (ch.incU' y))) ≅
    (Spec ch.R).presheaf.stalk (Spec.map ch.a (Spec.map ch.c y)) :=
  haveI := ch.isIso_stalkCompR y
  asIso (ch.stalkCompR y)

/-- **`𝒪_S(V) → 𝒪_{S, f(g' x')}`**: the germ map of `Spec 𝒪_S(V)` read through the comparison
at `V`. -/
public def toStalkR : ch.R →+* S.presheaf.stalk (f (g' (ch.incU' y))) :=
  (ch.stalkCompRIso y).inv.hom.comp
    (specGermRingHom ch.R (Spec.map ch.a (Spec.map ch.c y)))

/-- **`𝒪_X(U) → 𝒪_{X, g' x'}`**: the germ map of `Spec 𝒪_X(U)` read through the comparison
at `U`. -/
public def toStalkA : ch.A →+* X.presheaf.stalk (g' (ch.incU' y)) :=
  (ch.stalkCompAIso y).inv.hom.comp (specGermRingHom ch.A (Spec.map ch.c y))

/-- **`𝒪_{S'}(V') → 𝒪_{S', f' x'}`**: the germ map of `Spec 𝒪_{S'}(V')` read through the
comparison at `V'`. -/
public def toStalkR' : ch.R' →+* S'.presheaf.stalk (f' (ch.incU' y)) :=
  (ch.stalkCompR'Iso y).inv.hom.comp (specGermRingHom ch.R' (Spec.map ch.d y))

variable (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))

/-- **`𝒪_{X'}(U') → 𝒪_{X', x'}`**: the germ map of `Spec 𝒪_{X'}(U')` read through a given
inverse `ε'` of the comparison at `U'`. -/
public def toStalkA' : ch.A' →+* X'.presheaf.stalk (ch.incU' y) :=
  ε'.comp (specGermRingHom ch.A' y)

/-! ### The four compatibilities -/

/-- **The compatibility for `ch.a`.** The chart's `𝒪_S(V) → 𝒪_X(U)`, followed by the map to the
local ring of `X` at `g' x'`, is the stalk map of `f` precomposed with the map to the local ring
of `S` at `f (g' x')`. -/
public theorem toStalkA_a :
    (ch.toStalkA y).comp ch.a.hom =
      (f.stalkMap (g' (ch.incU' y))).hom.comp (ch.toStalkR y) := by
  refine RingHom.ext fun r => commRingCatIso_injective (ch.stalkCompAIso y) ?_
  have hgerm := DFunLike.congr_fun (specGermRingHom_stalkMap ch.a (Spec.map ch.c y)) r
  have hcomp := DFunLike.congr_fun (ch.stalkCompR_stalkMap_f y)
    ((ch.stalkCompRIso y).inv.hom (specGermRingHom ch.R (Spec.map ch.a (Spec.map ch.c y)) r))
  simp only [RingHom.comp_apply] at hgerm hcomp
  change (ch.stalkCompAIso y).hom.hom ((ch.stalkCompAIso y).inv.hom
      (specGermRingHom ch.A (Spec.map ch.c y) (ch.a.hom r))) =
    (ch.stalkCompAIso y).hom.hom ((f.stalkMap (g' (ch.incU' y))).hom
      ((ch.stalkCompRIso y).inv.hom
        (specGermRingHom ch.R (Spec.map ch.a (Spec.map ch.c y)) r)))
  refine Eq.trans (commRingCatIso_hom_inv_apply (ch.stalkCompAIso y) _) ?_
  refine Eq.trans hgerm.symm ?_
  refine Eq.trans (congrArg ((Spec.map ch.a).stalkMap (Spec.map ch.c y)).hom
    (commRingCatIso_hom_inv_apply (ch.stalkCompRIso y) _).symm) hcomp.symm

/-- **The compatibility for `ch.c`.** The chart's `𝒪_X(U) → 𝒪_{X'}(U')`, followed by the map to
the local ring of `X'` at `x'`, is the stalk map of `g'` precomposed with the map to the local
ring of `X` at `g' x'`. -/
public theorem toStalkA'_c (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z) :
    (g'.stalkMap (ch.incU' y)).hom.comp (ch.toStalkA y) =
      (ch.toStalkA' y ε').comp ch.c.hom := by
  have hinj : Function.Injective (ch.incU'.stalkMap y).hom := Function.LeftInverse.injective h₁
  refine RingHom.ext fun a => hinj ?_
  have hgerm := DFunLike.congr_fun (specGermRingHom_stalkMap ch.c y) a
  have hcomp := DFunLike.congr_fun (ch.stalkCompA_stalkMap_g' y)
    ((ch.stalkCompAIso y).inv.hom (specGermRingHom ch.A (Spec.map ch.c y) a))
  simp only [RingHom.comp_apply] at hgerm hcomp
  change (ch.incU'.stalkMap y).hom ((g'.stalkMap (ch.incU' y)).hom
      ((ch.stalkCompAIso y).inv.hom (specGermRingHom ch.A (Spec.map ch.c y) a))) =
    (ch.incU'.stalkMap y).hom (ε' (specGermRingHom ch.A' y (ch.c.hom a)))
  refine Eq.trans hcomp ?_
  refine Eq.trans (congrArg ((Spec.map ch.c).stalkMap y).hom
    (commRingCatIso_hom_inv_apply (ch.stalkCompAIso y) _)) ?_
  exact hgerm.trans (h₂ (specGermRingHom ch.A' y (ch.c.hom a))).symm

/-- **The compatibility for `ch.d`.** The chart's `𝒪_{S'}(V') → 𝒪_{X'}(U')`, followed by the map
to the local ring of `X'` at `x'`, is the stalk map of `f'` precomposed with the map to the local
ring of `S'` at `f' x'`. -/
public theorem toStalkA'_d (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z) :
    (ch.toStalkA' y ε').comp ch.d.hom =
      (f'.stalkMap (ch.incU' y)).hom.comp (ch.toStalkR' y) := by
  have hinj : Function.Injective (ch.incU'.stalkMap y).hom := Function.LeftInverse.injective h₁
  refine RingHom.ext fun r => hinj ?_
  have hgerm := DFunLike.congr_fun (specGermRingHom_stalkMap ch.d y) r
  have hcomp := DFunLike.congr_fun (ch.stalkCompR'_stalkMap_f' y)
    ((ch.stalkCompR'Iso y).inv.hom (specGermRingHom ch.R' (Spec.map ch.d y) r))
  simp only [RingHom.comp_apply] at hgerm hcomp
  change (ch.incU'.stalkMap y).hom (ε' (specGermRingHom ch.A' y (ch.d.hom r))) =
    (ch.incU'.stalkMap y).hom ((f'.stalkMap (ch.incU' y)).hom
      ((ch.stalkCompR'Iso y).inv.hom (specGermRingHom ch.R' (Spec.map ch.d y) r)))
  refine Eq.trans (h₂ (specGermRingHom ch.A' y (ch.d.hom r))) ?_
  refine Eq.trans hgerm.symm ?_
  refine Eq.trans (congrArg ((Spec.map ch.d).stalkMap y).hom
    (commRingCatIso_hom_inv_apply (ch.stalkCompR'Iso y) _).symm) hcomp.symm

/-- **The compatibility for `ch.b`.** The chart's `𝒪_S(V) → 𝒪_{S'}(V')`, followed by the map to
the local ring of `S'` at `f' x'`, is the base stalk map of the square of schemes precomposed
with the map to the local ring of `S` at `f (g' x')`. -/
public theorem toStalkR'_b (w : g' ≫ f = f' ≫ g) :
    (baseStalkMap f g f' g' w (ch.incU' y)).comp (ch.toStalkR y) =
      (ch.toStalkR' y).comp ch.b.hom := by
  have hbase : Spec.map ch.a (Spec.map ch.c y) = Spec.map ch.b (Spec.map ch.d y) :=
    congrArg (fun h : Spec ch.A' ⟶ Spec ch.R ↦ h y) ch.specW
  refine RingHom.ext fun r => commRingCatIso_injective (ch.stalkCompR'Iso y) ?_
  have hgerm := DFunLike.congr_fun (specGermRingHom_stalkMap ch.b (Spec.map ch.d y)) r
  have hcongr := DFunLike.congr_fun
    (stalkCongr_specGermRingHom ch.R (z := Spec.map ch.a (Spec.map ch.c y))
      (z' := Spec.map ch.b (Spec.map ch.d y)) (.of_eq hbase)) r
  have hcomp := DFunLike.congr_fun (ch.stalkCompR_baseStalkMap y w)
    ((ch.stalkCompRIso y).inv.hom
      (specGermRingHom ch.R (Spec.map ch.a (Spec.map ch.c y)) r))
  simp only [RingHom.comp_apply] at hgerm hcongr hcomp
  change (ch.stalkCompR'Iso y).hom.hom ((baseStalkMap f g f' g' w (ch.incU' y))
      ((ch.stalkCompRIso y).inv.hom
        (specGermRingHom ch.R (Spec.map ch.a (Spec.map ch.c y)) r))) =
    (ch.stalkCompR'Iso y).hom.hom ((ch.stalkCompR'Iso y).inv.hom
      (specGermRingHom ch.R' (Spec.map ch.d y) (ch.b.hom r)))
  refine Eq.trans hcomp ?_
  refine Eq.trans (congrArg
    (baseStalkMap (Spec.map ch.a) (Spec.map ch.b) (Spec.map ch.d) (Spec.map ch.c) ch.specW y)
    (commRingCatIso_hom_inv_apply (ch.stalkCompRIso y) _)) ?_
  refine Eq.trans ?_ (commRingCatIso_hom_inv_apply (ch.stalkCompR'Iso y) _).symm
  refine Eq.trans ?_ hgerm
  exact congrArg ((Spec.map ch.b).stalkMap (Spec.map ch.d y)).hom hcongr

/-! ### The three localizations -/

/-- The multiplicative set of `𝒪_X(U)` complementary to the prime of `g' x'`. -/
public def primeComplA : Submonoid ch.A :=
  haveI : (Spec.map ch.c y).asIdeal.IsPrime :=
    (show PrimeSpectrum (ch.A : Type u) from Spec.map ch.c y).isPrime
  (Spec.map ch.c y).asIdeal.primeCompl

/-- The multiplicative set of `𝒪_S(V)` complementary to the prime of `f (g' x')`. -/
public def primeComplR : Submonoid ch.R :=
  haveI : (Spec.map ch.a (Spec.map ch.c y)).asIdeal.IsPrime :=
    (show PrimeSpectrum (ch.R : Type u) from Spec.map ch.a (Spec.map ch.c y)).isPrime
  (Spec.map ch.a (Spec.map ch.c y)).asIdeal.primeCompl

/-- The multiplicative set of `𝒪_{S'}(V')` complementary to the prime of `f' x'`. -/
public def primeComplR' : Submonoid ch.R' :=
  haveI : (Spec.map ch.d y).asIdeal.IsPrime :=
    (show PrimeSpectrum (ch.R' : Type u) from Spec.map ch.d y).isPrime
  (Spec.map ch.d y).asIdeal.primeCompl

/-- A ring map `φ` that is the germ map of `Spec A` at `z` read through an isomorphism `e` of
`T` with the stalk is the localization at the prime of `z`. -/
private theorem isLocalization_of_stalkIso {A T : CommRingCat.{u}} (z : Spec A)
    (e : T ≅ (Spec A).presheaf.stalk z) (φ : A →+* T)
    (hφ : φ = e.inv.hom.comp (specGermRingHom A z)) (M : Submonoid A)
    (hM : M = (show PrimeSpectrum A from z).asIdeal.primeCompl) :
    letI := φ.toAlgebra
    IsLocalization M T := by
  subst hφ hM
  let := (specGermRingHom A z).toAlgebra
  let := (e.inv.hom.comp (specGermRingHom A z)).toAlgebra
  have : IsLocalization (show PrimeSpectrum A from z).asIdeal.primeCompl
      (ToType ((Spec A).presheaf.stalk z)) := isLocalization_atPrime_specGermRingHom A z
  exact IsLocalization.isLocalization_of_algEquiv _
    { e.symm.commRingCatIsoToRingEquiv with commutes' := fun _ => rfl }

/-- **`𝒪_X(U) → 𝒪_{X, g' x'}` is the localization at the prime of the point.** The germ map of
`Spec 𝒪_X(U)` is such a localization, and the comparison at `U` is an isomorphism of
`𝒪_X(U)`-algebras. -/
public theorem isLocalization_toStalkA :
    letI := (ch.toStalkA y).toAlgebra
    IsLocalization (ch.primeComplA y) (X.presheaf.stalk (g' (ch.incU' y))) :=
  isLocalization_of_stalkIso _ (ch.stalkCompAIso y) _ rfl _ rfl

/-- **`𝒪_S(V) → 𝒪_{S, f(g' x')}` is the localization at the prime of the point.** -/
public theorem isLocalization_toStalkR :
    letI := (ch.toStalkR y).toAlgebra
    IsLocalization (ch.primeComplR y) (S.presheaf.stalk (f (g' (ch.incU' y)))) :=
  isLocalization_of_stalkIso _ (ch.stalkCompRIso y) _ rfl _ rfl

/-- **`𝒪_{S'}(V') → 𝒪_{S', f' x'}` is the localization at the prime of the point.** -/
public theorem isLocalization_toStalkR' :
    letI := (ch.toStalkR' y).toAlgebra
    IsLocalization (ch.primeComplR' y) (S'.presheaf.stalk (f' (ch.incU' y))) :=
  isLocalization_of_stalkIso _ (ch.stalkCompR'Iso y) _ rfl _ rfl

/-- **`𝒪_X(U) → 𝒪_{X, g' x'}` is flat**, being a localization. -/
public theorem flat_toStalkA : (ch.toStalkA y).Flat := by
  let := (ch.toStalkA y).toAlgebra
  have := ch.isLocalization_toStalkA y
  exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (ch.primeComplA y))

/-- **`𝒪_{S'}(V') → 𝒪_{S', f' x'}` is flat**, being a localization. This is what lets cohomology
be exchanged with derived extension of scalars along it. -/
public theorem flat_toStalkR' : (ch.toStalkR' y).Flat := by
  let := (ch.toStalkR' y).toAlgebra
  have := ch.isLocalization_toStalkR' y
  exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (ch.primeComplR' y))

end BaseChangeChart

end AlgebraicGeometry

end
