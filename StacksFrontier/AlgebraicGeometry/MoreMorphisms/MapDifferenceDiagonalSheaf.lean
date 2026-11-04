module

public import StacksFrontier.AlgebraicGeometry.Assembly.Basic
public import StacksFrontier.AlgebraicGeometry.Conormal.SplitCotangentFibre
public import StacksFrontier.AlgebraicGeometry.ConormalOpenFactorizations.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DiagonalConormal
public import StacksFrontier.AlgebraicGeometry.Thickenings.FirstOrderConormalInclusion

/-!
# Infinitesimal deformations of maps: the difference of two maps through the diagonal

Let `S` be a scheme, let `i : X ⟶ X'` be an immersion over `S`, let `Y` be a scheme over `S` with
structure morphism `q : Y ⟶ S`, and let `a', b' : X' ⟶ Y` be two morphisms over `S` agreeing on
`X`, say `i ≫ a' = i ≫ b' = a`. The source forms the commutative square
```
X  --i-->   X'
|           |
a           (b', a')
↓           ↓
Y  --Δ-->  Y ×_S Y
```
whose horizontal arrows are immersions, with conormal sheaves `𝒞_{X/X'}` and — by
[Stacks Project, Tag 08S2] — `Ω_{Y/S}`. Reading the canonical map of [Stacks Project, Tag 01R4]
off that square gives `θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}`. **This file proves that `θ` and the
derivation `D` of [Stacks Project, Tag 04FG] are related by Equation
[Stacks Project, Tag 04BV], `D = d_{Y/S} ∘ θ`, for arbitrary `X'`, `Y` and `S`** — that is, it
proves [Stacks Project, Tag 04FL] with nothing affine.

The affine case over global sections, with the two conormal modules written as
`Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)]` and `RingHom.ker i.appTop.hom`, is
`Stacks.Thickenings.diagonalConormalMap_D` in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/MapDifferenceDiagonal.lean`; nothing here is
deduced from it.

## How the two sides are written

`D` is **not** re-assumed: it is *constructed* as `d_{Y/S}` followed by the transpose of `θ`
(`Stacks.Thickenings.liftDifferenceDerivation`), so Equation [Stacks Project, Tag 04BV] holds for
it by construction, and the whole content of the source becomes the identification of that
derivation as the difference derivation of [Stacks Project, Tag 04FG]: its value on a local
section `s` of `𝒪_Y` is the conormal class of `(a')^♯ s - (b')^♯ s`. That identification is
`Stacks.Thickenings.homEquiv_diagonalConormalSheafMap_d`, the declaration carrying the `04FL`
attribute, and it is restated for the derivation itself in
`Stacks.Thickenings.liftDifferenceDerivation_d`. The construction makes `D` an `𝒪_S`-derivation
for free — `PresheafOfModules.Derivation.postcomp` of the universal derivation — which is why no
Leibniz rule is verified below.

For a first-order thickening, where the conormal sheaf *is* the defining ideal and therefore sits
inside `𝒪_{X'}` by `Stacks.Thickenings.firstOrderImmersionConormalSheafι`, "the conormal class of
the difference" is the same information as the factorization
`(a')^♯ - (b')^♯ = ι ∘ D` asserted by [Stacks Project, Tag 04FG]; that literal form is
`Stacks.Thickenings.firstOrderImmersionConormalSheafι_liftDifferenceDerivation_d`.

## Main definitions

* `Stacks.Thickenings.liftPairOpen` and `Stacks.Thickenings.liftDiffSection`: the open
  `(b')⁻¹V ∩ (a')⁻¹V` of `X'` and the section `(a')^♯ s - (b')^♯ s` of `𝒪_{X'}` over it.
* `Stacks.Thickenings.liftPair`: the morphism `(b', a') : X' ⟶ Y ×_S Y` of the source's square.
* `Stacks.Thickenings.diagonalConormalSheafMap`: the map `θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}`, the map of
  [Stacks Project, Tag 01R4] for that square read through the isomorphism
  `Ω_{Y/S} ≅ 𝒞_{Y/(Y ×_S Y)}` of [Stacks Project, Tag 08S2].
* `Stacks.Thickenings.liftDifferenceDerivation`: the derivation `D` of
  [Stacks Project, Tag 04FG] for the pair `(a', b')`, namely `d_{Y/S}` followed by the transpose
  of `θ`.

## Main results

* `Stacks.Thickenings.homEquiv_diagonalConormalSheafMap_d`: **[Stacks Project, Tag 04FL]** —
  `θ (d_{Y/S} s)` is the conormal class of `(a')^♯ s - (b')^♯ s`, which is Equation
  [Stacks Project, Tag 04BV] for `θ` and the difference derivation.
* `Stacks.Thickenings.liftDifferenceDerivation_d` and
  `Stacks.Thickenings.firstOrderImmersionConormalSheafι_liftDifferenceDerivation_d`: the same
  statement read on the derivation `D`, and, for a first-order thickening, in the literal
  factorization form of [Stacks Project, Tag 04FG].
* `Stacks.Conormal.conormalClass_immersionConormalSheafMap` and its two variants: **the canonical
  map of [Stacks Project, Tag 01R4] carries conormal classes to conormal classes.** This is the
  generator formula of that tag written on `Stacks.Conormal.conormalClass` rather than on an
  affine presentation, and it is what makes the source's computation available at a sheaf level.
* `Stacks.Diagonal.cls_eq_conormalClass`: the conormal class that
  [Stacks Project, Tag 08S2] uses, `Stacks.LeibnizDerivation.cls`, is the conormal class of
  `p₂^♯ b - p₁^♯ b` in the sense of `Stacks.Conormal.conormalClass`.

## Implementation notes

**The proof is the source's hint, read on sheaves rather than on affine opens.** For a local
section `s` of `𝒪_Y` over `V`:

* `d_{Y/S} s` goes, under the comparison of [Stacks Project, Tag 08S2], to the conormal class of
  `1 ⊗ s - s ⊗ 1`, that is of `p₂^♯ s - p₁^♯ s`. The comparison is
  `Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal`, whose hom is
  `Stacks.LeibnizDerivation.toConormal` by definition, so its generator formula is
  `Stacks.LeibnizDerivation.toConormal_d`; `Stacks.Diagonal.cls_eq_conormalClass` rewrites the
  value as a `Stacks.Conormal.conormalClass`;
* the map of [Stacks Project, Tag 01R4] carries a conormal class to the conormal class of the
  image of a representative under the comorphism of the square's right arrow
  (`Stacks.Conormal.conormalClass_immersionConormalSheafMap`), and the comorphism of
  `(b', a')` takes `p₂^♯ s - p₁^♯ s` to `(a')^♯ s - (b')^♯ s`
  (`Stacks.Thickenings.map_app_liftPair_diffSection`), because the two projections of
  `Y ×_S Y` compose with `(b', a')` to `a'` and `b'`.

No affine open is chosen anywhere, and no locality argument is run: both steps are equalities of
sections over the open `V` the section `s` is given on.

**Why the conormal-class form of [Stacks Project, Tag 01R4] is proved here.** The library states
that tag's generator formula on an affine presentation, as
`Stacks.Immersion.IsInducedConormalSheafMap`, and separately in terms of the quotient map
`ℐ ⟶ i_* 𝒞` applied to a section of the ideal sheaf
(`Stacks.Conormal.conormalClass_homEquiv_immersionConormalSheafMap`). What the computation above
needs is the formula on `Stacks.Conormal.conormalClass`, which takes a section of `𝒪` killed by
the immersion rather than a section of the ideal sheaf. The bridge is
`Stacks.Conormal.conormalClass_eq_canonicalConormalQuotientMap`: a conormal class is the quotient
of the corresponding ideal-sheaf section, which exists by
`Stacks.ClosedImmersion.exists_idealSheaf_section_of_app_eq_zero` and is unique because the
inclusion of the ideal sheaf is injective on sections. Both halves of that bridge —
`Stacks.Conormal.conormalClass`, built from `Stacks.Conormal.idealSectionOf` over the coborder
neighbourhood, and `Stacks.Immersion.canonicalConormalQuotientMap`, built from the unit of
`i^* ⊣ i_*` at the ideal sheaf of `i` itself — are matched by
`Stacks.Immersion.conormalQuotientMap_apply_idealSheafComparison`.

**Where the two spellings of a category of sheaves of modules have to be kept apart.** The map of
[Stacks Project, Tag 01R4] lives in the ringed-space vocabulary
(`RingedSpaceModuleAdjunction.modulePullback` and its adjunction), while `Ω_{Y/S}` is an
`AlgebraicGeometry.Scheme.Modules`, whose `CategoryTheory.Category` instance is a structure copy.
Composing them is fine, but a rewrite inside the resulting composite produces a term that is not
type-correct at `implicit` transparency, so the composite is taken apart once and for all in
`Stacks.Thickenings.diagonalConormalSheafMap_homEquiv_app` and never rewritten again.
For the same reason `Stacks.Conormal.firstOrderImmersionConormalSheafι_conormalClass` substitutes
by `congrArg` rather than by `rw`: `Stacks.Conormal.conormalClass` and
`Stacks.Thickenings.firstOrderImmersionConormalSheafι` reach the witnessing
`AlgebraicGeometry.IsImmersion` instance by different routes, and `rw` matches on the nose.

## Generality

The hypotheses are weaker than the source's. `i` need only be an immersion, not a first-order
thickening — the derivation is a postcomposition of the universal one, so nothing needs
`ℐ² = 0`; only
`Stacks.Thickenings.firstOrderImmersionConormalSheafι_liftDifferenceDerivation_d`, which is about
the inclusion `𝒞_{X/X'} ⟶ 𝒪_{X'}`, assumes a closed immersion with square-zero ideal. And
instead of asking that `a'` and `b'` be morphisms over `S` for a common structure morphism
`X' ⟶ S`, only `b' ≫ q = a' ≫ q` is assumed, which is what the square needs.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
* [Stacks Project, Tag 04FL](https://stacks.math.columbia.edu/tag/04FL)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction AlgebraicGeometry.RingedSpace

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- **The ideal-sheaf comparison of the coborder factorization takes the section attached to a
vanishing function to `Stacks.Conormal.idealSectionOf`.** Both sections of the ideal sheaf of
`i.liftCoborder` have the same image in the structure sheaf of the coborder neighbourhood,
namely the restriction of `r`, and that image determines them. -/
theorem idealSheafComparison_eq_idealSectionOf (U : X.Opens) (r : Γ(X, U))
    (hr : (i.app U).hom r = 0)
    (y : (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.obj (op U))
    (hy : (Stacks.ClosedImmersion.idealSheafι i.toLRSHom.toShHom).val.app (op U) y = r) :
    (Stacks.Immersion.idealSheafComparison i i.coborderRange i.liftCoborder
        i.liftCoborder_ι).val.app (op U) y = idealSectionOf i U r hr := by
  refine Stacks.ClosedImmersion.injective_idealSheafι_val_app
    i.liftCoborder.toLRSHom.toShHom (i.coborderRange.ι ⁻¹ᵁ U) ?_
  have h1 := congr($(Stacks.Immersion.idealSheafComparison_comp_ι i i.coborderRange
    i.liftCoborder i.liftCoborder_ι).val.app (op U) y)
  simp only [comp_val_app_apply, Stacks.Immersion.modulePushforward_map_val_app_preimage] at h1
  rw [h1, hy]
  exact (kernelι_idealSectionOf i U r hr).symm

/-- **A conormal class is the canonical quotient of the corresponding section of the ideal
sheaf.** For an immersion `i : Z ⟶ X`, an open `U` of `X` and a section `r` of `𝒪_X` over `U`
killed by `i`, the class of `r` in `𝒞_{Z/X}` is the image of any section `y` of the ideal sheaf
of `i` lying over `r` under `Stacks.Immersion.canonicalConormalQuotientMap`.

This is the bridge between the two descriptions of the conormal sheaf as a quotient of the
ideal: `Stacks.Conormal.conormalClass` goes through the closed-immersion factorization of `i`
over its coborder neighbourhood, while `Stacks.Immersion.canonicalConormalQuotientMap` mentions
no factorization. -/
theorem conormalClass_eq_canonicalConormalQuotientMap (U : X.Opens) {V : Z.Opens}
    (hV : V ≤ i ⁻¹ᵁ U) (r : Γ(X, U)) (hr : (i.app U).hom r = 0)
    (y : (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.obj (op U))
    (hy : (Stacks.ClosedImmersion.idealSheafι i.toLRSHom.toShHom).val.app (op U) y = r) :
    conormalClass i U hV r hr =
      (conormalSheaf i).val.map (homOfLE hV).op
        ((Stacks.Immersion.canonicalConormalQuotientMap i).val.app (op U) y) := by
  have key := Stacks.Immersion.conormalQuotientMap_apply_idealSheafComparison i
    i.coborderRange i.liftCoborder i.liftCoborder_ι U V hV (le_liftCoborder_preimage i U hV) y
  rw [Stacks.Conormal.OpenFactorizations.conormalQuotientMap_liftCoborder i,
    idealSheafComparison_eq_idealSectionOf i U r hr y hy] at key
  exact key

/-- The restriction map of the conormal sheaf from an open to itself is the identity. -/
theorem conormalSheaf_map_self {V : Z.Opens} (h : V ≤ V)
    (x : (conormalSheaf i).val.obj (op V)) :
    (conormalSheaf i).val.map (homOfLE h).op x = x := by
  rw [Subsingleton.elim (homOfLE h) (𝟙 V)]
  exact congr($((conormalSheaf i).val.map_id (op V)) x)

/-- **The right arrow of a commutative square of immersions carries vanishing functions to
vanishing functions.** If `i ≫ k = f ≫ j` and `r` is killed by `j`, then `k^♯ r` is killed by
`i`. This is the containment `k^♯ J ⊆ I` of [Stacks Project, Tag 01R4], on sections. -/
theorem app_app_eq_zero_of_square {Z Z' W W' : Scheme.{u}} {i : Z ⟶ Z'} {j : W ⟶ W'}
    {f : Z ⟶ W} {k : Z' ⟶ W'} (hcomm : i ≫ k = f ≫ j) (V : W'.Opens) (r : Γ(W', V))
    (hr : (j.app V).hom r = 0) :
    (i.app (k ⁻¹ᵁ V)).hom ((k.app V).hom r) = 0 := by
  have key : ∀ (p : Z ⟶ W'), i ≫ k = p → (p.app V).hom r = 0 →
      (i.app (k ⁻¹ᵁ V)).hom ((k.app V).hom r) = 0 := by
    intro p hp hp2
    subst hp
    rw [Scheme.Hom.comp_app] at hp2
    exact hp2
  refine key (f ≫ j) hcomm ?_
  rw [Scheme.Hom.comp_app]
  show (f.app (j ⁻¹ᵁ V)).hom ((j.app V).hom r) = 0
  rw [hr, map_zero]

/-- **The map of conormal sheaves induced by a square of immersions carries conormal classes to
conormal classes.** -/
theorem conormalClass_immersionConormalSheafMap {Z Z' W W' : Scheme.{u}} (i : Z ⟶ Z')
    (j : W ⟶ W') (f : Z ⟶ W) (k : Z' ⟶ W') [IsImmersion i] [IsImmersion j]
    (hcomm : i ≫ k = f ≫ j) (V : W'.Opens) (C : Z.Opens) (hC : C ≤ i ⁻¹ᵁ (k ⁻¹ᵁ V))
    (hC' : C ≤ f ⁻¹ᵁ (j ⁻¹ᵁ V)) (r : Γ(W', V)) (hr : (j.app V).hom r = 0) :
    (conormalSheaf i).val.map (homOfLE hC').op
        ((((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
            (Stacks.Immersion.immersionConormalSheafMap i j f k
              (Stacks.Immersion.toShHom_square hcomm))).val.app (op (j ⁻¹ᵁ V)))
          (conormalClass j V (le_refl (j ⁻¹ᵁ V)) r hr)) =
      conormalClass i (k ⁻¹ᵁ V) hC ((k.app V).hom r)
        (app_app_eq_zero_of_square hcomm V r hr) := by
  obtain ⟨y, hy⟩ := Stacks.ClosedImmersion.exists_idealSheaf_section_of_app_eq_zero
    j.toLRSHom.toShHom V r hr
  obtain ⟨E, hE⟩ := Stacks.ClosedImmersion.exists_idealSheaf_section_of_app_eq_zero
    i.toLRSHom.toShHom (k ⁻¹ᵁ V) ((k.app V).hom r)
    (app_app_eq_zero_of_square hcomm V r hr)
  have hkey := conormalClass_homEquiv_immersionConormalSheafMap i j f k hcomm V C hC hC' y E
    (by rw [hE, hy])
  have hself := conormalSheaf_map_self j (le_refl (j ⁻¹ᵁ V))
    ((Stacks.Immersion.canonicalConormalQuotientMap j).val.app (op V) y)
  rw [conormalClass_eq_canonicalConormalQuotientMap j V (le_refl (j ⁻¹ᵁ V)) r hr y hy,
    hself,
    conormalClass_eq_canonicalConormalQuotientMap i (k ⁻¹ᵁ V) hC ((k.app V).hom r)
      (app_app_eq_zero_of_square hcomm V r hr) E hE]
  exact hkey

/-- `Stacks.Conormal.conormalClass` written through the adjunction unit. -/
theorem conormalClass_eq_unit (U : X.Opens) {V : Z.Opens} (hV : V ≤ i ⁻¹ᵁ U) (r : Γ(X, U))
    (hr : (i.app U).hom r = 0) :
    conormalClass i U hV r hr =
      (conormalSheaf i).val.map (homOfLE (le_liftCoborder_preimage i U hV)).op
        (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
          (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom)).val.app
            (op (i.coborderRange.ι ⁻¹ᵁ U)) (idealSectionOf i U r hr)) := rfl

/-- **A conormal class restricts to the conormal class over a smaller open.** This is
`Stacks.Conormal.conormalClass_restrict` with the ambient open left alone. -/
theorem conormalClass_restrict_target (U : X.Opens) {V V' : Z.Opens} (hV : V ≤ i ⁻¹ᵁ U)
    (hV' : V' ≤ i ⁻¹ᵁ U) (hVV' : V' ≤ V) (r : Γ(X, U)) (hr : (i.app U).hom r = 0) :
    (conormalSheaf i).val.map (homOfLE hVV').op (conormalClass i U hV r hr) =
      conormalClass i U hV' r hr := by
  have hr' : (i.app U).hom ((X.presheaf.map (homOfLE (le_refl U)).op).hom r) = 0 := by
    rw [Stacks.Diagonal.map_homOfLE_self_apply U (le_refl U) r]; exact hr
  refine (conormalClass_restrict i U U (le_refl U) hV hV' hVV' r hr hr').trans ?_
  exact conormalClass_congr i U hV' (Stacks.Diagonal.map_homOfLE_self_apply U (le_refl U) r) hr' hr

/-- `Stacks.Conormal.conormalClass` transported along an equality of ambient opens. -/
theorem conormalClass_congr_open (U U' : X.Opens) (hUU' : U = U') {V : Z.Opens}
    (hV : V ≤ i ⁻¹ᵁ U) (hV' : V ≤ i ⁻¹ᵁ U') (r : Γ(X, U)) (r' : Γ(X, U'))
    (hr : (i.app U).hom r = 0) (hr' : (i.app U').hom r' = 0)
    (hrr' : (X.presheaf.map (homOfLE hUU'.ge).op).hom r = r') :
    conormalClass i U hV r hr = conormalClass i U' hV' r' hr' := by
  subst hUU'
  rw [Stacks.Diagonal.map_homOfLE_self_apply U (le_refl U) r] at hrr'
  exact conormalClass_congr i U hV hrr' hr hr'

/-- A restriction map of a pushforward sheaf is the restriction map along the preimages. -/
theorem modulePushforward_obj_val_map {Z' X' : Scheme.{u}} (g : Z' ⟶ X')
    (M : SheafOfModules.{u} (structureSheafRing Z'.toLocallyRingedSpace.toRingedSpace))
    {A B : X'.Opens} (h : A ≤ B) (h' : g ⁻¹ᵁ A ≤ g ⁻¹ᵁ B)
    (x : ((modulePushforward g.toLRSHom.toShHom).obj M).val.obj (op B)) :
    ((modulePushforward g.toLRSHom.toShHom).obj M).val.map (homOfLE h).op x =
      M.val.map (homOfLE h').op x := by
  have h2 : (homOfLE h' : g ⁻¹ᵁ A ⟶ g ⁻¹ᵁ B) = (Opens.map g.base).map (homOfLE h) :=
    Subsingleton.elim _ _
  rw [h2]
  rfl

/-- **The map of conormal sheaves induced by a square of immersions carries conormal classes to
conormal classes**, read over an open of the source of the square's left arrow. -/
theorem conormalClass_immersionConormalSheafMap_restrict {Z Z' W W' : Scheme.{u}} (i : Z ⟶ Z')
    (j : W ⟶ W') (f : Z ⟶ W) (k : Z' ⟶ W') [IsImmersion i] [IsImmersion j]
    (hcomm : i ≫ k = f ≫ j) (V : W'.Opens) (D : W.Opens) (hD : D ≤ j ⁻¹ᵁ V) (C : Z.Opens)
    (hC : C ≤ i ⁻¹ᵁ (k ⁻¹ᵁ V)) (hCD : C ≤ f ⁻¹ᵁ D) (r : Γ(W', V))
    (hr : (j.app V).hom r = 0) :
    (conormalSheaf i).val.map (homOfLE hCD).op
        ((((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
            (Stacks.Immersion.immersionConormalSheafMap i j f k
              (Stacks.Immersion.toShHom_square hcomm))).val.app (op D))
          (conormalClass j V hD r hr)) =
      conormalClass i (k ⁻¹ᵁ V) hC ((k.app V).hom r)
        (app_app_eq_zero_of_square hcomm V r hr) := by
  have hC'' : C ≤ f ⁻¹ᵁ (j ⁻¹ᵁ V) := hCD.trans (f.preimage_mono hD)
  refine Eq.trans ?_ (conormalClass_immersionConormalSheafMap i j f k hcomm V C hC hC'' r hr)
  rw [← conormalClass_restrict_target j V (le_refl (j ⁻¹ᵁ V)) hD hD r hr,
    PresheafOfModules.naturality_apply
      (((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
        (Stacks.Immersion.immersionConormalSheafMap i j f k
          (Stacks.Immersion.toShHom_square hcomm))).val) (homOfLE hD).op
      (conormalClass j V (le_refl (j ⁻¹ᵁ V)) r hr),
    modulePushforward_obj_val_map f (Stacks.Conormal.conormalSheaf i) hD (f.preimage_mono hD)]
  have hcomp : ((homOfLE hC'').op : op (f ⁻¹ᵁ (j ⁻¹ᵁ V)) ⟶ op C) =
      (homOfLE (f.preimage_mono hD)).op ≫ (homOfLE hCD).op := Subsingleton.elim _ _
  rw [hcomp]
  exact (PresheafOfModules.map_comp_apply (Stacks.Conormal.conormalSheaf i).val
    (homOfLE (f.preimage_mono hD)).op (homOfLE hCD).op _).symm

/-- `Stacks.Conormal.conormalClass_immersionConormalSheafMap_restrict` over the whole preimage. -/
theorem conormalClass_immersionConormalSheafMap_app {Z Z' W W' : Scheme.{u}} (i : Z ⟶ Z')
    (j : W ⟶ W') (f : Z ⟶ W) (k : Z' ⟶ W') [IsImmersion i] [IsImmersion j]
    (hcomm : i ≫ k = f ≫ j) (V : W'.Opens) (D : W.Opens) (hD : D ≤ j ⁻¹ᵁ V)
    (hC : f ⁻¹ᵁ D ≤ i ⁻¹ᵁ (k ⁻¹ᵁ V)) (r : Γ(W', V)) (hr : (j.app V).hom r = 0) :
    (((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
          (Stacks.Immersion.immersionConormalSheafMap i j f k
            (Stacks.Immersion.toShHom_square hcomm))).val.app (op D))
        (conormalClass j V hD r hr) =
      conormalClass i (k ⁻¹ᵁ V) hC ((k.app V).hom r)
        (app_app_eq_zero_of_square hcomm V r hr) := by
  refine Eq.trans ?_ (conormalClass_immersionConormalSheafMap_restrict i j f k hcomm V D hD
    (f ⁻¹ᵁ D) hC (le_refl (f ⁻¹ᵁ D)) r hr)
  exact (conormalSheaf_map_self i (le_refl (f ⁻¹ᵁ D)) _).symm

section FirstOrder

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]

/-- **For a first-order thickening the inclusion `𝒞_{X/X'} ⟶ 𝒪_{X'}` undoes the conormal
class.** -/
theorem firstOrderImmersionConormalSheafι_conormalClass (hsq : i.ker ^ 2 = ⊥) (U : X.Opens)
    (r : Γ(X, U)) (hr : (i.app U).hom r = 0) :
    (Stacks.Thickenings.firstOrderImmersionConormalSheafι i hsq).val.app (op U)
        (conormalClass i U (le_refl (i ⁻¹ᵁ U)) r hr) = r := by
  obtain ⟨y, hy⟩ := Stacks.ClosedImmersion.exists_idealSheaf_section_of_app_eq_zero
    i.toLRSHom.toShHom U r hr
  refine Eq.trans (congrArg (ConcreteCategory.hom
      ((Stacks.Thickenings.firstOrderImmersionConormalSheafι i hsq).val.app (op U)))
    ((conormalClass_eq_canonicalConormalQuotientMap i U (le_refl (i ⁻¹ᵁ U)) r hr y hy).trans
      (conormalSheaf_map_self i (le_refl (i ⁻¹ᵁ U))
        ((Stacks.Immersion.canonicalConormalQuotientMap i).val.app (op U) y)))) ?_
  refine Eq.trans ?_ hy
  have hpin := Thickenings.canonicalConormalQuotientMap_comp_firstOrderImmersionConormalSheafι
    i hsq
  exact congr($(hpin).val.app (op U) y)

/-- `Stacks.Conormal.firstOrderImmersionConormalSheafι_conormalClass` with the open over which
the class is read presented by an equality with the preimage. -/
theorem firstOrderImmersionConormalSheafι_conormalClass_of_eq (hsq : i.ker ^ 2 = ⊥)
    (U : X.Opens) {V : Z.Opens} (hV : V ≤ i ⁻¹ᵁ U) (hUV : i ⁻¹ᵁ U = V) (r : Γ(X, U))
    (hr : (i.app U).hom r = 0) :
    (Stacks.Thickenings.firstOrderImmersionConormalSheafι i hsq).val.app (op U)
        ((conormalSheaf i).val.map (homOfLE hUV.le).op (conormalClass i U hV r hr)) = r := by
  rw [conormalClass_restrict_target i U hV (le_refl (i ⁻¹ᵁ U)) hUV.le r hr]
  exact firstOrderImmersionConormalSheafι_conormalClass i hsq U r hr

end FirstOrder

end Stacks.Conormal

namespace Stacks.Diagonal

/-- The comorphism of `f` on `V` after a restricted comorphism of `g` is the restricted
comorphism of `f ≫ g`, which may be presented as any equal morphism `g'`. -/
private theorem hom_app_hom_appLE_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {g' : X ⟶ Z} (hg : f ≫ g = g') (U : Z.Opens) (V : Y.Opens) (e : V ≤ g ⁻¹ᵁ U)
    (e' : f ⁻¹ᵁ V ≤ g' ⁻¹ᵁ U) (s : Γ(Z, U)) :
    (f.app V).hom ((g.appLE U V e).hom s) = (g'.appLE U (f ⁻¹ᵁ V) e').hom s := by
  subst hg
  have h := Scheme.Hom.appLE_comp_appLE f g U V (f ⁻¹ᵁ V) e le_rfl
  rw [Scheme.Hom.appLE_preimage_self] at h
  exact congrArg (fun z => z.hom s) h

open Stacks.Conormal Stacks.LeibnizDerivation

variable {Y S : Scheme.{u}} (q : Y ⟶ S)

/-- `Stacks.Diagonal.prodOpen` and `Stacks.LeibnizDerivation.ambientChart` are the same open of
`Y ×_S Y`, both being the intersection of the two preimages of `U`. -/
theorem prodOpen_eq_ambientChart (U : Y.Opens) : prodOpen q U = ambientChart q U := rfl

/-- **`p₂^♯ b - p₁^♯ b` over the chart of the coborder neighbourhood is the restriction of
`p₂^♯ b - p₁^♯ b` over the ambient chart.** The chart is the preimage of the ambient chart under
the inclusion of the coborder neighbourhood, and each projection's map on sections factors
through that inclusion. -/
theorem deltaAt_eq_app_diffSection (U : Y.Opens) (b : Γ(Y, U)) :
    deltaAt q U b =
      ((pullback.diagonal q).coborderRange.ι.app (prodOpen q U)).hom (diffSection q U b) := by
  have key : ∀ (p : pullback q q ⟶ Y) (e : prodOpen q U ≤ p ⁻¹ᵁ U)
      (e' : chart q U ≤ ((pullback.diagonal q).coborderRange.ι ≫ p) ⁻¹ᵁ U),
      (((pullback.diagonal q).coborderRange.ι ≫ p).appLE U (chart q U) e').hom b =
        ((pullback.diagonal q).coborderRange.ι.app (prodOpen q U)).hom
          ((p.appLE U (prodOpen q U) e).hom b) := fun p e e' =>
    (hom_app_hom_appLE_apply _ p rfl U (prodOpen q U) e e' b).symm
  rw [deltaAt, Stacks.DiagonalDerivation.delta_eq, diffSection, map_sub,
    key (pullback.snd q q) (prodOpen_le_snd q U) (chart_le_snd q U),
    key (pullback.fst q q) (prodOpen_le_fst q U) (chart_le_fst q U)]
  rfl

/-- The two names for the section of the ideal sheaf of the diagonal attached to
`p₂^♯ b - p₁^♯ b` agree: a section of that ideal sheaf is determined by its image in the
structure sheaf. -/
theorem deltaIdealSection_eq_idealSectionOf (U : Y.Opens) (b : Γ(Y, U)) :
    idealSectionOf (pullback.diagonal q) (prodOpen q U) (diffSection q U b)
        (app_diffSection q U b) = deltaIdealSection q U b :=
  eq_idealSection (pullback.diagonal q).liftCoborder (chart q U) (deltaAt q U b)
    (app_deltaAt_eq_zero q U b) _
    ((kernelι_idealSectionOf (pullback.diagonal q) (prodOpen q U) (diffSection q U b)
      (app_diffSection q U b)).trans (deltaAt_eq_app_diffSection q U b).symm)

/-- **The conormal class of [Stacks, Tag 08S2] is the conormal class of `p₂^♯ b - p₁^♯ b`.** -/
theorem cls_eq_conormalClass (U : Y.Opens) (b : Γ(Y, U)) :
    cls q U b =
      conormalClass (pullback.diagonal q) (prodOpen q U) (le_diagonal_preimage_prodOpen q U)
        (diffSection q U b) (app_diffSection q U b) := by
  rw [conormalClass_eq_unit, deltaIdealSection_eq_idealSectionOf q U b,
    Subsingleton.elim (homOfLE (le_liftCoborder_preimage (pullback.diagonal q) (prodOpen q U)
      (le_diagonal_preimage_prodOpen q U))) (homOfLE (le_chart_preimage q U))]
  show _ = (conormalSheaf (pullback.diagonal q)).val.map (homOfLE (le_chart_preimage q U)).op
    (((modulePullbackPushforwardAdjunction
          (pullback.diagonal q).liftCoborder.toLRSHom.toShHom).unit.app
        (Stacks.ClosedImmersion.idealSheaf
          (pullback.diagonal q).liftCoborder.toLRSHom.toShHom)).val.app
      (op (chart q U)) (deltaIdealSection q U b))
  rw [← Stacks.Conormal.OpenFactorizations.conormalQuotientMap_liftCoborder
    (pullback.diagonal q)]
  rfl

end Stacks.Diagonal


namespace Stacks.Thickenings

open Stacks.Conormal Stacks.Diagonal CategoryTheory.Limits

variable {S X X' Y : Scheme.{u}}

/-- The open `(b')⁻¹V ∩ (a')⁻¹V` of `X'`. -/
def liftPairOpen (a' b' : X' ⟶ Y) (V : Y.Opens) : X'.Opens := b' ⁻¹ᵁ V ⊓ a' ⁻¹ᵁ V

/-- The section `(a')^♯ s - (b')^♯ s` of `𝒪_{X'}`. -/
def liftDiffSection (a' b' : X' ⟶ Y) (V : Y.Opens) (s : Γ(Y, V)) :
    Γ(X', liftPairOpen a' b' V) :=
  (a'.appLE V (liftPairOpen a' b' V) inf_le_right).hom s -
    (b'.appLE V (liftPairOpen a' b' V) inf_le_left).hom s

variable {i : X ⟶ X'} {a : X ⟶ Y} {a' b' : X' ⟶ Y} {q : Y ⟶ S}

/-- The morphism `(b', a') : X' ⟶ Y ×_S Y`. -/
def liftPair (hq : b' ≫ q = a' ≫ q) : X' ⟶ pullback q q := pullback.lift b' a' hq

/-- The first projection of the pair `(b', a')` is `b'`. -/
theorem liftPair_fst (hq : b' ≫ q = a' ≫ q) : liftPair hq ≫ pullback.fst q q = b' :=
  pullback.lift_fst _ _ _

/-- The second projection of the pair `(b', a')` is `a'`. -/
theorem liftPair_snd (hq : b' ≫ q = a' ≫ q) : liftPair hq ≫ pullback.snd q q = a' :=
  pullback.lift_snd _ _ _

/-- **The commutative square of the source.** The pair `(b', a')` restricted to `X` is the
diagonal composed with `a`, because `a'` and `b'` both restrict to `a`. -/
theorem liftPair_square (hq : b' ≫ q = a' ≫ q) (comm_a : i ≫ a' = a) (comm_b : i ≫ b' = a) :
    i ≫ liftPair hq = a ≫ pullback.diagonal q := by
  refine pullback.hom_ext ?_ ?_ <;> rw [Category.assoc, Category.assoc]
  · rw [liftPair_fst, pullback.diagonal_fst, Category.comp_id, comm_b]
  · rw [liftPair_snd, pullback.diagonal_snd, Category.comp_id, comm_a]

/-- The pair `(b', a')` pulls the open `p₁⁻¹V ∩ p₂⁻¹V` of `Y ×_S Y` back to
`(b')⁻¹V ∩ (a')⁻¹V`. -/
theorem liftPair_preimage_prodOpen (hq : b' ≫ q = a' ≫ q) (V : Y.Opens) :
    liftPair hq ⁻¹ᵁ prodOpen q V = liftPairOpen a' b' V := by
  rw [prodOpen, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
    ← Scheme.Hom.comp_preimage, liftPair_fst, liftPair_snd]
  rfl

/-- `i` pulls `(b')⁻¹V ∩ (a')⁻¹V` back to `a⁻¹V`, since `a'` and `b'` both restrict to `a`. -/
theorem preimage_liftPairOpen (comm_a : i ≫ a' = a) (comm_b : i ≫ b' = a) (V : Y.Opens) :
    i ⁻¹ᵁ (liftPairOpen a' b' V) = a ⁻¹ᵁ V := by
  rw [liftPairOpen, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
    ← Scheme.Hom.comp_preimage, comm_a, comm_b, inf_idem]

/-- `a⁻¹V` is contained in `i⁻¹((b')⁻¹V ∩ (a')⁻¹V)`, which is the direction the restriction map
of a sheaf of modules consumes. -/
theorem le_preimage_liftPairOpen (comm_a : i ≫ a' = a) (comm_b : i ≫ b' = a) (V : Y.Opens) :
    a ⁻¹ᵁ V ≤ i ⁻¹ᵁ (liftPairOpen a' b' V) :=
  (preimage_liftPairOpen comm_a comm_b V).ge

/-- **The difference `(a')^♯ s - (b')^♯ s` is killed by `i`.** Both comorphisms restrict to
`a^♯` on `X`, so the difference lies in the defining ideal of `i`. This is where the hypothesis
that `a'` and `b'` agree on `X` is used. -/
theorem app_liftDiffSection (comm_a : i ≫ a' = a) (comm_b : i ≫ b' = a) (V : Y.Opens)
    (s : Γ(Y, V)) : (i.app (liftPairOpen a' b' V)).hom (liftDiffSection a' b' V s) = 0 := by
  have key : ∀ (c : X' ⟶ Y) (e : liftPairOpen a' b' V ≤ c ⁻¹ᵁ V), i ≫ c = a →
      (i.app (liftPairOpen a' b' V)).hom ((c.appLE V (liftPairOpen a' b' V) e).hom s) =
        (a.appLE V (i ⁻¹ᵁ (liftPairOpen a' b' V))
          ((preimage_liftPairOpen comm_a comm_b V).le)).hom s :=
    fun c e hc => hom_app_hom_appLE_apply i c hc V _ e _ s
  rw [liftDiffSection, map_sub, key a' inf_le_right comm_a, key b' inf_le_left comm_b, sub_self]

/-- **The comparison isomorphism of [Stacks Project, Tag 08S2] sends `d_{Y/S} s` to the conormal
class of `p₂^♯ s - p₁^♯ s`**, written as a `Stacks.Conormal.conormalClass`. Its hom is
`Stacks.LeibnizDerivation.toConormal` by definition, so this is that map's generator formula read
through `Stacks.Diagonal.cls_eq_conormalClass`. -/
theorem relativeDifferentialsIsoDiagonalConormal_hom_d (V : Y.Opens) (s : Γ(Y, V)) :
    ((Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal q).hom.val.app
        (op V)).hom (q.universalRelativeDerivation.d s) =
      conormalClass (pullback.diagonal q) (prodOpen q V) (le_diagonal_preimage_prodOpen q V)
        (diffSection q V s) (app_diffSection q V s) := by
  have hiso : (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal q).hom =
      Stacks.LeibnizDerivation.toConormal q := rfl
  rw [hiso, Stacks.LeibnizDerivation.toConormal_d, cls_eq_conormalClass]

/-- **The map `θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}` of [Stacks, Tag 01R4] for the diagonal square.** -/
def diagonalConormalSheafMap [IsImmersion i] (hq : b' ≫ q = a' ≫ q) (comm_a : i ≫ a' = a)
    (comm_b : i ≫ b' = a) :
    (modulePullback a.toLRSHom.toShHom).obj (Scheme.Hom.relativeDifferentials q) ⟶
      Stacks.Conormal.conormalSheaf i :=
  (modulePullback a.toLRSHom.toShHom).map
      (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal q).hom ≫
    Stacks.Immersion.immersionConormalSheafMap i (pullback.diagonal q) a (liftPair hq)
      (Stacks.Immersion.toShHom_square (liftPair_square hq comm_a comm_b))

/-- **The comorphism of the pair `(b', a')` takes `p₂^♯ s - p₁^♯ s` to `(a')^♯ s - (b')^♯ s`**,
after the identification of `(b', a')⁻¹(p₁⁻¹V ∩ p₂⁻¹V)` with `(b')⁻¹V ∩ (a')⁻¹V`. This is the
second half of the source's hint. -/
theorem map_app_liftPair_diffSection (hq : b' ≫ q = a' ≫ q) (V : Y.Opens) (s : Γ(Y, V)) :
    (X'.presheaf.map (homOfLE (liftPair_preimage_prodOpen hq V).ge).op).hom
        (((liftPair hq).app (prodOpen q V)).hom (diffSection q V s)) =
      liftDiffSection a' b' V s := by
  have hc : liftPairOpen a' b' V ≤ liftPair hq ⁻¹ᵁ prodOpen q V :=
    (liftPair_preimage_prodOpen hq V).ge
  have key : ∀ (c : X' ⟶ Y) (pr : pullback q q ⟶ Y), liftPair hq ≫ pr = c →
      ∀ (e : prodOpen q V ≤ pr ⁻¹ᵁ V) (e2 : liftPairOpen a' b' V ≤ c ⁻¹ᵁ V),
      (X'.presheaf.map (homOfLE hc).op).hom
          (((liftPair hq).app (prodOpen q V)).hom ((pr.appLE V (prodOpen q V) e).hom s)) =
        (c.appLE V (liftPairOpen a' b' V) e2).hom s := by
    intro c pr hpr e e2
    have e1 : liftPair hq ⁻¹ᵁ prodOpen q V ≤ c ⁻¹ᵁ V := by
      rw [liftPair_preimage_prodOpen]; exact e2
    rw [hom_app_hom_appLE_apply (liftPair hq) pr hpr V (prodOpen q V) e e1 s]
    exact congrArg (fun z : Γ(Y, V) ⟶ Γ(X', liftPairOpen a' b' V) => z.hom s)
      (Scheme.Hom.appLE_map c e1 (homOfLE hc).op)
  rw [diffSection]
  simp only [map_sub]
  rw [key a' (pullback.snd q q) (liftPair_snd hq) (prodOpen_le_snd q V) inf_le_right,
    key b' (pullback.fst q q) (liftPair_fst hq) (prodOpen_le_fst q V) inf_le_left]
  rfl


/-- **The transpose of `θ` on sections, split into its two factors**: the comparison
isomorphism of [Stacks Project, Tag 08S2] followed by the transpose of the canonical map of
[Stacks Project, Tag 01R4]. This is naturality of the adjunction in its left variable; it is
stated once so that no later step has to rewrite inside the composite. -/
theorem diagonalConormalSheafMap_homEquiv_app [IsImmersion i] (hq : b' ≫ q = a' ≫ q)
    (comm_a : i ≫ a' = a) (comm_b : i ≫ b' = a) (V : Y.Opens)
    (x : (Scheme.Hom.relativeDifferentials q).val.obj (op V)) :
    (((modulePullbackPushforwardAdjunction a.toLRSHom.toShHom).homEquiv _ _
          (diagonalConormalSheafMap hq comm_a comm_b)).val.app (op V)) x =
      (((modulePullbackPushforwardAdjunction a.toLRSHom.toShHom).homEquiv _ _
            (Stacks.Immersion.immersionConormalSheafMap i (pullback.diagonal q) a (liftPair hq)
              (Stacks.Immersion.toShHom_square (liftPair_square hq comm_a comm_b)))).val.app
          (op V))
        (((Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal q).hom.val.app
          (op V)).hom x) := by
  have hnat := Adjunction.homEquiv_naturality_left
    (modulePullbackPushforwardAdjunction a.toLRSHom.toShHom)
    (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal q).hom
    (Stacks.Immersion.immersionConormalSheafMap i (pullback.diagonal q) a (liftPair hq)
      (Stacks.Immersion.toShHom_square (liftPair_square hq comm_a comm_b)))
  rw [diagonalConormalSheafMap, hnat]
  rfl

/-- **The difference of two maps to a fixed scheme, through the diagonal**,
[Stacks, Tag 04FL]. -/
@[stacks 04FL]
theorem homEquiv_diagonalConormalSheafMap_d [IsImmersion i] (hq : b' ≫ q = a' ≫ q)
    (comm_a : i ≫ a' = a) (comm_b : i ≫ b' = a) (V : Y.Opens) (s : Γ(Y, V)) :
    (((modulePullbackPushforwardAdjunction a.toLRSHom.toShHom).homEquiv _ _
          (diagonalConormalSheafMap hq comm_a comm_b)).val.app (op V))
        (q.universalRelativeDerivation.d s) =
      conormalClass i (liftPairOpen a' b' V) (le_preimage_liftPairOpen comm_a comm_b V)
        (liftDiffSection a' b' V s) (app_liftDiffSection comm_a comm_b V s) := by
  have hC : a ⁻¹ᵁ V ≤ i ⁻¹ᵁ (liftPair hq ⁻¹ᵁ prodOpen q V) := by
    rw [liftPair_preimage_prodOpen]; exact le_preimage_liftPairOpen comm_a comm_b V
  have hA := conormalClass_immersionConormalSheafMap_app i (pullback.diagonal q) a
    (liftPair hq) (liftPair_square hq comm_a comm_b) (prodOpen q V) V
    (le_diagonal_preimage_prodOpen q V) hC (diffSection q V s) (app_diffSection q V s)
  rw [diagonalConormalSheafMap_homEquiv_app hq comm_a comm_b V,
    relativeDifferentialsIsoDiagonalConormal_hom_d, hA]
  exact conormalClass_congr_open i (liftPair hq ⁻¹ᵁ prodOpen q V) (liftPairOpen a' b' V)
    (liftPair_preimage_prodOpen hq V) hC (le_preimage_liftPairOpen comm_a comm_b V) _ _ _ _
    (map_app_liftPair_diffSection hq V s)

/-- **The derivation `D` of [Stacks, Tag 04FG]** for a pair of maps into an unthickened target:
`d_{Y/S}` followed by the transpose of `θ`, which is Equation [Stacks, Tag 04BV] by
construction. -/
def liftDifferenceDerivation [IsImmersion i] (hq : b' ≫ q = a' ≫ q) (comm_a : i ≫ a' = a)
    (comm_b : i ≫ b' = a) :
    SheafOfModules.SheafDerivation (inverseImageStructureMap q)
      ((modulePushforward a.toLRSHom.toShHom).obj (Stacks.Conormal.conormalSheaf i)) :=
  (Scheme.Hom.universalRelativeDerivation q).postcomp
    ((modulePullbackPushforwardAdjunction a.toLRSHom.toShHom).homEquiv _ _
      (diagonalConormalSheafMap hq comm_a comm_b)).val

/-- **Equation [Stacks Project, Tag 04BV] read on the derivation.** The derivation
`D = d_{Y/S} ∘ θ` sends a local section `s` of `𝒪_Y` to the conormal class of
`(a')^♯ s - (b')^♯ s`; that is, it is the difference derivation of
[Stacks Project, Tag 04FG] for the pair `(a', b')`. -/
theorem liftDifferenceDerivation_d [IsImmersion i] (hq : b' ≫ q = a' ≫ q)
    (comm_a : i ≫ a' = a) (comm_b : i ≫ b' = a) (V : Y.Opens) (s : Γ(Y, V)) :
    (liftDifferenceDerivation hq comm_a comm_b).d (X := op V) s =
      conormalClass i (liftPairOpen a' b' V) (le_preimage_liftPairOpen comm_a comm_b V)
        (liftDiffSection a' b' V s) (app_liftDiffSection comm_a comm_b V s) :=
  homEquiv_diagonalConormalSheafMap_d hq comm_a comm_b V s

/-- **The factorization of [Stacks, Tag 04FG] for a pair of maps into an unthickened target.**
The difference `(a')^♯ s - (b')^♯ s` is the image of `D s` under the inclusion
`𝒞_{X/X'} ⟶ 𝒪_{X'}` of a first-order thickening. -/
theorem firstOrderImmersionConormalSheafι_liftDifferenceDerivation_d
    [AlgebraicGeometry.IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥) (hq : b' ≫ q = a' ≫ q)
    (comm_a : i ≫ a' = a) (comm_b : i ≫ b' = a) (V : Y.Opens) (s : Γ(Y, V)) :
    (firstOrderImmersionConormalSheafι i hsq).val.app (op (liftPairOpen a' b' V))
        ((Stacks.Conormal.conormalSheaf i).val.map
            (homOfLE (preimage_liftPairOpen comm_a comm_b V).le).op
          ((liftDifferenceDerivation hq comm_a comm_b).d (X := op V) s)) =
      liftDiffSection a' b' V s := by
  rw [liftDifferenceDerivation_d]
  exact firstOrderImmersionConormalSheafι_conormalClass_of_eq i hsq (liftPairOpen a' b' V)
    (le_preimage_liftPairOpen comm_a comm_b V) (preimage_liftPairOpen comm_a comm_b V)
    (liftDiffSection a' b' V s) (app_liftDiffSection comm_a comm_b V s)

end Stacks.Thickenings

end
