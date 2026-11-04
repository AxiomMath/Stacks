module

public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSheafCorepresentable
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSquareZero

/-!
# Existence in the corepresentation of derivations by the pullback of `Ω_{X/S}`

Let `f : X ⟶ S` be a morphism of schemes, let `V` be an affine open of `S` and `W` an affine open
of `X` with `W ≤ f ⁻¹ᵁ V`, let `a : T ⟶ X` be a morphism of schemes mapping into `W`, and let `N`
be a sheaf of modules on `T`. Composing a morphism `φ : a^*Ω_{X/S} ⟶ N` with the pullback
`Stacks.Smooth.pullbackD` of the universal differential produces a `Γ(S, V)`-derivation of
`Γ(X, W)` with values in `Γ(N, ⊤)`. That this assignment is injective is
`Stacks.Smooth.pullbackCotangentSheaf_hom_ext`; this file proves that it is **surjective**, and
hence bijective. That bijection is the affine computation of [Stacks Project, Tag 01UM] in the
form that [Stacks Project, Tag 02H6] consumes.

## Main definitions

* `Stacks.Smooth.basicOpenD` is the extension of the given derivation `δ` of `Γ(X, W)` to the
  sections over a basic open `X.basicOpen g` of `W`, obtained from
  `Stacks.Smooth.derivationLocalizationLift`.
* `Stacks.Smooth.glueD` is the sectionwise differential obtained by gluing those extensions: for
  every open `V₀` of `X` a map `Γ(X, V₀) → Γ(N, a ⁻¹ᵁ V₀)`.
* `Stacks.Smooth.glueDerivation` packages it as a relative derivation of `𝒪_X` over `f⁻¹𝒪_S` with
  values in `a_*N`.

## Main results

* `Stacks.Smooth.eq_zero_of_leibniz_basicOpen'` generalizes
  `Stacks.Smooth.eq_zero_of_leibniz_basicOpen` to values in the sections over an arbitrary open of
  `T` mapping into the basic open; it is the uniqueness statement that drives everything below.
* `Stacks.Smooth.map_basicOpenD` says that the extensions attached to two basic opens agree where
  both are defined, which is what makes them glue.
* `Stacks.Smooth.basicOpenD_appLE`: the extension of `δ` kills the image of `Γ(S, V')` for *every*
  open `V'` of `S`, not only for `V`.
* `Stacks.Smooth.existsUnique_glueD` is the gluing, and `Stacks.Smooth.glueD_mul`,
  `Stacks.Smooth.glueD_map`, `Stacks.Smooth.glueD_app` are the Leibniz rule, the naturality and
  the vanishing on the base for the glued family.
* `Stacks.Smooth.exists_hom_pullbackCotangentSheaf` is the existence statement, and
  `Stacks.Smooth.existsUnique_hom_pullbackCotangentSheaf` combines it with the uniqueness statement
  into the full corepresentability.

## Implementation notes

The construction is the standard local argument, run in the existence direction.

Over a basic open `X.basicOpen g` of `W` the ring `Γ(X, X.basicOpen g)` is a localization of
`Γ(X, W)`, so `δ` — composed with restriction of sections of `N` — extends uniquely to it by
`Stacks.Smooth.derivationLocalizationLift`. Two such extensions agree on the preimage of any open
mapping into both basic opens, again by uniqueness along a localization, so the family is
compatible on the cover of `a ⁻¹ᵁ V₀` by the preimages of the basic opens of `W` contained in
`V₀` (`Stacks.Smooth.preimage_le_iSup_preimage_basicOpen`) and glues, since `N` is a sheaf.

Three properties of the glued family then have to be checked, and each is checked locally against
the characterizing property `Stacks.Smooth.glueD_restrict`: the Leibniz rule, naturality in the
open, and the vanishing on sections coming from `𝒪_S`. The last one is the only one that is not
formal. It needs the vanishing on `Γ(S, V')` for an *arbitrary* open `V'` of `S`, whereas `δ` is
only assumed to be a `Γ(S, V)`-derivation; this is `Stacks.Smooth.basicOpenD_appLE`, proved by
covering `X.basicOpen g` by the basic opens of `W` lying over a basic open `S.basicOpen s` of the
affine `V` contained in `V'`, on which `Γ(S, S.basicOpen s)` is a localization of `Γ(S, V)` whose
denominators become units in `Γ(X, X.basicOpen g'')` — so the Leibniz rule propagates the
vanishing (`Stacks.Smooth.basicOpenD_appLE_basicOpen`).

Finally the glued family is a derivation over `f⁻¹𝒪_S`, not merely over the images of the
`Γ(S, V')`; that step is
`Stacks.Smooth.apply_inverseImageStructureApp_eq_zero`, proved by adjunction in
`StacksFrontier.AlgebraicGeometry.Smooth.CotangentSquareZero`. Feeding the resulting derivation to
`Stacks.Sheaves.Differentials.universalDerivation_isUniversal` gives a morphism
`Ω_{X/S} ⟶ a_*N`, and `Stacks.Smooth.pullbackCotangentSheafHomEquiv` transports it to the desired
`a^*Ω_{X/S} ⟶ N`.

What is *not* proved here is bijectivity of `Stacks.Smooth.cotangentComparison`. The results of
this file give, for `T` affine with `A = Γ(T, ⊤)`, a two-sided inverse of
`cotangentComparison f a W hWV le_top` as soon as one knows that an arbitrary `A`-module is the
module of global sections of a sheaf of modules on `T` in a way that is adjoint to taking global
sections: taking `N` to be the sheaf attached to `A ⊗[Γ(X, W)] Ω[Γ(X, W)⁄Γ(S, V)]` and `δ` to be
`b ↦ 1 ⊗ d b` produces a retraction, and the adjoint of `cotangentComparison` itself produces a
section, the two composites being identified with the identity by
`Stacks.Smooth.existsUnique_hom_pullbackCotangentSheaf`. Mathlib has that adjunction only for
`T = Spec R` on the nose (`AlgebraicGeometry.tilde.adjunction`), so transporting it along
`T ≅ Spec Γ(T, ⊤)` is the remaining step.

## References

* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Sheaves.RingedSpaceDifferentials

universe u

namespace Stacks.Smooth

/-! ### Derivations on a basic open, with values in a smaller open of `T` -/

section Localization

variable {X T : Scheme.{u}} (a : T ⟶ X) (M : T.Modules) {W : X.Opens}

/-- The scalar tower `Γ(X, W) → Γ(X, X.basicOpen g) → Γ(M, U)`, for `U` an open of `T` mapping
into the basic open of `g`. -/
theorem isScalarTower_basicOpen (g : Γ(X, W)) {U : T.Opens} (hU : U ≤ a ⁻¹ᵁ X.basicOpen g) :
    letI := moduleAppLE a M (hU.trans ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le)
    letI := moduleAppLE a M hU
    IsScalarTower Γ(X, W) Γ(X, X.basicOpen g) Γ(M, U) := by
  let := moduleAppLE a M (hU.trans ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le)
  let := moduleAppLE a M hU
  refine IsScalarTower.of_algebraMap_smul fun c n ↦ ?_
  change (a.appLE (X.basicOpen g) U hU).hom
        ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom c) • n
      = (a.appLE W U
        (hU.trans ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le)).hom c • n
  rw [← CommRingCat.comp_apply, a.map_appLE]

/-- **A derivation on a basic open is determined by the sections it comes from**, in the form in
which the values are taken in the sections over an arbitrary open `U` of `T` mapping into the
basic open. A map from `Γ(X, X.basicOpen g)` to `Γ(M, U)` satisfying the Leibniz rule and
vanishing on the sections restricted from the affine open `W` vanishes identically. -/
theorem eq_zero_of_leibniz_basicOpen' (hW : IsAffineOpen W) (g : Γ(X, W)) {U : T.Opens}
    (hU : U ≤ a ⁻¹ᵁ X.basicOpen g) (e : Γ(X, X.basicOpen g) → Γ(M, U))
    (hmul : ∀ x y : Γ(X, X.basicOpen g),
      e (x * y) = (a.appLE (X.basicOpen g) U hU).hom x • e y
        + (a.appLE (X.basicOpen g) U hU).hom y • e x)
    (hzero : ∀ b : Γ(X, W), e ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom b) = 0)
    (x : Γ(X, X.basicOpen g)) : e x = 0 := by
  let := moduleAppLE a M (hU.trans ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le)
  let := moduleAppLE a M hU
  have := hW.isLocalization_basicOpen g
  have := isScalarTower_basicOpen a M g hU
  exact eq_zero_of_leibniz_of_apply_algebraMap_eq_zero Γ(X, X.basicOpen g)
    (Submonoid.powers g) e hmul hzero x

end Localization

/-! ### Restricting and extending a derivation of the sections over `W` -/

section Extension

variable {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) (N : T.Modules) {V : S.Opens}
  {W : X.Opens}

/-- Restriction of sections of a sheaf of modules on `T`, as a `Γ(X, W)`-linear map for the
module structures `Stacks.Smooth.moduleAppLE`. -/
noncomputable def restrictLinearMap {U U' : T.Opens} (hUW : U ≤ a ⁻¹ᵁ W) (hU'W : U' ≤ a ⁻¹ᵁ W)
    (hU'U : U' ≤ U) :
    letI := moduleAppLE a N hUW
    letI := moduleAppLE a N hU'W
    Γ(N, U) →ₗ[Γ(X, W)] Γ(N, U') :=
  letI := moduleAppLE a N hUW
  letI := moduleAppLE a N hU'W
  { toFun := (N.presheaf.map (homOfLE hU'U).op).hom
    map_add' := map_add _
    map_smul' := fun c n ↦ by
      change (N.presheaf.map (homOfLE hU'U).op).hom ((a.appLE W U hUW).hom c • n)
          = (a.appLE W U' hU'W).hom c • (N.presheaf.map (homOfLE hU'U).op).hom n
      rw [Scheme.Modules.map_smul, ← CommRingCat.comp_apply, a.appLE_map] }

/-- **Restriction of a derivation of the sections over `W`.** A `Γ(S, V)`-derivation of `Γ(X, W)`
with values in the sections of `N` over an open `U` of `T` mapping into `W` restricts to one with
values in the sections over a smaller open `U'`. -/
noncomputable def restrictDerivation (hWV : W ≤ f ⁻¹ᵁ V) {U U' : T.Opens} (hUW : U ≤ a ⁻¹ᵁ W)
    (hU'W : U' ≤ a ⁻¹ᵁ W) (hU'U : U' ≤ U)
    (δ : letI := algebraAppLE f hWV
      letI := moduleAppLE a N hUW
      letI := moduleAppLEBase f a N hWV hUW
      Derivation Γ(S, V) Γ(X, W) Γ(N, U)) :
    letI := algebraAppLE f hWV
    letI := moduleAppLE a N hU'W
    letI := moduleAppLEBase f a N hWV hU'W
    Derivation Γ(S, V) Γ(X, W) Γ(N, U') :=
  letI := algebraAppLE f hWV
  letI := moduleAppLE a N hUW
  letI := moduleAppLE a N hU'W
  letI := moduleAppLEBase f a N hWV hUW
  letI := moduleAppLEBase f a N hWV hU'W
  letI := isScalarTowerAppLEBase f a N hWV hUW
  letI := isScalarTowerAppLEBase f a N hWV hU'W
  (restrictLinearMap a N hUW hU'W hU'U).compDer δ

/-- The underlying map of a restricted derivation is the derivation followed by restriction of
sections. -/
theorem restrictDerivation_apply (hWV : W ≤ f ⁻¹ᵁ V) {U U' : T.Opens} (hUW : U ≤ a ⁻¹ᵁ W)
    (hU'W : U' ≤ a ⁻¹ᵁ W) (hU'U : U' ≤ U)
    (δ : letI := algebraAppLE f hWV
      letI := moduleAppLE a N hUW
      letI := moduleAppLEBase f a N hWV hUW
      Derivation Γ(S, V) Γ(X, W) Γ(N, U)) (b : Γ(X, W)) :
    restrictDerivation f a N hWV hUW hU'W hU'U δ b
      = (N.presheaf.map (homOfLE hU'U).op).hom (δ b) :=
  rfl

/-- The scalar tower `Γ(S, V) → Γ(X, W) → Γ(X, X.basicOpen g)`. -/
theorem isScalarTower_appLE_basicOpen (hWV : W ≤ f ⁻¹ᵁ V) (g : Γ(X, W)) :
    letI := algebraAppLE f hWV
    letI := algebraAppLE f ((X.basicOpen_le g).trans hWV)
    IsScalarTower Γ(S, V) Γ(X, W) Γ(X, X.basicOpen g) := by
  let := algebraAppLE f hWV
  let := algebraAppLE f ((X.basicOpen_le g).trans hWV)
  refine IsScalarTower.of_algebraMap_eq fun c ↦ ?_
  change (f.appLE V (X.basicOpen g) ((X.basicOpen_le g).trans hWV)).hom c
      = (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom ((f.appLE V W hWV).hom c)
  rw [← CommRingCat.comp_apply, f.appLE_map]

variable (hWV : W ≤ f ⁻¹ᵁ V) (hW : IsAffineOpen W) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W)
  (δ : letI := algebraAppLE f hWV
    letI := moduleAppLE a N hUW
    letI := moduleAppLEBase f a N hWV hUW
    Derivation Γ(S, V) Γ(X, W) Γ(N, (⊤ : T.Opens)))

/-- **The extension of a derivation to a basic open.** For `W` an affine open of `X` and `g` a
section of `𝒪_X` over `W`, a `Γ(S, V)`-derivation `δ` of `Γ(X, W)` with values in the sections of
`N` over the preimage of `W` extends to a `Γ(S, V)`-derivation of `Γ(X, X.basicOpen g)` with
values in the sections over the preimage of `X.basicOpen g`.

The extension exists and is unique because `Γ(X, X.basicOpen g)` is a localization of
`Γ(X, W)`. -/
noncomputable def basicOpenD (g : Γ(X, W)) :
    letI := algebraAppLE f ((X.basicOpen_le g).trans hWV)
    letI := moduleAppLE a N (le_refl (a ⁻¹ᵁ X.basicOpen g))
    letI := moduleAppLEBase f a N hWV
      ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le
    Derivation Γ(S, V) Γ(X, X.basicOpen g) Γ(N, a ⁻¹ᵁ X.basicOpen g) :=
  letI := algebraAppLE f hWV
  letI := algebraAppLE f ((X.basicOpen_le g).trans hWV)
  letI := isScalarTower_appLE_basicOpen f hWV g
  letI := moduleAppLE a N (le_refl (a ⁻¹ᵁ X.basicOpen g))
  letI := moduleAppLE a N ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le
  letI := moduleAppLEBase f a N hWV ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le
  letI := isScalarTowerAppLEBase f a N hWV
    ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le
  letI := isScalarTower_basicOpen a N g (le_refl (a ⁻¹ᵁ X.basicOpen g))
  haveI := hW.isLocalization_basicOpen g
  derivationLocalizationLift Γ(X, X.basicOpen g) (Submonoid.powers g)
    (restrictDerivation f a N hWV hUW
      ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le le_top δ)

/-- The extension of `δ` to a basic open of `W` restricts to `δ` along `Γ(X, W) →
Γ(X, X.basicOpen g)`. -/
theorem basicOpenD_map (g b : Γ(X, W)) :
    basicOpenD f a N hWV hW hUW δ g ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom b)
      = (N.presheaf.map (homOfLE (le_top : a ⁻¹ᵁ X.basicOpen g ≤ ⊤)).op).hom (δ b) := by
  let := algebraAppLE f hWV
  let := algebraAppLE f ((X.basicOpen_le g).trans hWV)
  let := isScalarTower_appLE_basicOpen f hWV g
  let := moduleAppLE a N (le_refl (a ⁻¹ᵁ X.basicOpen g))
  let := moduleAppLE a N ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le
  let := moduleAppLEBase f a N hWV ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le
  let := isScalarTowerAppLEBase f a N hWV
    ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le
  let := isScalarTower_basicOpen a N g (le_refl (a ⁻¹ᵁ X.basicOpen g))
  have := hW.isLocalization_basicOpen g
  exact derivationLocalizationLift_apply Γ(X, X.basicOpen g) (Submonoid.powers g) _ b

/-- The Leibniz rule for the extension of `δ` to a basic open, with the action of
`Γ(X, X.basicOpen g)` written out through `a.appLE`. -/
theorem basicOpenD_mul (g : Γ(X, W)) (x y : Γ(X, X.basicOpen g)) :
    basicOpenD f a N hWV hW hUW δ g (x * y)
      = (a.appLE (X.basicOpen g) (a ⁻¹ᵁ X.basicOpen g) le_rfl).hom x •
          basicOpenD f a N hWV hW hUW δ g y
        + (a.appLE (X.basicOpen g) (a ⁻¹ᵁ X.basicOpen g) le_rfl).hom y •
          basicOpenD f a N hWV hW hUW δ g x :=
  let := algebraAppLE f ((X.basicOpen_le g).trans hWV)
  let := moduleAppLE a N (le_refl (a ⁻¹ᵁ X.basicOpen g))
  let := moduleAppLEBase f a N hWV ((Opens.map a.base).map (homOfLE (X.basicOpen_le g))).le
  (basicOpenD f a N hWV hW hUW δ g).leibniz x y

/-- **The extensions of `δ` to two basic opens agree.** If the basic open of `g'` is contained in
the basic open of `g`, then on the sections of `N` over any open `U` of `T` mapping into both, the
extension of `δ` attached to `g` restricts to the extension attached to `g'`.

Both sides satisfy the Leibniz rule as functions of `y` and agree on the sections restricted from
`W`, so they agree because `Γ(X, X.basicOpen g)` is a localization of `Γ(X, W)`. -/
theorem map_basicOpenD (g g' : Γ(X, W)) (hle : X.basicOpen g' ≤ X.basicOpen g) {U : T.Opens}
    (hUg : U ≤ a ⁻¹ᵁ X.basicOpen g) (hUg' : U ≤ a ⁻¹ᵁ X.basicOpen g')
    (y : Γ(X, X.basicOpen g)) :
    (N.presheaf.map (homOfLE hUg).op).hom (basicOpenD f a N hWV hW hUW δ g y)
      = (N.presheaf.map (homOfLE hUg').op).hom
          (basicOpenD f a N hWV hW hUW δ g' ((X.presheaf.map (homOfLE hle).op).hom y)) := by
  have key1 : ∀ z : Γ(X, X.basicOpen g),
      (T.presheaf.map (homOfLE hUg).op).hom
          ((a.appLE (X.basicOpen g) (a ⁻¹ᵁ X.basicOpen g) le_rfl).hom z)
        = (a.appLE (X.basicOpen g) U hUg).hom z := fun z ↦ by
    rw [← CommRingCat.comp_apply, a.appLE_map]
  have key2 : ∀ z : Γ(X, X.basicOpen g),
      (T.presheaf.map (homOfLE hUg').op).hom
          ((a.appLE (X.basicOpen g') (a ⁻¹ᵁ X.basicOpen g') le_rfl).hom
            ((X.presheaf.map (homOfLE hle).op).hom z))
        = (a.appLE (X.basicOpen g) U hUg).hom z := fun z ↦ by
    rw [← CommRingCat.comp_apply, a.appLE_map, ← CommRingCat.comp_apply, a.map_appLE]
  refine sub_eq_zero.mp (eq_zero_of_leibniz_basicOpen' a N hW g hUg
    (fun z ↦ (N.presheaf.map (homOfLE hUg).op).hom (basicOpenD f a N hWV hW hUW δ g z)
      - (N.presheaf.map (homOfLE hUg').op).hom
          (basicOpenD f a N hWV hW hUW δ g' ((X.presheaf.map (homOfLE hle).op).hom z)))
    (fun z₁ z₂ ↦ ?_) (fun b ↦ ?_) y)
  · rw [basicOpenD_mul, map_add, Scheme.Modules.map_smul, Scheme.Modules.map_smul, key1, key1,
      map_mul, basicOpenD_mul, map_add, Scheme.Modules.map_smul, Scheme.Modules.map_smul,
      key2, key2, smul_sub, smul_sub]
    abel
  · have hb : (X.presheaf.map (homOfLE hle).op).hom
        ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom b)
          = (X.presheaf.map (homOfLE (X.basicOpen_le g')).op).hom b := by
      rw [← Functor.map_comp_apply]
      rfl
    rw [basicOpenD_map, hb, basicOpenD_map, ← Functor.map_comp_apply, ← Functor.map_comp_apply]
    exact sub_eq_zero.mpr rfl

/-- `Stacks.Smooth.map_basicOpenD` over the full preimage of the smaller basic open. -/
theorem map_basicOpenD' (g g' : Γ(X, W)) (hle : X.basicOpen g' ≤ X.basicOpen g)
    (y : Γ(X, X.basicOpen g)) :
    (N.presheaf.map (homOfLE ((Opens.map a.base).map (homOfLE hle)).le).op).hom
        (basicOpenD f a N hWV hW hUW δ g y)
      = basicOpenD f a N hWV hW hUW δ g' ((X.presheaf.map (homOfLE hle).op).hom y) := by
  rw [map_basicOpenD f a N hWV hW hUW δ g g' hle (U := a ⁻¹ᵁ X.basicOpen g')
      ((Opens.map a.base).map (homOfLE hle)).le le_rfl,
    show homOfLE (le_refl (a ⁻¹ᵁ X.basicOpen g')) = 𝟙 _ from rfl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- The extension of `δ` to a basic open kills the image of `Γ(S, V)`. -/
theorem basicOpenD_appLE_base (g : Γ(X, W)) (r : Γ(S, V)) :
    basicOpenD f a N hWV hW hUW δ g
        ((f.appLE V (X.basicOpen g) ((X.basicOpen_le g).trans hWV)).hom r) = 0 := by
  let := algebraAppLE f hWV
  let := moduleAppLE a N hUW
  let := moduleAppLEBase f a N hWV hUW
  have hδ : δ ((f.appLE V W hWV).hom r) = 0 := δ.map_algebraMap r
  rw [show (f.appLE V (X.basicOpen g) ((X.basicOpen_le g).trans hWV)).hom r
      = (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom ((f.appLE V W hWV).hom r) by
        rw [← CommRingCat.comp_apply, f.appLE_map], basicOpenD_map, hδ, map_zero]

/-- Restricting sections of `𝒪_S` before applying `f.appLE` is `f.appLE` on the larger open. -/
private theorem appLE_restrict_apply {U U' : S.Opens} {Y : X.Opens} (hU : U ≤ U')
    (h : Y ≤ f ⁻¹ᵁ U) (h' : Y ≤ f ⁻¹ᵁ U') (x : Γ(S, U')) :
    (f.appLE U Y h).hom ((S.presheaf.map (homOfLE hU).op).hom x) = (f.appLE U' Y h').hom x := by
  rw [← CommRingCat.comp_apply, f.map_appLE]

/-- **The extension of `δ` kills the sections coming from a basic open of `V`.** If the basic open
of `g` lies over the basic open of a section `s` of `𝒪_S` over the affine open `V`, then the
extension of `δ` to `X.basicOpen g` kills the image of `Γ(S, S.basicOpen s)`.

The ring `Γ(S, S.basicOpen s)` is the localization of `Γ(S, V)` away from `s`, and the image of
`s` in `Γ(X, X.basicOpen g)` is a unit, so the Leibniz rule propagates the vanishing on `Γ(S, V)`
to the whole localization. -/
theorem basicOpenD_appLE_basicOpen (hV : IsAffineOpen V) (g : Γ(X, W)) (s : Γ(S, V))
    (hgs : X.basicOpen g ≤ f ⁻¹ᵁ S.basicOpen s) (r : Γ(S, S.basicOpen s)) :
    basicOpenD f a N hWV hW hUW δ g
      ((f.appLE (S.basicOpen s) (X.basicOpen g) hgs).hom r) = 0 := by
  have hgV : X.basicOpen g ≤ f ⁻¹ᵁ V := (X.basicOpen_le g).trans hWV
  have hunit : IsUnit ((f.appLE V (X.basicOpen g) hgV).hom s) := by
    have h1 : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le (f.app V s))).op).hom
        (f.app V s)) := X.toRingedSpace.isUnit_res_basicOpen _
    have h2 : X.basicOpen g ≤ X.basicOpen ((f.app V s)) := by
      rw [← Scheme.preimage_basicOpen]
      exact hgs
    have := h1.map (X.presheaf.map (homOfLE h2).op).hom
    rwa [← CommRingCat.comp_apply, ← Functor.map_comp,
      show (homOfLE (X.basicOpen_le (f.app V s))).op ≫ (homOfLE h2).op
        = (homOfLE (hgV.trans (le_refl (f ⁻¹ᵁ V)))).op from rfl] at this
  have := hV.isLocalization_basicOpen s
  obtain ⟨⟨x, c⟩, hc⟩ := IsLocalization.surj (Submonoid.powers s) r
  obtain ⟨n, hn⟩ := c.2
  have hcunit : IsUnit ((f.appLE V (X.basicOpen g) hgV).hom (c : Γ(S, V))) := by
    rw [← hn, map_pow]
    exact hunit.pow n
  have hmul : (f.appLE (S.basicOpen s) (X.basicOpen g) hgs).hom r
        * (f.appLE V (X.basicOpen g) hgV).hom (c : Γ(S, V))
      = (f.appLE V (X.basicOpen g) hgV).hom x := by
    rw [← appLE_restrict_apply f (S.basicOpen_le s) hgs hgV,
      ← appLE_restrict_apply f (S.basicOpen_le s) hgs hgV, ← map_mul]
    exact congrArg _ hc
  have hkey := basicOpenD_mul f a N hWV hW hUW δ g
    ((f.appLE (S.basicOpen s) (X.basicOpen g) hgs).hom r)
    ((f.appLE V (X.basicOpen g) hgV).hom (c : Γ(S, V)))
  rw [hmul, basicOpenD_appLE_base, basicOpenD_appLE_base, smul_zero, zero_add] at hkey
  exact (hcunit.map (a.appLE (X.basicOpen g) (a ⁻¹ᵁ X.basicOpen g) le_rfl).hom).smul_eq_zero.mp
    hkey.symm

/-- **The extension of `δ` kills the base.** For every open `V'` of `S` over which the basic open
of `g` lies, the extension of `δ` to `X.basicOpen g` kills the image of `Γ(S, V')`.

This is checked locally: the basic opens of `W` that lie over a basic open of the affine open `V`
contained in `V'` cover `X.basicOpen g`, and on each of them
`Stacks.Smooth.basicOpenD_appLE_basicOpen` applies. -/
theorem basicOpenD_appLE (hV : IsAffineOpen V) (g : Γ(X, W)) {V' : S.Opens}
    (hgV' : X.basicOpen g ≤ f ⁻¹ᵁ V') (r : Γ(S, V')) :
    basicOpenD f a N hWV hW hUW δ g ((f.appLE V' (X.basicOpen g) hgV').hom r) = 0 := by
  have hgV : X.basicOpen g ≤ f ⁻¹ᵁ V := (X.basicOpen_le g).trans hWV
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun p : {p : Γ(X, W) × Γ(S, V) // X.basicOpen p.1 ≤ X.basicOpen g ∧
        X.basicOpen p.1 ≤ f ⁻¹ᵁ S.basicOpen p.2 ∧ S.basicOpen p.2 ≤ V'} ↦
      a ⁻¹ᵁ X.basicOpen p.1.1)
    (a ⁻¹ᵁ X.basicOpen g) (fun p ↦ homOfLE ((Opens.map a.base).map (homOfLE p.2.1)).le)
    (fun t ht ↦ ?_) _ 0 (fun p ↦ ?_)
  · obtain ⟨s, hsV', hsmem⟩ := hV.exists_basicOpen_le (V := V')
      ⟨f.base (a.base t), hgV' ht⟩ (hgV ht)
    obtain ⟨g'', hg''le, hg''mem⟩ := hW.exists_basicOpen_le
      (V := X.basicOpen g ⊓ f ⁻¹ᵁ S.basicOpen s) ⟨a.base t, ht, hsmem⟩
      (X.basicOpen_le g ht)
    exact Opens.mem_iSup.mpr
      ⟨⟨(g'', s), hg''le.trans inf_le_left, hg''le.trans inf_le_right, hsV'⟩, hg''mem⟩
  · rw [map_zero, map_basicOpenD' f a N hWV hW hUW δ g p.1.1 p.2.1,
      ← CommRingCat.comp_apply, f.appLE_map,
      ← appLE_restrict_apply f p.2.2.2 p.2.2.1 (p.2.1.trans hgV') r,
      basicOpenD_appLE_basicOpen f a N hWV hW hUW δ hV]

/-! ### Gluing the extensions over the basic opens of `W` -/

/-- **The extensions of `δ` to the basic opens of `W` glue.** For every open `V₀` of `X` and every
section `x` of `𝒪_X` over `V₀` there is a unique section of `N` over `a ⁻¹ᵁ V₀` restricting, on
the preimage of each basic open of `W` contained in `V₀`, to the extension of `δ` applied to the
restriction of `x`.

The preimages of those basic opens cover `a ⁻¹ᵁ V₀` by
`Stacks.Smooth.preimage_le_iSup_preimage_basicOpen`, the two extensions attached to `g` and `g'`
agree on the preimage of `X.basicOpen (g * g')` by `Stacks.Smooth.map_basicOpenD`, and `N` is a
sheaf. -/
theorem existsUnique_glueD (V₀ : X.Opens) (x : Γ(X, V₀)) :
    ∃! u : Γ(N, a ⁻¹ᵁ V₀), ∀ (g : Γ(X, W)) (hg : X.basicOpen g ≤ V₀),
      (N.presheaf.map (homOfLE ((Opens.map a.base).map (homOfLE hg)).le).op).hom u
        = basicOpenD f a N hWV hW hUW δ g ((X.presheaf.map (homOfLE hg).op).hom x) := by
  have hcompat : TopCat.Presheaf.IsCompatible N.presheaf
      (fun g : {g : Γ(X, W) // X.basicOpen g ≤ V₀} ↦ a ⁻¹ᵁ X.basicOpen g.1)
      (fun g ↦ basicOpenD f a N hWV hW hUW δ g.1
        ((X.presheaf.map (homOfLE g.2).op).hom x)) := by
    intro i j
    have hmul : X.basicOpen (i.1 * j.1) = X.basicOpen i.1 ⊓ X.basicOpen j.1 :=
      X.basicOpen_mul _ _
    have hle₁ : X.basicOpen (i.1 * j.1) ≤ X.basicOpen i.1 := hmul.le.trans inf_le_left
    have hle₂ : X.basicOpen (i.1 * j.1) ≤ X.basicOpen j.1 := hmul.le.trans inf_le_right
    have hinf : a ⁻¹ᵁ X.basicOpen i.1 ⊓ a ⁻¹ᵁ X.basicOpen j.1
        ≤ a ⁻¹ᵁ X.basicOpen (i.1 * j.1) := by
      rw [hmul, Scheme.Hom.preimage_inf]
    have hx : (X.presheaf.map (homOfLE hle₁).op).hom
          ((X.presheaf.map (homOfLE i.2).op).hom x)
        = (X.presheaf.map (homOfLE hle₂).op).hom
          ((X.presheaf.map (homOfLE j.2).op).hom x) := by
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
      rfl
    change (N.presheaf.map (homOfLE (inf_le_left :
          a ⁻¹ᵁ X.basicOpen i.1 ⊓ a ⁻¹ᵁ X.basicOpen j.1 ≤ _)).op).hom _
        = (N.presheaf.map (homOfLE (inf_le_right :
          a ⁻¹ᵁ X.basicOpen i.1 ⊓ a ⁻¹ᵁ X.basicOpen j.1 ≤ _)).op).hom _
    rw [map_basicOpenD f a N hWV hW hUW δ i.1 (i.1 * j.1) hle₁ inf_le_left hinf,
      map_basicOpenD f a N hWV hW hUW δ j.1 (i.1 * j.1) hle₂ inf_le_right hinf, hx]
  obtain ⟨u, hu, huniq⟩ := TopCat.Sheaf.existsUnique_gluing'
    (F := (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf _ T))
    (fun g : {g : Γ(X, W) // X.basicOpen g ≤ V₀} ↦ a ⁻¹ᵁ X.basicOpen g.1)
    (a ⁻¹ᵁ V₀) (fun g ↦ homOfLE ((Opens.map a.base).map (homOfLE g.2)).le)
    (preimage_le_iSup_preimage_basicOpen a hW hUW V₀) _ hcompat
  exact ⟨u, fun g hg ↦ hu ⟨g, hg⟩, fun v hv ↦ huniq v fun g ↦ hv g.1 g.2⟩

/-- **The sectionwise differential attached to `δ`.** For an open `V₀` of `X`, this is the map
`Γ(X, V₀) → Γ(N, a ⁻¹ᵁ V₀)` obtained by gluing the extensions of `δ` to the basic opens of `W`
contained in `V₀`. -/
noncomputable def glueD (V₀ : X.Opens) (x : Γ(X, V₀)) : Γ(N, a ⁻¹ᵁ V₀) :=
  (existsUnique_glueD f a N hWV hW hUW δ V₀ x).choose

/-- The glued differential restricts, on the preimage of a basic open of `W`, to the extension of
`δ` to that basic open. -/
theorem glueD_restrict (V₀ : X.Opens) (x : Γ(X, V₀)) (g : Γ(X, W))
    (hg : X.basicOpen g ≤ V₀) :
    (N.presheaf.map (homOfLE ((Opens.map a.base).map (homOfLE hg)).le).op).hom
        (glueD f a N hWV hW hUW δ V₀ x)
      = basicOpenD f a N hWV hW hUW δ g ((X.presheaf.map (homOfLE hg).op).hom x) :=
  (existsUnique_glueD f a N hWV hW hUW δ V₀ x).choose_spec.1 g hg

/-- The glued differential is the only section with the restriction property of
`Stacks.Smooth.glueD_restrict`. -/
theorem glueD_unique (V₀ : X.Opens) (x : Γ(X, V₀)) (u : Γ(N, a ⁻¹ᵁ V₀))
    (hu : ∀ (g : Γ(X, W)) (hg : X.basicOpen g ≤ V₀),
      (N.presheaf.map (homOfLE ((Opens.map a.base).map (homOfLE hg)).le).op).hom u
        = basicOpenD f a N hWV hW hUW δ g ((X.presheaf.map (homOfLE hg).op).hom x)) :
    u = glueD f a N hWV hW hUW δ V₀ x :=
  (existsUnique_glueD f a N hWV hW hUW δ V₀ x).choose_spec.2 u hu

/-- The glued differential is additive. -/
theorem glueD_add (V₀ : X.Opens) (x y : Γ(X, V₀)) :
    glueD f a N hWV hW hUW δ V₀ (x + y)
      = glueD f a N hWV hW hUW δ V₀ x + glueD f a N hWV hW hUW δ V₀ y := by
  refine (glueD_unique f a N hWV hW hUW δ V₀ (x + y) _ fun g hg ↦ ?_).symm
  rw [map_add, glueD_restrict, glueD_restrict, map_add, map_add]

/-- The scalars of the Leibniz rule for the glued differential, read on a basic open of `W`. -/
theorem appLE_restrict (V₀ : X.Opens) (x : Γ(X, V₀)) (g : Γ(X, W))
    (hg : X.basicOpen g ≤ V₀) :
    (T.presheaf.map (homOfLE ((Opens.map a.base).map (homOfLE hg)).le).op).hom
        ((a.appLE V₀ (a ⁻¹ᵁ V₀) le_rfl).hom x)
      = (a.appLE (X.basicOpen g) (a ⁻¹ᵁ X.basicOpen g) le_rfl).hom
        ((X.presheaf.map (homOfLE hg).op).hom x) := by
  rw [← CommRingCat.comp_apply, a.appLE_map, ← CommRingCat.comp_apply, a.map_appLE]

/-- **The Leibniz rule for the glued differential.** -/
theorem glueD_mul (V₀ : X.Opens) (x y : Γ(X, V₀)) :
    glueD f a N hWV hW hUW δ V₀ (x * y)
      = (a.appLE V₀ (a ⁻¹ᵁ V₀) le_rfl).hom x • glueD f a N hWV hW hUW δ V₀ y
        + (a.appLE V₀ (a ⁻¹ᵁ V₀) le_rfl).hom y • glueD f a N hWV hW hUW δ V₀ x := by
  refine (glueD_unique f a N hWV hW hUW δ V₀ (x * y) _ fun g hg ↦ ?_).symm
  rw [map_add, Scheme.Modules.map_smul, Scheme.Modules.map_smul, glueD_restrict, glueD_restrict,
    appLE_restrict, appLE_restrict, map_mul, basicOpenD_mul]

/-- **The glued differential commutes with restriction of sections.** -/
theorem glueD_map {V₀ V₁ : X.Opens} (hV : V₁ ≤ V₀) (x : Γ(X, V₀)) :
    (N.presheaf.map (homOfLE ((Opens.map a.base).map (homOfLE hV)).le).op).hom
        (glueD f a N hWV hW hUW δ V₀ x)
      = glueD f a N hWV hW hUW δ V₁ ((X.presheaf.map (homOfLE hV).op).hom x) := by
  refine glueD_unique f a N hWV hW hUW δ V₁ _ _ fun g hg ↦ ?_
  rw [← Functor.map_comp_apply,
    show (homOfLE ((Opens.map a.base).map (homOfLE hV)).le).op
        ≫ (homOfLE ((Opens.map a.base).map (homOfLE hg)).le).op
      = (homOfLE ((Opens.map a.base).map (homOfLE (hg.trans hV))).le).op from rfl,
    glueD_restrict, ← Functor.map_comp_apply]
  rfl

/-- **The glued differential kills the base.** On the preimage of an open `V'` of `S` it kills the
image of `Γ(S, V')`. -/
theorem glueD_app (hV : IsAffineOpen V) (V' : S.Opens) (r : Γ(S, V')) :
    glueD f a N hWV hW hUW δ (f ⁻¹ᵁ V') ((f.app V').hom r) = 0 := by
  refine (glueD_unique f a N hWV hW hUW δ (f ⁻¹ᵁ V') _ 0 fun g hg ↦ ?_).symm
  rw [map_zero, show (X.presheaf.map (homOfLE hg).op).hom ((f.app V').hom r)
      = (f.appLE V' (X.basicOpen g) hg).hom r by rw [← CommRingCat.comp_apply]; rfl,
    basicOpenD_appLE f a N hWV hW hUW δ hV]

/-! ### The sheaf derivation attached to `δ` -/

/-- The glued differential, as a family of additive maps with values in the pushforward of `N`.
This is the shape in which it is a relative derivation of `𝒪_X`. -/
noncomputable def glueDHom (V₀ : X.Opens) :
    Γ(X, V₀) →+ Γ((Scheme.Modules.pushforward a).obj N, V₀) :=
  AddMonoidHom.mk' (glueD f a N hWV hW hUW δ V₀) (glueD_add f a N hWV hW hUW δ V₀)

/-- The Leibniz rule for `Stacks.Smooth.glueDHom`, for the module structure on the pushforward. -/
theorem glueDHom_mul (V₀ : X.Opens) (x y : Γ(X, V₀)) :
    glueDHom f a N hWV hW hUW δ V₀ (x * y)
      = x • glueDHom f a N hWV hW hUW δ V₀ y + y • glueDHom f a N hWV hW hUW δ V₀ x := by
  change glueD f a N hWV hW hUW δ V₀ (x * y)
      = (a.app V₀).hom x • glueD f a N hWV hW hUW δ V₀ y
        + (a.app V₀).hom y • glueD f a N hWV hW hUW δ V₀ x
  rw [glueD_mul, a.app_eq_appLE]

/-- `Stacks.Smooth.glueDHom` commutes with restriction of sections. -/
theorem glueDHom_map {V₀ V₁ : (X.Opens)ᵒᵖ} (h : V₀ ⟶ V₁) (x : Γ(X, V₀.unop)) :
    (((Scheme.Modules.pushforward a).obj N).presheaf.map h).hom
        (glueDHom f a N hWV hW hUW δ V₀.unop x)
      = glueDHom f a N hWV hW hUW δ V₁.unop ((X.presheaf.map h).hom x) :=
  glueD_map f a N hWV hW hUW δ h.unop.le x

/-- `Stacks.Smooth.glueDHom` kills the image of `Γ(S, V')` for every open `V'` of `S`. -/
theorem glueDHom_app (hV : IsAffineOpen V) (V' : S.Opens) (r : Γ(S, V')) :
    glueDHom f a N hWV hW hUW δ (f ⁻¹ᵁ V') ((f.app V').hom r) = 0 :=
  glueD_app f a N hWV hW hUW δ hV V' r

/-- **`Stacks.Smooth.glueDHom` kills the image of `f⁻¹𝒪_S`.** This is
`Stacks.Smooth.apply_inverseImageStructureApp_eq_zero` applied to the glued differential. -/
theorem glueDHom_inverseImageStructureApp (hV : IsAffineOpen V) (V₀ : (X.Opens)ᵒᵖ)
    (t : (inverseImageSheaf (ringedSpaceHom f)).obj.obj V₀) :
    glueDHom f a N hWV hW hUW δ V₀.unop ((inverseImageStructureApp f V₀).hom t) = 0 :=
  apply_inverseImageStructureApp_eq_zero f ((Scheme.Modules.pushforward a).obj N)
    (glueDHom f a N hWV hW hUW δ) (glueDHom_mul f a N hWV hW hUW δ)
    (fun h x ↦ glueDHom_map f a N hWV hW hUW δ h x)
    (glueDHom_app f a N hWV hW hUW δ hV) V₀ t

/-- **The relative derivation of `𝒪_X` attached to `δ`.** The glued differential of `δ` is a
derivation of `𝒪_X` relative to `f⁻¹𝒪_S` with values in `a_*N`. -/
noncomputable def glueDerivation (hV : IsAffineOpen V) :
    ((Scheme.Modules.pushforward a).obj N).val.Derivation'
      (inverseImageStructureMap (ringedSpaceHom f)).hom where
  d {V₀} := glueDHom f a N hWV hW hUW δ V₀.unop
  d_mul {V₀} x y := glueDHom_mul f a N hWV hW hUW δ V₀.unop x y
  d_map {_ _} h x := (glueDHom_map f a N hWV hW hUW δ h x).symm
  d_app {V₀} t := glueDHom_inverseImageStructureApp f a N hWV hW hUW δ hV V₀ t

/-! ### Existence of the morphism attached to a derivation -/

/-- The glued differential over `W` restricts to `δ` on the sections of `N` over `T`. -/
theorem map_glueD_top (b : Γ(X, W)) :
    (N.presheaf.map (homOfLE hUW).op).hom (glueD f a N hWV hW hUW δ W b) = δ b := by
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun g : {g : Γ(X, W) // X.basicOpen g ≤ W} ↦ a ⁻¹ᵁ X.basicOpen g.1) ⊤
    (fun _ ↦ homOfLE le_top)
    (hUW.trans (preimage_le_iSup_preimage_basicOpen a hW hUW W)) _ _ fun g ↦ ?_
  rw [← basicOpenD_map f a N hWV hW hUW δ g.1 b,
    ← glueD_restrict f a N hWV hW hUW δ W b g.1 (X.basicOpen_le g.1),
    ← Functor.map_comp_apply]
  rfl

include hWV hW in
/-- **Existence in the corepresentation of derivations by `a^*Ω_{X/S}`.** Let `f : X ⟶ S` be a
morphism of schemes, let `V` be an affine open of `S` and `W` an affine open of `X` with
`W ≤ f ⁻¹ᵁ V`, let `a : T ⟶ X` be a morphism mapping into `W` and let `N` be a sheaf of modules
on `T`. Every `Γ(S, V)`-derivation of `Γ(X, W)` with values in `Γ(N, ⊤)` is induced by a morphism
`a^*Ω_{X/S} ⟶ N` composed with the pullback `Stacks.Smooth.pullbackD` of the universal
differential.

Together with `Stacks.Smooth.pullbackCotangentSheaf_hom_ext` this is the full corepresentability
statement, which is the form of the affine computation of [Stacks Project, Tag 01UM] that
[Stacks Project, Tag 02H6] consumes. -/
theorem exists_hom_pullbackCotangentSheaf (hV : IsAffineOpen V) :
    ∃ φ : pullbackCotangentSheaf f a ⟶ N,
      ∀ b : Γ(X, W), φ.app ⊤ (pullbackD f a W hUW b) = δ b := by
  obtain ⟨ψ, hψ, -⟩ := Stacks.Sheaves.Differentials.universalDerivation_isUniversal
    (inverseImageSheaf (ringedSpaceHom f)) _ (inverseImageStructureMap (ringedSpaceHom f))
    ((Scheme.Modules.pushforward a).obj N) (glueDerivation f a N hWV hW hUW δ hV)
  refine ⟨(pullbackCotangentSheafHomEquiv f a N).symm ψ, fun b ↦ ?_⟩
  have hψφ : pullbackCotangentSheafHomEquiv f a N
      ((pullbackCotangentSheafHomEquiv f a N).symm ψ) = ψ := Equiv.apply_symm_apply _ _
  have hkey : ((pullbackCotangentSheafHomEquiv f a N).symm ψ).app (a ⁻¹ᵁ W)
        (pullbackD f a W (le_refl (a ⁻¹ᵁ W)) b)
      = glueD f a N hWV hW hUW δ W b := by
    rw [pullbackD_self, ← pullbackCotangentSheafHomEquiv_app, hψφ]
    exact PresheafOfModules.Derivation.congr_d hψ b
  rw [← map_pullbackD f a W (le_refl (a ⁻¹ᵁ W)) hUW hUW b,
    app_map_section ((pullbackCotangentSheafHomEquiv f a N).symm ψ) hUW, hkey, map_glueD_top]

include hWV hW in
/-- **Corepresentability of derivations by `a^*Ω_{X/S}`.** Exactly one morphism
`a^*Ω_{X/S} ⟶ N` induces a given `Γ(S, V)`-derivation of `Γ(X, W)` with values in `Γ(N, ⊤)`.

Existence is `Stacks.Smooth.exists_hom_pullbackCotangentSheaf` and uniqueness is
`Stacks.Smooth.pullbackCotangentSheaf_hom_ext`. This is the affine computation of
[Stacks Project, Tag 01UM] in the form that [Stacks Project, Tag 02H6] consumes. -/
theorem existsUnique_hom_pullbackCotangentSheaf (hV : IsAffineOpen V) :
    ∃! φ : pullbackCotangentSheaf f a ⟶ N,
      ∀ b : Γ(X, W), φ.app ⊤ (pullbackD f a W hUW b) = δ b := by
  obtain ⟨φ, hφ⟩ := exists_hom_pullbackCotangentSheaf f a N hWV hW hUW δ hV
  exact ⟨φ, hφ, fun ψ hψ ↦ pullbackCotangentSheaf_hom_ext f a N hW hUW
    fun b ↦ (hψ b).trans (hφ b).symm⟩

end Extension

end Stacks.Smooth

end
