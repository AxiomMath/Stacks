module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobalConjugationArrow

/-!
# The modified lift of Tag 0CK1 is natural in the thickening

Let `i₁ : X ⟶ X₁'` and `i₂ : X ⟶ X₂'` be two first-order thickenings of one scheme `X`, let
`j₁ : Y ⟶ Y₁'` and `j₂ : Y ⟶ Y₂'` be two morphisms out of one scheme `Y`, and let
`w : X₂' ⟶ X₁'`, `v : Y₂' ⟶ Y₁'` be vertical maps restricting to the identities,
`i₂ ≫ w = i₁` and `j₂ ≫ v = j₁`. This is the shape of a *pushforward of a pair of deformations
along a morphism of `𝒞_Λ`*: `X₁'` and `Y₁'` are the total spaces of two deformations over `A`,
`X₂'` and `Y₂'` those of their base changes to `B`, and `w`, `v` are the projections of the base
changes.

For an `𝒪_X`-linear map `θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}` the modified lift `θ ⬝ a'` of
[Stacks Project, Tag 0CK1] is `Stacks.Thickenings.derivationActionGlobal`, whose comorphism is
`(a')^♯ + D_θ` with `D_θ` the perturbation `Stacks.Thickenings.derivationSection`. This file
proves that the construction is natural in the thickening: the relation
`Stacks.Thickenings.DerivationSectionsCorrespond` between a datum `θ₁` on the first situation and
a datum `θ₂` on the second — that `w^♯` carries the perturbation of `θ₁` to the perturbation of
`θ₂` — is **equivalent** to the commutativity

`(θ₂ ⬝ a₂) ≫ v = w ≫ (θ₁ ⬝ a₁)`

for one, equivalently every, pair of compatible lifts `a₂ ≫ v = w ≫ a₁`.

The relation mentions no lift at all, which is the point: the transport of the acting group of
[Stacks Project, Tag 0CK2] along a morphism of the base is a property of the two acting sections,
not of the lift it is first observed at.

## Main definitions

* `Stacks.Thickenings.DerivationSectionsCorrespond`: the perturbations of two data correspond
  under the vertical maps.

## Main results

* `Stacks.Thickenings.derivationActionGlobal_comp_of_correspond`: corresponding data act
  compatibly on every pair of compatible lifts.
* `Stacks.Thickenings.correspond_of_derivationActionGlobal_comp`: two data acting compatibly on
  one pair of compatible lifts correspond.
* `Stacks.Thickenings.derivationActionGlobal_comp_of_comp`: hence compatibility at one pair of
  lifts gives compatibility at every pair.
* `Stacks.Thickenings.correspond_add` and `Stacks.Thickenings.correspond_zero`: the relation is
  additive.

## Implementation notes

Both directions compare the comorphisms of the two morphisms `X₂' ⟶ Y₁'` over a pair of opens,
through `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`. The forward direction concludes with the
uniqueness statement `Stacks.Thickenings.eq_derivationActionGlobal` at the *zero* datum of the
mixed situation `(i₂, j₁)`, whose modified lift is the lift itself
(`Stacks.Thickenings.derivationActionGlobal_zero`): this is how an equality of two morphisms of
schemes with the same underlying map is read off their comorphisms without a separate extension
lemma.

## References

* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 04BZ](https://stacks.math.columbia.edu/tag/04BZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-! ### Opens -/

/-- A composite of comorphisms over pairs of opens, on a section. -/
theorem comp_appLE_apply {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (W : C.Opens)
    (U : B.Opens) (V : A.Opens) (h₁ : U ≤ g ⁻¹ᵁ W) (h₂ : V ≤ f ⁻¹ᵁ U)
    (h : V ≤ (f ≫ g) ⁻¹ᵁ W) (x : Γ(C, W)) :
    ((f ≫ g).appLE W V h).hom x = (f.appLE U V h₂).hom ((g.appLE W U h₁).hom x) :=
  (congrArg (fun z : Γ(C, W) ⟶ Γ(A, V) => z.hom x)
    (Scheme.Hom.appLE_comp_appLE f g W U V h₁ h₂)).symm

/-- **An open whose part on the subscheme maps into `W` maps into `W` under any lift.** A
first-order thickening is surjective on points, so `V ≤ a'⁻¹W` may be checked on `i⁻¹V`. -/
theorem le_preimage_of_preimage_le {X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'}
    {a : X ⟶ Y} {a' : X' ⟶ Y'} [IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥)
    (comm_a : i ≫ a' = a ≫ j) {W : Y'.Opens} {V : X'.Opens}
    (hU : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W)) : V ≤ a' ⁻¹ᵁ W := by
  intro x hx
  obtain ⟨y, rfl⟩ := (isThickening_of_ker_pow_eq_bot i inferInstance (n := 1) hsq).2 x
  have hy : j (a y) ∈ W := hU hx
  show a' (i y) ∈ W
  rw [← Scheme.Hom.comp_apply, comm_a, Scheme.Hom.comp_apply]
  exact hy

section BaseNaturality

variable {S₁ S₂ X X₁' X₂' Y Y₁' Y₂' : Scheme.{u}} {i₁ : X ⟶ X₁'} {i₂ : X ⟶ X₂'}
  {j₁ : Y ⟶ Y₁'} {j₂ : Y ⟶ Y₂'} {a : X ⟶ Y} {q₁ : Y₁' ⟶ S₁} {q₂ : Y₂' ⟶ S₂}
  [IsClosedImmersion i₁] [IsClosedImmersion i₂] {w : X₂' ⟶ X₁'} {v : Y₂' ⟶ Y₁'}

omit [IsClosedImmersion i₁] [IsClosedImmersion i₂] in
/-- The opens of the second situation over which the transported perturbation is read. -/
theorem preimage_le_preimage_of_vertical (hw : i₂ ≫ w = i₁) (hv : j₂ ≫ v = j₁)
    {W : Y₁'.Opens} {V : X₁'.Opens} (hU : i₁ ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j₁ ⁻¹ᵁ W)) :
    i₂ ⁻¹ᵁ (w ⁻¹ᵁ V) ≤ a ⁻¹ᵁ (j₂ ⁻¹ᵁ (v ⁻¹ᵁ W)) := by
  have h₁ : i₂ ⁻¹ᵁ (w ⁻¹ᵁ V) = i₁ ⁻¹ᵁ V := by rw [← hw]; rfl
  have h₂ : j₂ ⁻¹ᵁ (v ⁻¹ᵁ W) = j₁ ⁻¹ᵁ W := by rw [← hv]; rfl
  rw [h₁, h₂]
  exact hU

/-- **The perturbations of two data correspond under the vertical maps.** For data `θ₁` on the
first situation and `θ₂` on the second, `w^♯` carries the perturbation `D_{θ₁} g` of every
section `g` of `𝒪_{Y₁'}` to the perturbation `D_{θ₂} (v^♯ g)`. This is the commuting square of
[Stacks Project, Tag 04BZ], read on the perturbations of the global track; it mentions no lift. -/
def DerivationSectionsCorrespond (hsq₁ : i₁.ker ^ 2 = ⊥) (hsq₂ : i₂.ker ^ 2 = ⊥)
    (hw : i₂ ≫ w = i₁) (hv : j₂ ≫ v = j₁)
    (θ₁ : Smooth.pullbackCotangentSheaf (j₁ ≫ q₁) a ⟶ conormalModules i₁)
    (θ₂ : Smooth.pullbackCotangentSheaf (j₂ ≫ q₂) a ⟶ conormalModules i₂) : Prop :=
  ∀ (W : Y₁'.Opens) (V : X₁'.Opens) (hU : i₁ ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j₁ ⁻¹ᵁ W)) (g : Γ(Y₁', W)),
    (w.app V).hom (derivationSection hsq₁ θ₁ W V hU g) =
      derivationSection hsq₂ θ₂ (v ⁻¹ᵁ W) (w ⁻¹ᵁ V)
        (preimage_le_preimage_of_vertical hw hv hU) ((v.app W).hom g)

variable (hsq₁ : i₁.ker ^ 2 = ⊥) (hsq₂ : i₂.ker ^ 2 = ⊥) (hw : i₂ ≫ w = i₁) (hv : j₂ ≫ v = j₁)

/-- An open of `X₂'` over `a₁⁻¹W` lies over `v⁻¹W` under `a₂`, when `a₂ ≫ v = w ≫ a₁`. -/
private theorem le_preimage_of_comp_eq {a₁ : X₁' ⟶ Y₁'} {a₂ : X₂' ⟶ Y₂'}
    (hcomp : a₂ ≫ v = w ≫ a₁) {W : Y₁'.Opens} {V : X₂'.Opens} (hV : V ≤ w ⁻¹ᵁ (a₁ ⁻¹ᵁ W)) :
    V ≤ a₂ ⁻¹ᵁ (v ⁻¹ᵁ W) := by
  rw [← Scheme.Hom.comp_preimage, hcomp, Scheme.Hom.comp_preimage]
  exact hV

/-- The comorphisms of `a₂ ≫ v = w ≫ a₁` agree on sections, over a pair of opens. -/
private theorem appLE_comp_eq_of_comp_eq {a₁ : X₁' ⟶ Y₁'} {a₂ : X₂' ⟶ Y₂'}
    (hcomp : a₂ ≫ v = w ≫ a₁) (W : Y₁'.Opens) (U : X₁'.Opens) (V : X₂'.Opens)
    (hU : U ≤ a₁ ⁻¹ᵁ W) (hV : V ≤ w ⁻¹ᵁ U) (g : Γ(Y₁', W)) :
    (a₂.appLE (v ⁻¹ᵁ W) V (le_preimage_of_comp_eq hcomp (hV.trans (w.preimage_mono hU)))).hom
        ((v.app W).hom g) = (w.appLE U V hV).hom ((a₁.appLE W U hU).hom g) := by
  have hV' : V ≤ w ⁻¹ᵁ (a₁ ⁻¹ᵁ W) := hV.trans (w.preimage_mono hU)
  have e1 := comp_appLE_apply a₂ v W (v ⁻¹ᵁ W) V le_rfl (le_preimage_of_comp_eq hcomp hV')
    (show V ≤ (a₂ ≫ v) ⁻¹ᵁ W from le_preimage_of_comp_eq hcomp hV') g
  have e2 := comp_appLE_apply w a₁ W U V hU hV (show V ≤ (w ≫ a₁) ⁻¹ᵁ W from hV') g
  rw [Scheme.Hom.appLE_eq_app] at e1
  rw [← e1, ← e2]
  exact congrArg (fun z : Γ(Y₁', W) ⟶ Γ(X₂', V) => z.hom g) (appLE_congr_hom hcomp W V _ _)

/-- The comorphism of `(θ₂ ⬝ a₂) ≫ v` over a pair of opens. -/
private theorem appLE_derivationActionGlobal_comp
    (θ₂ : Smooth.pullbackCotangentSheaf (j₂ ≫ q₂) a ⟶ conormalModules i₂)
    {a₂ : X₂' ⟶ Y₂'} (ca₂ : i₂ ≫ a₂ = a ≫ j₂) (W : Y₁'.Opens) (V : X₂'.Opens)
    (hB : V ≤ a₂ ⁻¹ᵁ (v ⁻¹ᵁ W)) (h : V ≤ (derivationActionGlobal hsq₂ θ₂ ca₂ ≫ v) ⁻¹ᵁ W)
    (g : Γ(Y₁', W)) :
    ((derivationActionGlobal hsq₂ θ₂ ca₂ ≫ v).appLE W V h).hom g =
      (a₂.appLE (v ⁻¹ᵁ W) V hB).hom ((v.app W).hom g) +
        derivationSection hsq₂ θ₂ (v ⁻¹ᵁ W) V (preimage_le_of_comm ca₂ hB) ((v.app W).hom g) := by
  rw [comp_appLE_apply (derivationActionGlobal hsq₂ θ₂ ca₂) v W (v ⁻¹ᵁ W) V le_rfl
      (show V ≤ derivationActionGlobal hsq₂ θ₂ ca₂ ⁻¹ᵁ (v ⁻¹ᵁ W) from hB) h,
    Scheme.Hom.appLE_eq_app, derivationActionGlobal_appLE hsq₂ θ₂ ca₂ (v ⁻¹ᵁ W) V hB]

/-- **Corresponding data act compatibly on every pair of compatible lifts.** If the
perturbations of `θ₁` and `θ₂` correspond under `(w, v)`, then for lifts `a₁` and `a₂` of `a`
with `a₂ ≫ v = w ≫ a₁`,

`(θ₂ ⬝ a₂) ≫ v = w ≫ (θ₁ ⬝ a₁)`. -/
theorem derivationActionGlobal_comp_of_correspond
    {θ₁ : Smooth.pullbackCotangentSheaf (j₁ ≫ q₁) a ⟶ conormalModules i₁}
    {θ₂ : Smooth.pullbackCotangentSheaf (j₂ ≫ q₂) a ⟶ conormalModules i₂}
    (hθ : DerivationSectionsCorrespond hsq₁ hsq₂ hw hv θ₁ θ₂)
    {a₁ : X₁' ⟶ Y₁'} {a₂ : X₂' ⟶ Y₂'} (ca₁ : i₁ ≫ a₁ = a ≫ j₁) (ca₂ : i₂ ≫ a₂ = a ≫ j₂)
    (hcomp : a₂ ≫ v = w ≫ a₁) :
    derivationActionGlobal hsq₂ θ₂ ca₂ ≫ v = w ≫ derivationActionGlobal hsq₁ θ₁ ca₁ := by
  have cR : i₂ ≫ (w ≫ derivationActionGlobal hsq₁ θ₁ ca₁) = a ≫ j₁ := by
    rw [← Category.assoc, hw, comm_derivationActionGlobal]
  have cL : i₂ ≫ (derivationActionGlobal hsq₂ θ₂ ca₂ ≫ v) = a ≫ j₁ := by
    rw [← Category.assoc, comm_derivationActionGlobal, Category.assoc, hv]
  refine (eq_derivationActionGlobal (q := q₁) hsq₂ 0 cR cL fun W V hA g => ?_).trans
    (derivationActionGlobal_zero hsq₂ _ cR)
  rw [derivationSection_zero_hom, add_zero]
  have hA₁ : a₁ ⁻¹ᵁ W ≤ (derivationActionGlobal hsq₁ θ₁ ca₁) ⁻¹ᵁ W := le_rfl
  have hV : V ≤ w ⁻¹ᵁ (a₁ ⁻¹ᵁ W) := hA
  have hB := le_preimage_of_comp_eq hcomp hV
  rw [appLE_derivationActionGlobal_comp hsq₂ θ₂ ca₂ W V hB,
    comp_appLE_apply w _ W (a₁ ⁻¹ᵁ W) V hA₁ hV hA,
    derivationActionGlobal_appLE hsq₁ θ₁ ca₁ W (a₁ ⁻¹ᵁ W) le_rfl g, map_add]
  congr 1
  · exact appLE_comp_eq_of_comp_eq hcomp W (a₁ ⁻¹ᵁ W) V le_rfl hV g
  · have h := hθ W (a₁ ⁻¹ᵁ W) (preimage_le_of_comm ca₁ le_rfl) g
    show _ = (X₂'.presheaf.map (homOfLE hV).op).hom ((w.app (a₁ ⁻¹ᵁ W)).hom _)
    rw [h, map_derivationSection]

/-- **Two data acting compatibly on one pair of compatible lifts correspond.** -/
theorem correspond_of_derivationActionGlobal_comp
    {θ₁ : Smooth.pullbackCotangentSheaf (j₁ ≫ q₁) a ⟶ conormalModules i₁}
    {θ₂ : Smooth.pullbackCotangentSheaf (j₂ ≫ q₂) a ⟶ conormalModules i₂}
    {a₁ : X₁' ⟶ Y₁'} {a₂ : X₂' ⟶ Y₂'} (ca₁ : i₁ ≫ a₁ = a ≫ j₁) (ca₂ : i₂ ≫ a₂ = a ≫ j₂)
    (hcomp : a₂ ≫ v = w ≫ a₁)
    (h : derivationActionGlobal hsq₂ θ₂ ca₂ ≫ v = w ≫ derivationActionGlobal hsq₁ θ₁ ca₁) :
    DerivationSectionsCorrespond hsq₁ hsq₂ hw hv θ₁ θ₂ := by
  intro W V hU g
  have hA₁ : V ≤ a₁ ⁻¹ᵁ W := le_preimage_of_preimage_le hsq₁ ca₁ hU
  have hV : w ⁻¹ᵁ V ≤ w ⁻¹ᵁ (a₁ ⁻¹ᵁ W) := w.preimage_mono hA₁
  have hB := le_preimage_of_comp_eq hcomp hV
  have hR : w ⁻¹ᵁ V ≤ (w ≫ derivationActionGlobal hsq₁ θ₁ ca₁) ⁻¹ᵁ W := hV
  have hL : w ⁻¹ᵁ V ≤ (derivationActionGlobal hsq₂ θ₂ ca₂ ≫ v) ⁻¹ᵁ W := by
    rw [h]; exact hR
  have key := congrArg (fun z : Γ(Y₁', W) ⟶ Γ(X₂', w ⁻¹ᵁ V) => z.hom g)
    (appLE_congr_hom h W (w ⁻¹ᵁ V) hL hR)
  rw [appLE_derivationActionGlobal_comp hsq₂ θ₂ ca₂ W (w ⁻¹ᵁ V) hB,
    comp_appLE_apply w (derivationActionGlobal hsq₁ θ₁ ca₁) W V (w ⁻¹ᵁ V)
      (show V ≤ derivationActionGlobal hsq₁ θ₁ ca₁ ⁻¹ᵁ W from hA₁) le_rfl hR,
    Scheme.Hom.appLE_eq_app,
    derivationActionGlobal_appLE hsq₁ θ₁ ca₁ W V hA₁ g, map_add] at key
  have hbase := appLE_comp_eq_of_comp_eq hcomp W V (w ⁻¹ᵁ V) hA₁ le_rfl g
  rw [Scheme.Hom.appLE_eq_app] at hbase
  rw [hbase] at key
  exact (add_left_cancel key).symm

include hw hv in
/-- **Compatibility at one pair of lifts gives compatibility at every pair.** -/
theorem derivationActionGlobal_comp_of_comp
    {θ₁ : Smooth.pullbackCotangentSheaf (j₁ ≫ q₁) a ⟶ conormalModules i₁}
    {θ₂ : Smooth.pullbackCotangentSheaf (j₂ ≫ q₂) a ⟶ conormalModules i₂}
    {a₁ : X₁' ⟶ Y₁'} {a₂ : X₂' ⟶ Y₂'} (ca₁ : i₁ ≫ a₁ = a ≫ j₁) (ca₂ : i₂ ≫ a₂ = a ≫ j₂)
    (hcomp : a₂ ≫ v = w ≫ a₁)
    (h : derivationActionGlobal hsq₂ θ₂ ca₂ ≫ v = w ≫ derivationActionGlobal hsq₁ θ₁ ca₁)
    {b₁ : X₁' ⟶ Y₁'} {b₂ : X₂' ⟶ Y₂'} (cb₁ : i₁ ≫ b₁ = a ≫ j₁) (cb₂ : i₂ ≫ b₂ = a ≫ j₂)
    (hcomp' : b₂ ≫ v = w ≫ b₁) :
    derivationActionGlobal hsq₂ θ₂ cb₂ ≫ v = w ≫ derivationActionGlobal hsq₁ θ₁ cb₁ :=
  derivationActionGlobal_comp_of_correspond hsq₁ hsq₂ hw hv
    (correspond_of_derivationActionGlobal_comp hsq₁ hsq₂ hw hv ca₁ ca₂ hcomp h) cb₁ cb₂ hcomp'

/-- **The relation is additive.** -/
theorem correspond_add
    {θ₁ η₁ : Smooth.pullbackCotangentSheaf (j₁ ≫ q₁) a ⟶ conormalModules i₁}
    {θ₂ η₂ : Smooth.pullbackCotangentSheaf (j₂ ≫ q₂) a ⟶ conormalModules i₂}
    (hθ : DerivationSectionsCorrespond hsq₁ hsq₂ hw hv θ₁ θ₂)
    (hη : DerivationSectionsCorrespond hsq₁ hsq₂ hw hv η₁ η₂) :
    DerivationSectionsCorrespond hsq₁ hsq₂ hw hv (θ₁ + η₁) (θ₂ + η₂) := by
  intro W V hU g
  rw [derivationSection_add_hom, derivationSection_add_hom, map_add, hθ, hη]

/-- **The zero data correspond.** -/
theorem correspond_zero :
    DerivationSectionsCorrespond (q₁ := q₁) (q₂ := q₂) (a := a) hsq₁ hsq₂ hw hv 0 0 := by
  intro W V hU g
  rw [derivationSection_zero_hom, derivationSection_zero_hom, map_zero]

/-! ### Data related by a map of conormal sheaves -/

omit [IsClosedImmersion i₁] [IsClosedImmersion i₂] in
/-- The two preimages of an open of the first ambient scheme on the common subscheme agree. -/
theorem preimage_preimage_le_of_comp (hw : i₂ ≫ w = i₁) (V : X₁'.Opens) :
    i₂ ⁻¹ᵁ (w ⁻¹ᵁ V) ≤ i₁ ⁻¹ᵁ V := by
  rw [← hw]; exact le_rfl

/-- **A map of conormal sheaves lies over the vertical map `w`.** For first-order thickenings
`i₁ : X ⟶ X₁'` and `i₂ : X ⟶ X₂'` and `w : X₂' ⟶ X₁'` with `i₂ ≫ w = i₁`, the map
`c : 𝒞_{X/X₁'} ⟶ 𝒞_{X/X₂'}` is the one `w` induces when `w^♯` carries the image in `𝒪_{X₁'}` of
every conormal section to the image in `𝒪_{X₂'}` of its image under `c`. Since the conormal
sections of a first-order thickening *are* its defining ideal, such a `c` is unique; for an
arrow of deformations it is the map of [Stacks Project, Tag 01R4]. -/
def IsConormalMapOver (hsq₁ : i₁.ker ^ 2 = ⊥) (hsq₂ : i₂.ker ^ 2 = ⊥) (hw : i₂ ≫ w = i₁)
    (c : conormalModules i₁ ⟶ conormalModules i₂) : Prop :=
  ∀ (V : X₁'.Opens) (s : Γ(conormalModules i₁, i₁ ⁻¹ᵁ V)),
    (w.app V).hom (conormalSection hsq₁ V s) =
      conormalSection hsq₂ (w ⁻¹ᵁ V)
        ((conormalModules i₂).presheaf.map (homOfLE (preimage_preimage_le_of_comp hw V)).op
          ((Scheme.Modules.Hom.app c (i₁ ⁻¹ᵁ V)).hom s))

/-- **Data related by a map of conormal sheaves over `w` correspond.** If `c` lies over `w` and
`c ∘ θ₁` and `θ₂` agree on the pulled-back universal differentials, then the perturbations of
`θ₁` and `θ₂` correspond under `(w, v)`. -/
theorem correspond_of_isConormalMapOver
    {θ₁ : Smooth.pullbackCotangentSheaf (j₁ ≫ q₁) a ⟶ conormalModules i₁}
    {θ₂ : Smooth.pullbackCotangentSheaf (j₂ ≫ q₂) a ⟶ conormalModules i₂}
    {c : conormalModules i₁ ⟶ conormalModules i₂} (hc : IsConormalMapOver hsq₁ hsq₂ hw c)
    (hpd : ∀ (A : Y.Opens) (U : X.Opens) (h : U ≤ a ⁻¹ᵁ A) (y : Γ(Y, A)),
      (Scheme.Modules.Hom.app c U).hom
          ((Scheme.Modules.Hom.app θ₁ U).hom (Smooth.pullbackD (j₁ ≫ q₁) a A h y)) =
        (Scheme.Modules.Hom.app θ₂ U).hom (Smooth.pullbackD (j₂ ≫ q₂) a A h y)) :
    DerivationSectionsCorrespond hsq₁ hsq₂ hw hv θ₁ θ₂ := by
  subst hw hv
  intro W V hU g
  rw [derivationSection, hc, hpd]
  rw [derivationSection]
  congr 1
  have hθ := (Scheme.Modules.Hom.mapPresheaf θ₂).naturality
    (homOfLE (preimage_preimage_le_of_comp (rfl : i₂ ≫ w = i₂ ≫ w) V)).op
  have hθ' := congrArg (fun z : Γ(Smooth.pullbackCotangentSheaf (j₂ ≫ q₂) a, (i₂ ≫ w) ⁻¹ᵁ V) ⟶
      Γ(conormalModules i₂, i₂ ⁻¹ᵁ (w ⁻¹ᵁ V)) => z.hom
    (Smooth.pullbackD (j₂ ≫ q₂) a ((j₂ ≫ v) ⁻¹ᵁ W) hU (((j₂ ≫ v).app W).hom g))) hθ
  refine hθ'.symm.trans ?_
  exact congrArg (Scheme.Modules.Hom.app θ₂ _).hom
    (Smooth.map_pullbackD (j₂ ≫ q₂) a _ hU _ _ _)

end BaseNaturality

/-! ### A modified self-map acts trivially on the conormal sheaf -/

section SelfMap

variable {S X X' : Scheme.{u}} {i : X ⟶ X'} [IsClosedImmersion i]

/-- **A modified self-map `u ⬝ 𝟙` induces the identity on the conormal sheaf.** Its comorphism
is `g ↦ g + D_u g`, and `D_u` kills the defining ideal of `i`
(`Stacks.Thickenings.derivationSection_eq_zero_of_mem_ker`), which is where the conormal sections
live. -/
theorem isConormalMapOver_derivationActionGlobal_self (hsq : i.ker ^ 2 = ⊥) {q : X' ⟶ S}
    (u : Smooth.pullbackCotangentSheaf (i ≫ q) (𝟙 X) ⟶ conormalModules i)
    (comm : i ≫ (𝟙 X' : X' ⟶ X') = (𝟙 X : X ⟶ X) ≫ i)
    (hw : i ≫ derivationActionGlobal hsq u comm = i) :
    IsConormalMapOver hsq hsq hw (𝟙 (conormalModules i)) := by
  intro V s
  rw [derivationActionGlobal_app, derivationSection_eq_zero_of_mem_ker _ _ _
    (RingHom.mem_ker.mp (conormalSection_mem_ker hsq V s)), add_zero]
  show conormalSection hsq V s = conormalSection hsq V
    ((conormalModules i).presheaf.map (𝟙 (Opposite.op (i ⁻¹ᵁ V))) s)
  rw [CategoryTheory.Functor.map_id]
  rfl

end SelfMap

end Stacks.Thickenings

end
