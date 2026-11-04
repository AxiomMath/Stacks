module

public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictSquareMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FirstOrderThickeningRestrict
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationMaps

/-!
# The presheaf of constrained lifts of a morphism along a first order thickening

Let `S` be a scheme, let `i : X ⟶ X'` and `j : Y ⟶ Y'` be immersions, let `a : X ⟶ Y` be a
morphism and let `A : a^* 𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` be a map of `𝒪_X`-modules. For an open `V` of `X'`,
`Stacks.Thickenings.compatibleLifts` is the set of morphisms `b : V ⟶ Y'` over `S` restricting to
`a` on `i⁻¹V` and inducing the restriction of `A` there; this is the set of
[Stacks Project, Tag 04FI], and [Stacks Project, Tag 04FH] asserts that `V ↦ {b}` is a sheaf of
sets on `X'`.

This file builds the **presheaf**: it proves that the third condition of the tag, the one about
conormal sheaves, is stable under shrinking `V`, and assembles the three conditions into
restriction maps.

## Main results

* `Stacks.Thickenings.restrictConormalSheafMap_eq` rewrites the restriction of `A` through the
  canonical map of [Stacks Project, Tag 01R4] attached to the restriction square of `i`.
* `Stacks.Thickenings.restrictConormalSheafMap_homOfLE` is the restriction law for that map: it is
  the pullback of the restriction over the larger open, composed with the canonical map of the
  restriction square between the two.
* `Stacks.Thickenings.IsCompatibleLift.restrict_trd` and
  `Stacks.Thickenings.IsCompatibleLift.restrict`: the third condition, and so all three, restrict.
* `Stacks.Thickenings.compatibleLiftsRestrict` and
  `Stacks.Thickenings.compatibleLiftsPresheaf`: the restriction maps and the presheaf they define.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 04FH](https://stacks.math.columbia.edu/tag/04FH)
* [Stacks Project, Tag 04FI](https://stacks.math.columbia.edu/tag/04FI)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.Immersion Stacks.ClosedImmersion

universe u

namespace Stacks.Thickenings

private theorem restrict_shuffle {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ C₀ D₀ E₀ F₀ : C}
    {c1' : A₀ ⟶ A₁} {c2' : A₁ ⟶ A₂} {m' : A₂ ⟶ A₃}
    {x : A₂ ⟶ B₀} {m2 : B₀ ⟶ A₃} {qq : B₀ ⟶ B₁} {mm : B₁ ⟶ B₂} {nn : B₂ ⟶ A₃}
    {y : A₁ ⟶ C₀} {aa : C₀ ⟶ B₀} {qq' : C₀ ⟶ D₀} {cc : D₀ ⟶ B₁}
    {e : A₀ ⟶ E₀} {g : E₀ ⟶ C₀} {pb : E₀ ⟶ F₀} {f1 : F₀ ⟶ D₀} {w : F₀ ⟶ B₂}
    (H1a : m' = x ≫ m2) (H1b : m2 = qq ≫ mm ≫ nn)
    (H2 : c2' ≫ x = y ≫ aa) (H3 : aa ≫ qq = qq' ≫ cc)
    (H4 : c1' ≫ y = e ≫ g) (H5 : pb ≫ f1 = g ≫ qq') (H6 : w = f1 ≫ cc ≫ mm) :
    c1' ≫ c2' ≫ m' = e ≫ pb ≫ w ≫ nn := by
  subst H1b H1a H6
  simp only [Category.assoc]
  rw [reassoc_of% H2, reassoc_of% H4, reassoc_of% H3, ← reassoc_of% H5]

private theorem modulePullback_map_congr' {Z W : Scheme.{u}} {f f' : Z ⟶ W} (hf : f = f')
    {M N : SheafOfModules.{u} (structureSheafRing W.toLocallyRingedSpace.toRingedSpace)}
    (φ : M ⟶ N) :
    (modulePullback f'.toLRSHom.toShHom).map φ ≫
        eqToHom (congrArg
          (fun p : Z ⟶ W => (modulePullback p.toLRSHom.toShHom).obj N) hf.symm) =
      eqToHom (congrArg
          (fun p : Z ⟶ W => (modulePullback p.toLRSHom.toShHom).obj M) hf.symm) ≫
        (modulePullback f.toLRSHom.toShHom).map φ := by
  subst hf
  exact (Category.comp_id _).trans (Category.id_comp _).symm

private theorem modulePullbackComp_congr_left' {Z W V : Scheme.{u}} {f f' : Z ⟶ W} (hf : f = f')
    (g : W ⟶ V) (M : SheafOfModules.{u} (structureSheafRing V.toLocallyRingedSpace.toRingedSpace)) :
    (modulePullbackComp f'.toLRSHom.toShHom g.toLRSHom.toShHom).hom.app M ≫
        eqToHom (congrArg (fun p : Z ⟶ W => (modulePullback p.toLRSHom.toShHom).obj
          ((modulePullback g.toLRSHom.toShHom).obj M)) hf.symm) =
      eqToHom (congrArg
          (fun p : Z ⟶ W => (modulePullback (p ≫ g).toLRSHom.toShHom).obj M) hf.symm) ≫
        (modulePullbackComp f.toLRSHom.toShHom g.toLRSHom.toShHom).hom.app M := by
  subst hf
  exact (Category.comp_id _).trans (Category.id_comp _).symm

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'}

variable [IsImmersion i] [IsImmersion j]

/-- **`Stacks.Thickenings.restrictConormalSheafMap` through the canonical map of the restriction
square.** The restriction of `A : a^* 𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` to the open `i⁻¹V` of `X` is the
pseudofunctoriality comparison, followed by the pullback of `A` along `ι_{i⁻¹V}`, followed by the
map of conormal sheaves of [Stacks Project, Tag 01R4] attached to the restriction square of `i`
over `V`. -/
theorem restrictConormalSheafMap_eq (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) (V : X'.Opens) :
    restrictConormalSheafMap a A V =
      (modulePullbackComp (i ⁻¹ᵁ V).ι.toLRSHom.toShHom a.toLRSHom.toShHom).hom.app
          (immersionConormalSheaf j) ≫
        (modulePullback (i ⁻¹ᵁ V).ι.toLRSHom.toShHom).map A ≫
        immersionConormalSheafMap (i ∣_ V) i (i ⁻¹ᵁ V).ι V.ι
          (toShHom_square (morphismRestrict_ι i V)) :=
  whisker_eq _ (whisker_eq _
    (modulePullbackRestrictIso_comp_conormalSheafSelfRestrictIso i V))

/-- `Stacks.Immersion.immersionConormalSheafMap_congr` at the two edges `ρ ≫ ι_{i⁻¹V} = ι_{i⁻¹V'}`
and `ρ_{X'} ≫ ι_V = ι_{V'}` of a restriction tower. -/
private theorem restrictSquareMap_congr {V V' : X'.Opens} (hV : V' ≤ V) :
    immersionConormalSheafMap (i ∣_ V') i (i ⁻¹ᵁ V').ι V'.ι
        (toShHom_square (morphismRestrict_ι i V')) =
      eqToHom (congrArg (fun p : (i ⁻¹ᵁ V').toScheme ⟶ X =>
          (modulePullback p.toLRSHom.toShHom).obj (immersionConormalSheaf i))
        (Scheme.homOfLE_ι X (i.preimage_mono hV)).symm) ≫
        immersionConormalSheafMap (i ∣_ V') i ((X.homOfLE (i.preimage_mono hV)) ≫ (i ⁻¹ᵁ V).ι)
          (X'.homOfLE hV ≫ V.ι)
          (toShHom_square (square_comp (morphismRestrict_homOfLE i V' V hV)
            (morphismRestrict_ι i V))) :=
  immersionConormalSheafMap_congr (i ∣_ V') i
    (Scheme.homOfLE_ι X (i.preimage_mono hV)) (Scheme.homOfLE_ι X' hV)
    (toShHom_square (square_comp (morphismRestrict_homOfLE i V' V hV)
      (morphismRestrict_ι i V)))
    (toShHom_square (morphismRestrict_ι i V'))

omit [IsImmersion i] in
/-- The associativity coherence of the pullback composition isomorphism at the triple
`ρ`, `ι_{i⁻¹V}`, `a`. -/
private theorem modulePullbackComp_assoc_restrict (a : X ⟶ Y) {V V' : X'.Opens} (hV : V' ≤ V) :
    (modulePullbackComp (X.homOfLE (i.preimage_mono hV)).toLRSHom.toShHom
          ((i ⁻¹ᵁ V).ι ≫ a).toLRSHom.toShHom).hom.app (immersionConormalSheaf j) ≫
        (modulePullback (X.homOfLE (i.preimage_mono hV)).toLRSHom.toShHom).map
          ((modulePullbackComp (i ⁻¹ᵁ V).ι.toLRSHom.toShHom a.toLRSHom.toShHom).hom.app
          (immersionConormalSheaf j)) =
      (modulePullbackComp ((X.homOfLE (i.preimage_mono hV)) ≫ (i ⁻¹ᵁ V).ι).toLRSHom.toShHom
            a.toLRSHom.toShHom).hom.app (immersionConormalSheaf j) ≫
        (modulePullbackComp (X.homOfLE (i.preimage_mono hV)).toLRSHom.toShHom
            (i ⁻¹ᵁ V).ι.toLRSHom.toShHom).hom.app
          ((modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j)) :=
  modulePullbackComp_assoc (X.homOfLE (i.preimage_mono hV)).toLRSHom.toShHom
    (i ⁻¹ᵁ V).ι.toLRSHom.toShHom a.toLRSHom.toShHom (immersionConormalSheaf j)

/-- The pullback along `ρ` of `Stacks.Thickenings.restrictConormalSheafMap`, split into its three
factors. -/
private theorem modulePullback_map_restrictConormalSheafMap (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) {V V' : X'.Opens} (hV : V' ≤ V) :
    (modulePullback (X.homOfLE (i.preimage_mono hV)).toLRSHom.toShHom).map
        (restrictConormalSheafMap a A V) =
      (modulePullback (X.homOfLE (i.preimage_mono hV)).toLRSHom.toShHom).map
          ((modulePullbackComp (i ⁻¹ᵁ V).ι.toLRSHom.toShHom a.toLRSHom.toShHom).hom.app
          (immersionConormalSheaf j)) ≫
        (modulePullback (X.homOfLE (i.preimage_mono hV)).toLRSHom.toShHom).map
            ((modulePullback (i ⁻¹ᵁ V).ι.toLRSHom.toShHom).map A) ≫
          (modulePullback (X.homOfLE (i.preimage_mono hV)).toLRSHom.toShHom).map
            (immersionConormalSheafMap (i ∣_ V) i (i ⁻¹ᵁ V).ι V.ι
            (toShHom_square (morphismRestrict_ι i V))) :=
  (congrArg (modulePullback (X.homOfLE (i.preimage_mono hV)).toLRSHom.toShHom).map
      (restrictConormalSheafMap_eq a A V)).trans
    (((modulePullback (X.homOfLE (i.preimage_mono hV)).toLRSHom.toShHom).map_comp _ _).trans
      (whisker_eq _
        ((modulePullback (X.homOfLE (i.preimage_mono hV)).toLRSHom.toShHom).map_comp _ _)))

/-- **The third condition of [Stacks Project, Tag 04FI] restricts to a smaller open.** The
restriction of `A` to `i⁻¹V'`, as a map `(ι_{i⁻¹V'} ≫ a)^* 𝒞_{Y/Y'} ⟶ 𝒞_{i ∣_ V'}`, is the
restriction of `A` to `i⁻¹V` pulled back along `ρ : i⁻¹V' ⟶ i⁻¹V`, composed with the map of
conormal sheaves of the square `(i ∣_ V') ≫ ρ_{X'} = ρ ≫ (i ∣_ V)`. The `CategoryTheory.eqToHom`
in front transports along `ρ ≫ ι_{i⁻¹V} = ι_{i⁻¹V'}`. -/
theorem restrictConormalSheafMap_homOfLE (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) {V V' : X'.Opens} (hV : V' ≤ V) :
    restrictConormalSheafMap a A V' =
      eqToHom (congrArg (fun p : (i ⁻¹ᵁ V').toScheme ⟶ X =>
            (modulePullback (p ≫ a).toLRSHom.toShHom).obj (immersionConormalSheaf j))
          (Scheme.homOfLE_ι X (i.preimage_mono hV)).symm) ≫
        (modulePullbackComp (X.homOfLE (i.preimage_mono hV)).toLRSHom.toShHom
            ((i ⁻¹ᵁ V).ι ≫ a).toLRSHom.toShHom).hom.app (immersionConormalSheaf j) ≫
          (modulePullback (X.homOfLE (i.preimage_mono hV)).toLRSHom.toShHom).map
              (restrictConormalSheafMap a A V) ≫
            immersionConormalSheafMap (i ∣_ V') (i ∣_ V)
              (X.homOfLE (i.preimage_mono hV)) (X'.homOfLE hV)
              (toShHom_square (morphismRestrict_homOfLE i V' V hV)) := by
  rw [restrictConormalSheafMap_eq a A V']
  exact restrict_shuffle
    (restrictSquareMap_congr hV)
    (immersionConormalSheafMap_morphismRestrict i hV (i ⁻¹ᵁ V).ι V.ι
      (morphismRestrict_ι i V))
    (modulePullback_map_congr' (Scheme.homOfLE_ι X (i.preimage_mono hV)) A)
    ((modulePullbackComp _ _).hom.naturality A)
    (modulePullbackComp_congr_left' (Scheme.homOfLE_ι X (i.preimage_mono hV)) a
        (immersionConormalSheaf j))
    (modulePullbackComp_assoc_restrict a hV)
    (modulePullback_map_restrictConormalSheafMap a A hV)

omit [IsImmersion i] [IsImmersion j] in
/-- The inclusion of `i⁻¹V'` into `X` followed by `a` factors through the inclusion of `i⁻¹V`. -/
theorem homOfLE_comp_ι_comp (a : X ⟶ Y) {V V' : X'.Opens} (hV : V' ≤ V) :
    X.homOfLE (i.preimage_mono hV) ≫ (i ⁻¹ᵁ V).ι ≫ a = (i ⁻¹ᵁ V').ι ≫ a := by
  rw [← Category.assoc, Scheme.homOfLE_ι]

variable {pX' : X' ⟶ S} {pY' : Y' ⟶ S} {a : X ⟶ Y}
  {A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
    immersionConormalSheaf i} {V : X'.Opens} {b : V.toScheme ⟶ Y'}

/-- **Condition (3) of [Stacks Project, Tag 04FI] is stable under restriction.** If the map of
conormal sheaves induced by a lift `b` over `V` is the restriction of `A`, then the same holds for
the restriction of `b` to a smaller open `V'` of `X'`. -/
theorem IsCompatibleLift.restrict_trd (hb : IsCompatibleLift pX' pY' a A V b)
    {V' : X'.Opens} (hV : V' ≤ V) :
    immersionConormalSheafMap (i ∣_ V') j ((i ⁻¹ᵁ V').ι ≫ a) (X'.homOfLE hV ≫ b)
        (toShHom_square (hb.restrict_snd hV)) =
      restrictConormalSheafMap a A V' := by
  obtain ⟨h, h3⟩ := hb.2
  refine (immersionConormalSheafMap_congr (i ∣_ V') j (homOfLE_comp_ι_comp a hV) rfl
      (toShHom_square (square_comp (morphismRestrict_homOfLE i V' V hV) h))
      (toShHom_square (hb.restrict_snd hV))).trans ?_
  exact Eq.trans (whisker_eq _
    ((immersionConormalSheafMap_comp (i ∣_ V') (i ∣_ V) j
        (X.homOfLE (i.preimage_mono hV)) (X'.homOfLE hV)
        (morphismRestrict_homOfLE i V' V hV) ((i ⁻¹ᵁ V).ι ≫ a) b h).trans
      (whisker_eq _
        (eq_whisker
          (congrArg (modulePullback (X.homOfLE (i.preimage_mono hV)).toLRSHom.toShHom).map h3)
          _)))) (restrictConormalSheafMap_homOfLE a A hV).symm

/-- **The three conditions of [Stacks Project, Tag 04FI] are stable under restriction.** A lift of
`a` over an open `V` of `X'` compatible with `A` restricts to a compatible lift over any smaller
open `V'`. -/
@[stacks 04FH "the restriction maps"]
theorem IsCompatibleLift.restrict (hb : IsCompatibleLift pX' pY' a A V b)
    {V' : X'.Opens} (hV : V' ≤ V) :
    IsCompatibleLift pX' pY' a A V' (X'.homOfLE hV ≫ b) :=
  ⟨hb.restrict_fst hV, hb.restrict_snd hV, hb.restrict_trd hV⟩

/-- **The restriction map of [Stacks Project, Tag 04FH].** A compatible lift of `a` over an open
`V` of `X'` restricts to a compatible lift over a smaller open `V'`, by composing with the
inclusion `V' ⟶ V`. -/
def compatibleLiftsRestrict (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) {V V' : X'.Opens} (hV : V' ≤ V) :
    compatibleLifts pX' pY' a A V ⟶ compatibleLifts pX' pY' a A V' :=
  TypeCat.ofHom fun c ↦ ⟨X'.homOfLE hV ≫ c.1, c.2.restrict hV⟩

/-- The underlying morphism of a restricted compatible lift is the composite of the inclusion
`V' ⟶ V` with the lift. -/
theorem compatibleLiftsRestrict_coe (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) {V V' : X'.Opens} (hV : V' ≤ V)
    (c : compatibleLifts pX' pY' a A V) :
    (compatibleLiftsRestrict pX' pY' a A hV c).1 = X'.homOfLE hV ≫ c.1 := rfl

/-- **The presheaf of compatible lifts.** The rule assigning to an open `V` of `X'` the set of
morphisms `V ⟶ Y'` over `S` restricting to `a` on `i⁻¹V` and inducing the restriction of `A`
there, with the restriction maps of `Stacks.Thickenings.compatibleLiftsRestrict`. -/
@[stacks 04FH "the restriction maps"]
def compatibleLiftsPresheaf (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) :
    TopCat.Presheaf (Type u) X'.carrier where
  obj V := compatibleLifts pX' pY' a A V.unop
  map f := compatibleLiftsRestrict pX' pY' a A f.unop.le
  map_id V := by
    ext c
    exact Subtype.ext
      ((congrArg (fun z ↦ z ≫ c.1) (Scheme.homOfLE_rfl X' V.unop)).trans (Category.id_comp c.1))
  map_comp f g := by
    ext c
    exact Subtype.ext
      ((congrArg (fun z ↦ z ≫ c.1)
        (Scheme.homOfLE_homOfLE X' g.unop.le f.unop.le).symm).trans (Category.assoc _ _ _))

end Stacks.Thickenings

end
