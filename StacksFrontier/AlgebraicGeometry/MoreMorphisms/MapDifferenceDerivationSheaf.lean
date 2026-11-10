module

public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeMiddleExact
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationSheafAction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDifferenceDiagonalSheaf

/-!
# Infinitesimal deformations of maps: the difference of two lifts is a derivation, at sheaf level

Let `S` be a scheme, let `i : X ⟶ X'` be a first-order thickening, let `j : Y ⟶ Y'` be an
immersion with structure morphism `q : Y' ⟶ S`, and let `(a, a')` and `(a, b')` be two morphisms
of thickenings `(X ⊂ X') ⟶ (Y ⊂ Y')` over `S`. Suppose that the two reductions agree — this is
hypothesis (1) of the source, imposed by writing both squares over one and the same `a` — and
that the two induced maps `a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 01R4] agree, which is
hypothesis (2). Then `(a')^♯ - (b')^♯` factors as
```
𝒪_{Y'} ⟶ 𝒪_Y --D--> a_*𝒞_{X/X'} ⟶ a_*𝒪_{X'}
```
with `D` an `𝒪_S`-derivation. **This file proves that for arbitrary `X'`, `Y'` and `S`** — no
scheme is assumed affine anywhere — which is the unrestricted form of
[Stacks Project, Tag 04FG]. The affine case over global sections is
`Stacks.Thickenings.mapDifferenceDerivation` in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/MapDifferenceDerivation.lean`; nothing here is
deduced from it.

## Main definitions

* `Stacks.Thickenings.differenceDerivationMap`: the map `j^*Ω_{Y'/S} ⟶ a_*𝒞_{X/X'}` of
  [Stacks Project, Tag 01R4] for the diagonal square of the pair `(a', b')`, transposed to `Y`.
* `Stacks.Thickenings.differenceDerivationHom`: its descent `Ω_{Y/S} ⟶ a_*𝒞_{X/X'}` along the
  conormal sequence of `j`.
* `Stacks.Thickenings.differenceDerivation`: the `𝒪_S`-derivation `D` of
  [Stacks Project, Tag 04FG].
* `Stacks.Thickenings.differenceDerivationTheta`: the datum `θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}` that
  corresponds to `D` under the universal property of `Ω_{Y/S}`.

## Main results

* `Stacks.Thickenings.firstOrderImmersionConormalSheafι_differenceDerivation_d`:
  **[Stacks Project, Tag 04FG]** — the factorization, read through the inclusion
  `𝒞_{X/X'} ⟶ 𝒪_{X'}` of the conormal sheaf of a first-order thickening.
* `Stacks.Thickenings.liftDiffSection_eq_zero_of_conormalSheafMap_eq`: hypothesis (2) makes the
  two comorphisms agree on the defining ideal of `Y ⊂ Y'`. This is where that hypothesis is
  used.
* `Stacks.Thickenings.conormalDifferential_comp_differenceDerivationMap`: the difference map
  kills the first arrow of the conormal sequence of `j`, which is what makes the descent
  possible.
* `Stacks.Thickenings.isDerivationAction_differenceDerivationTheta` and
  `Stacks.Thickenings.exists_isDerivationAction`: the factorization rewritten in the comorphism
  form `Stacks.Thickenings.IsDerivationAction`, that is, `b'` is `θ ⬝ a'` in the sense of
  [Stacks Project, Tag 0CK1] for a `θ` that is produced. This is the converse direction of the
  simple-transitivity half of [Stacks Project, Tag 04FJ].
* `Stacks.Thickenings.homEquiv_coborderPullbackDifferentialsIso_inv_apply` and
  `Stacks.Thickenings.map_conormalDerivation_d_app`: the comparison
  `Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso` of differentials over the
  coborder neighbourhood, read on a universal differential. These are what move the conormal
  sequence of `j`, which is built over that neighbourhood, back onto `Y'`.

## Route

**The difference is not descended by hand; it is descended along the conormal sequence.** The
file never identifies sheaves on `X'` with sheaves on `X`, never inverts the underlying
homeomorphism of a thickening, and glues nothing.

1. The pair `(a', b')` consists of two morphisms `X' ⟶ Y'` agreeing on `X`, so the *unthickened*
   case of the source — [Stacks Project, Tag 04FL], proved for arbitrary schemes in
   `StacksFrontier/AlgebraicGeometry/MoreMorphisms/MapDifferenceDiagonalSheaf.lean` — already
   produces a map `θ' : (a ≫ j)^*Ω_{Y'/S} ⟶ 𝒞_{X/X'}` whose associated derivation sends a local
   section `s` of `𝒪_{Y'}` to the conormal class of `(a')^♯ s - (b')^♯ s`. Transposed, that is
   `Stacks.Thickenings.differenceDerivationMap : j^*Ω_{Y'/S} ⟶ a_*𝒞_{X/X'}`.
2. `Ω_{Y/S}` is the cokernel of the first arrow `𝒞_{Y/Y'} ⟶ j^*Ω_{Y'/S}` of the conormal
   sequence of [Stacks Project, Tag 01UZ]
   (`Stacks.ConormalSequenceRight.conormalShortComplex_exact`). So the difference map descends
   to `Ω_{Y/S}` as soon as it kills that arrow, and the whole content of hypothesis (2) is that
   it does.
3. That vanishing is checked on the sections of the defining ideal sheaf of `j`, which determine
   a morphism out of the conormal sheaf
   (`Stacks.AlgebraicGeometry.RegularIdealSheaf.existsUnique_hom_conormalComparison`). On such a
   section the first arrow is `1 ⊗ d`, so what has to vanish is the difference derivation of
   step 1 on a section killed by `j^♯` — and that is hypothesis (2), read off the conormal
   classes of [Stacks Project, Tag 01R4] by
   `Stacks.Conormal.conormalClass_immersionConormalSheafMap` and
   `Stacks.Conormal.firstOrderImmersionConormalSheafι_conormalClass_of_eq`.
4. Composing the descent with the universal relative derivation of `Y` over `S` makes `D` an
   `𝒪_S`-derivation by construction, so no Leibniz rule and no vanishing on the base is verified
   below.

## Implementation notes

The conormal sequence is built over the coborder neighbourhood `W = j.coborderRange` of the image
of `j`, so its first arrow is pinned by a formula involving `d_{W/S}` and the comparison
`Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso`. Step 3 needs that formula on
`Y'` instead, and the bridge is
`Stacks.Thickenings.map_conormalDerivation_d_app`: the value of the defining derivation on
`ι^♯ s` restricts to the unit image of `d_{Y'/S} s`. Every open of `W` is `ι⁻¹V` for `V = ι(W)`,
and `AlgebraicGeometry.Scheme.Opens.ι_appIso` makes the sections of `𝒪_{Y'}` over `V` the
sections of `𝒪_W`, so no choice is involved.

`AlgebraicGeometry.Scheme.Modules` is a structure copy of `SheafOfModules`, and the two hom types
are compared only after unfolding it. The conormal sheaf and the map of
[Stacks Project, Tag 01R4] are built in the unwrapped category while the pullback comparison
isomorphisms and the conormal sequence live in the wrapped one, so the two are bridged once, in
`Stacks.Thickenings.diagonalConormalSheafMapModules`, and never again.

## Generality

The hypotheses are weaker than the source's. `j` need only be an immersion, not a first-order
thickening: the conormal sequence of [Stacks Project, Tag 01UZ] is right exact for any immersion,
and nothing else about `j` is used. And instead of asking that both lifts be morphisms over `S`
for a common structure morphism `X' ⟶ S`, only `b' ≫ q = a' ≫ q` is assumed, which is what the
diagonal square needs. For `i` the full first-order thickening hypothesis is used, through the
inclusion `Stacks.Thickenings.firstOrderImmersionConormalSheafι` of its conormal sheaf into
`𝒪_{X'}`.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 04FL](https://stacks.math.columbia.edu/tag/04FL)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Thickenings

/-! ### Transposing along the comparison isomorphisms of iterated pullbacks -/

/-- The inverse of the comparison of pullbacks along equal morphisms is the comparison for the
symmetric equality. -/
theorem pullbackCongr_inv {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (Scheme.Modules.pullbackCongr h).inv = (Scheme.Modules.pullbackCongr h.symm).hom := by
  subst h
  rfl

/-- **Transposing along equal morphisms agrees**, up to the restriction map induced by the
resulting equality of preimages. -/
theorem homEquiv_pullbackCongr_apply {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    (hff : f = f') (M : Y.Modules) (N : X.Modules)
    (k : (Scheme.Modules.pullback f').obj M ⟶ N)
    (V : Y.Opens) (hle : f ⁻¹ᵁ V ≤ f' ⁻¹ᵁ V) (z : M.val.obj (op V)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M N
        ((Scheme.Modules.pullbackCongr hff).hom.app M ≫ k)).val.app (op V)).hom z =
      (N.val.map (homOfLE hle).op).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction f').homEquiv M N k).val.app
          (op V)).hom z) := by
  subst hff
  have h1 : (Scheme.Modules.pullbackCongr (rfl : f = f)).hom.app M = 𝟙 _ := rfl
  have h2 : (homOfLE hle : f ⁻¹ᵁ V ⟶ f ⁻¹ᵁ V) = 𝟙 _ := Subsingleton.elim _ _
  rw [h1, Category.id_comp, h2, op_id, N.val.map_id]
  rfl

/-- **Transposing `α.app A ≫ k` along one adjunction is transposing `k` along the other**,
followed by the conjugate (mate) of `α`. -/
theorem homEquiv_conjugate {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) (A : C) (B : D) (k : L₁.obj A ⟶ B) :
    adj₂.homEquiv A B (α.app A ≫ k) =
      adj₁.homEquiv A B k ≫ (conjugateEquiv adj₁ adj₂ α).app B := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, ← unit_conjugateEquiv adj₁ adj₂ α A, Category.assoc,
    ← (conjugateEquiv adj₁ adj₂ α).naturality k, ← Category.assoc]

/-- **Transposition along a composition**, expressed by transposing twice through the comparison
isomorphism for iterated pullbacks of sheaves of modules. -/
theorem homEquiv_pullbackComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (N : X.Modules)
    (k : (Scheme.Modules.pullback (f ≫ g)).obj M ⟶ N) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv M N k =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
          ((Scheme.Modules.pullbackComp f g).hom.app M ≫ k))) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app N := by
  have h := homEquiv_conjugate
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M N
    ((Scheme.Modules.pullbackComp f g).hom.app M ≫ k)
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_homEquiv] at h
  simpa only [Iso.inv_hom_id_app_assoc, Equiv.trans_apply] using h

/-- **Section-level form of `Stacks.Thickenings.homEquiv_pullbackComp`**: the comparison morphism
of pushforwards is the identity on sections. -/
theorem homEquiv_pullbackComp_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (N : X.Modules)
    (k : (Scheme.Modules.pullback (f ≫ g)).obj M ⟶ N)
    (V : Z.Opens) (z : M.val.obj (op V)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv M N k).val.app
        (op V)).hom z =
      ((((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
          ((Scheme.Modules.pullbackComp f g).hom.app M ≫ k))).val.app (op V)).hom z) := by
  rw [homEquiv_pullbackComp]
  rfl

/-- Restricting a section of a sheaf of modules to the open it is already given on does
nothing. -/
theorem module_map_self {Z : Scheme.{u}}
    {M : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)}
    {U : Z.Opens} (h : U ≤ U) (m : M.val.obj (op U)) : M.val.map (homOfLE h).op m = m := by
  rw [PresheafOfModules.congr_map_apply M.val
    (Subsingleton.elim (homOfLE h).op (𝟙 (op U))) m]
  simp
  rfl

/-- Restriction along an equality of opens is injective on sections of the structure sheaf. -/
theorem presheaf_map_injective {Z : Scheme.{u}} {A B : (Z.Opens)ᵒᵖ} (u : A ⟶ B) (v : B ⟶ A)
    {m n : Z.presheaf.obj A}
    (h : (Z.presheaf.map u).hom m = (Z.presheaf.map u).hom n) : m = n := by
  have key : ∀ t : Z.presheaf.obj A, (Z.presheaf.map v).hom ((Z.presheaf.map u).hom t) = t :=
    fun t ↦ (presheaf_map_map u v (𝟙 A) t).trans (presheaf_map_self (𝟙 A) t)
  rw [← key m, ← key n, h]

/-- Restriction along an equality of opens is injective on sections of a sheaf of modules. -/
theorem module_map_injective_of_le {Z : Scheme.{u}}
    {M : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)}
    {U W : Z.Opens} (h : W ≤ U) (h' : U ≤ W) {m n : M.val.obj (op U)}
    (hmn : M.val.map (homOfLE h).op m = M.val.map (homOfLE h).op n) : m = n := by
  have key : ∀ t : M.val.obj (op U),
      M.val.map (homOfLE h').op (M.val.map (homOfLE h).op t) = t := fun t ↦
    (module_map_map (homOfLE h).op (homOfLE h').op (homOfLE (le_refl U)).op t).trans
      (module_map_self (le_refl U) t)
  rw [← key m, ← key n, hmn]

/-- The inverse of an isomorphism of sheaves of modules, followed by the isomorphism, is the
identity on sections. -/
theorem iso_inv_hom_app_apply {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N) (U : Z.Opens)
    (n : N.val.obj (op U)) : e.hom.val.app (op U) (e.inv.val.app (op U) n) = n := by
  have h : e.inv.val.app (op U) ≫ e.hom.val.app (op U) = 𝟙 _ :=
    congrArg (fun φ : N ⟶ N ↦ φ.val.app (op U)) e.inv_hom_id
  exact ConcreteCategory.congr_hom h n

/-- **Naturality of a morphism of sheaves of modules on a scheme, read on sections.** -/
theorem modules_naturality_apply {Z : Scheme.{u}} {M N : Z.Modules} (φ : M ⟶ N)
    {U W : Z.Opens} (h : W ≤ U) (m : M.val.obj (op U)) :
    φ.val.app (op W) (M.val.map (homOfLE h).op m) =
      N.val.map (homOfLE h).op (φ.val.app (op U) m) :=
  PresheafOfModules.naturality_apply φ.val (homOfLE h).op m

/-! ### The coborder comparison of differentials, read on sections -/

section Coborder

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S)

/-- `Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso` inverted, written out as the
composite of the two comparison isomorphisms of pullbacks and the canonical map of the open
immersion of the coborder neighbourhood. -/
theorem coborderPullbackDifferentialsIso_inv_eq :
    (Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso i p).inv =
      (Scheme.Modules.pullbackCongr i.liftCoborder_ι.symm).hom.app
          (Scheme.Hom.relativeDifferentials p) ≫
        ((Scheme.Modules.pullbackComp i.liftCoborder i.coborderRange.ι).inv.app
            (Scheme.Hom.relativeDifferentials p) ≫
          (Scheme.Modules.pullback i.liftCoborder).map
            (Scheme.Hom.relativeDifferentialsMap i.coborderRange.ι p
              (i.coborderRange.ι ≫ p) (𝟙 S) (by simp))) := by
  rw [← pullbackCongr_inv]
  rfl

/-- **The coborder comparison of differentials, inverted and read on a universal differential.**
The transpose of `(Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso i p).inv` sends
`d_{X/S} s` to `1 ⊗ d_{W/S} (ι^♯ s)`, where `W = i.coborderRange` and `ι` is its inclusion. -/
theorem homEquiv_coborderPullbackDifferentialsIso_inv_apply (V : X.Opens)
    (hle : i ⁻¹ᵁ V ≤ i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ V)) (s : Γ(X, V)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _
          (Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso i p).inv).val.app
        (op V)).hom ((Scheme.Hom.universalRelativeDerivation p).d s) =
      (((Scheme.Modules.pullback i.liftCoborder).obj
            (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p))).val.map
          (homOfLE hle).op).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
                (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p))).val.app
            (op (i.coborderRange.ι ⁻¹ᵁ V))).hom
          ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d
            ((i.coborderRange.ι.app V).hom s))) := by
  rw [coborderPullbackDifferentialsIso_inv_eq,
    homEquiv_pullbackCongr_apply i.liftCoborder_ι.symm _ _ _ V hle _]
  refine congrArg (fun t ↦ (((Scheme.Modules.pullback i.liftCoborder).obj
      (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p))).val.map
    (homOfLE hle).op).hom t) ?_
  rw [homEquiv_pullbackComp_apply i.liftCoborder i.coborderRange.ι _ _ _ V _]
  have hsimp : (Scheme.Modules.pullbackComp i.liftCoborder i.coborderRange.ι).hom.app
        (Scheme.Hom.relativeDifferentials p) ≫
      ((Scheme.Modules.pullbackComp i.liftCoborder i.coborderRange.ι).inv.app
          (Scheme.Hom.relativeDifferentials p) ≫
        (Scheme.Modules.pullback i.liftCoborder).map
          (Scheme.Hom.relativeDifferentialsMap i.coborderRange.ι p
            (i.coborderRange.ι ≫ p) (𝟙 S) (by simp))) =
      (Scheme.Modules.pullback i.liftCoborder).map
        (Scheme.Hom.relativeDifferentialsMap i.coborderRange.ι p
          (i.coborderRange.ι ≫ p) (𝟙 S) (by simp)) := by
    rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  rw [hsimp]
  have hunit : (Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).homEquiv _ _
      ((Scheme.Modules.pullback i.liftCoborder).map
        (Scheme.Hom.relativeDifferentialsMap i.coborderRange.ι p
          (i.coborderRange.ι ≫ p) (𝟙 S) (by simp))) =
      Scheme.Hom.relativeDifferentialsMap i.coborderRange.ι p (i.coborderRange.ι ≫ p) (𝟙 S)
          (by simp) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
          (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p)) := by
    rw [Adjunction.homEquiv_unit]
    exact ((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.naturality _).symm
  rw [hunit, Adjunction.homEquiv_naturality_right]
  exact congrArg (fun t ↦ ((((Scheme.Modules.pullbackPushforwardAdjunction
      i.liftCoborder).unit.app
        (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p))).val.app
      (op (i.coborderRange.ι ⁻¹ᵁ V))).hom) t)
    (Scheme.Hom.relativeDifferentialsMap_app_d (f := i.coborderRange.ι) (p := p)
      (p' := i.coborderRange.ι ≫ p) (𝟙 S) (by simp) V s)


/-- The derivation `a ↦ 1 ⊗ d a` defining the first arrow of the conormal sequence, read as the
coborder comparison applied to the unit image of a universal differential. This is the definition
of `Stacks.ConormalSequenceRight.conormalDerivation` unfolded on a section. -/
theorem conormalDerivation_d (W : (i.coborderRange.toScheme).Opens)
    (x : Γ(i.coborderRange.toScheme, W)) :
    (Stacks.ConormalSequenceRight.conormalDerivation i p).d (X := op W) x =
      ((Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso i p).hom.val.app
          (op (i.liftCoborder ⁻¹ᵁ W)))
        ((((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
              (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p))).val.app (op W)).hom
          ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d x)) :=
  rfl

/-- **The derivation of the first arrow of the conormal sequence, on a section pulled back from
the ambient scheme.** For a section `s` of `𝒪_X` over `V`, the value of
`Stacks.ConormalSequenceRight.conormalDerivation` on `ι^♯ s` restricts, over `i⁻¹V`, to the
unit image `1 ⊗ d_{X/S} s` of the universal differential of `s`.

This is `Stacks.Thickenings.homEquiv_coborderPullbackDifferentialsIso_inv_apply` read in the
other direction across the coborder comparison. -/
theorem map_conormalDerivation_d_app (V : X.Opens)
    (hle : i ⁻¹ᵁ V ≤ i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ V)) (s : Γ(X, V)) :
    ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)).val.map
        (homOfLE hle).op
        ((Stacks.ConormalSequenceRight.conormalDerivation i p).d
          (X := op (i.coborderRange.ι ⁻¹ᵁ V)) ((i.coborderRange.ι.app V).hom s)) =
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (Scheme.Hom.relativeDifferentials p)).val.app (op V)).hom
        ((Scheme.Hom.universalRelativeDerivation p).d s) := by
  have hM := homEquiv_coborderPullbackDifferentialsIso_inv_apply i p V hle s
  rw [Adjunction.homEquiv_unit] at hM
  have hnat := modules_naturality_apply
    (Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso i p).hom hle
    ((((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
            (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p))).val.app
          (op (i.coborderRange.ι ⁻¹ᵁ V))).hom
      ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d
        ((i.coborderRange.ι.app V).hom s)))
  rw [conormalDerivation_d, ← hnat, ← hM]
  exact iso_inv_hom_app_apply
    (Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso i p) (i ⁻¹ᵁ V) _

end Coborder

/-! ### The difference map on the pulled-back differentials of the ambient target -/

section Difference

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y} {a' b' : X' ⟶ Y'}
  [IsClosedImmersion i] [IsImmersion j] (q : Y' ⟶ S)

/-- **`Stacks.Thickenings.diagonalConormalSheafMap` for the pair `(a', b')`**, with its source
written through `AlgebraicGeometry.Scheme.Modules.pullback` rather than through
`RingedSpaceModuleAdjunction.modulePullback`.

The two spellings of the pullback of sheaves of modules are definitionally equal, but
`AlgebraicGeometry.Scheme.Modules` is a structure copy of `SheafOfModules`, so the two hom types
are compared only after unfolding it. Doing that once, here, keeps every later statement in the
`AlgebraicGeometry.Scheme.Modules` vocabulary that
`Stacks.ConormalSequenceRight.conormalDifferential` is stated in. -/
def diagonalConormalSheafMapModules (hq : b' ≫ q = a' ≫ q) (ca : i ≫ a' = a ≫ j)
    (cb : i ≫ b' = a ≫ j) :
    (Scheme.Modules.pullback (a ≫ j)).obj (Scheme.Hom.relativeDifferentials q) ⟶
      Stacks.Conormal.conormalSheaf i :=
  show (modulePullback (a ≫ j).toLRSHom.toShHom).obj (Scheme.Hom.relativeDifferentials q) ⟶
      Stacks.Conormal.conormalSheaf i from
    diagonalConormalSheafMap hq ca cb

/-- **The map `a^*Ω_{Y'/S} ⟶ 𝒞_{X/X'}` of the difference of two lifts, transposed to `Y`.**
It is the map `θ` of [Stacks Project, Tag 01R4] for the diagonal square of the pair `(a', b')`,
read as a morphism `j^*Ω_{Y'/S} ⟶ a_*𝒞_{X/X'}` of sheaves of modules on `Y`. -/
def differenceDerivationMap (hq : b' ≫ q = a' ≫ q) (ca : i ≫ a' = a ≫ j)
    (cb : i ≫ b' = a ≫ j) :
    (Scheme.Modules.pullback j).obj (Scheme.Hom.relativeDifferentials q) ⟶
      (Scheme.Modules.pushforward a).obj (Stacks.Conormal.conormalSheaf i) :=
  (Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
      ((Scheme.Modules.pullback j).obj (Scheme.Hom.relativeDifferentials q))
      (Stacks.Conormal.conormalSheaf i)
    ((Scheme.Modules.pullbackComp a j).hom.app (Scheme.Hom.relativeDifferentials q) ≫
      diagonalConormalSheafMapModules q hq ca cb)

omit [IsImmersion j] in
/-- **The transpose of `Stacks.Thickenings.differenceDerivationMap` is the difference
derivation.** On the universal differential of a section `s` of `𝒪_{Y'}` it takes the value
`Stacks.Thickenings.liftDifferenceDerivation` does, namely the conormal class of
`(a')^♯ s - (b')^♯ s`. -/
theorem homEquiv_differenceDerivationMap_d (hq : b' ≫ q = a' ≫ q) (ca : i ≫ a' = a ≫ j)
    (cb : i ≫ b' = a ≫ j) (V : Y'.Opens) (s : Γ(Y', V)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv
            (Scheme.Hom.relativeDifferentials q)
            ((Scheme.Modules.pushforward a).obj (Stacks.Conormal.conormalSheaf i))
          (differenceDerivationMap q hq ca cb)).val.app (op V)).hom
        ((Scheme.Hom.universalRelativeDerivation q).d s) =
      (liftDifferenceDerivation hq ca cb).d (X := op V) s :=
  (homEquiv_pullbackComp_apply a j (Scheme.Hom.relativeDifferentials q)
    (Stacks.Conormal.conormalSheaf i) (diagonalConormalSheafMapModules q hq ca cb) V
    ((Scheme.Hom.universalRelativeDerivation q).d s)).symm

omit [IsImmersion j] in
/-- **`Stacks.Thickenings.differenceDerivationMap` on the unit image of a universal
differential.** This is `Stacks.Thickenings.homEquiv_differenceDerivationMap_d` with the
transpose written out. -/
theorem differenceDerivationMap_unit_d (hq : b' ≫ q = a' ≫ q) (ca : i ≫ a' = a ≫ j)
    (cb : i ≫ b' = a ≫ j) (V : Y'.Opens) (s : Γ(Y', V)) :
    ((differenceDerivationMap q hq ca cb).val.app (op (j ⁻¹ᵁ V))).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
            (Scheme.Hom.relativeDifferentials q)).val.app (op V)).hom
          ((Scheme.Hom.universalRelativeDerivation q).d s)) =
      (liftDifferenceDerivation hq ca cb).d (X := op V) s := by
  rw [← homEquiv_differenceDerivationMap_d q hq ca cb V s, Adjunction.homEquiv_unit]
  rfl

/-! ### The difference kills the defining ideal of the target thickening -/

omit [IsClosedImmersion i] [IsImmersion j] in
/-- **A section of the defining ideal of `j` pulls back into the defining ideal of `i`.** If
`j^♯ s = 0` then `i^♯ (a')^♯ s = 0`, because both routes around the square `i ≫ a' = a ≫ j`
agree. -/
theorem app_app_eq_zero_of_app_eq_zero (ca : i ≫ a' = a ≫ j) (V : Y'.Opens) (s : Γ(Y', V))
    (hs : (j.app V).hom s = 0) : (i.app (a' ⁻¹ᵁ V)).hom ((a'.app V).hom s) = 0 := by
  rw [← app_square_eq ca V s, hs, map_zero, map_zero]

omit [IsClosedImmersion i] [IsImmersion j] in
/-- The same vanishing after restriction to a smaller open of `X'`. -/
theorem app_map_app_eq_zero_of_app_eq_zero (ca : i ≫ a' = a ≫ j) (V : Y'.Opens)
    {U : X'.Opens} (hU : U ≤ a' ⁻¹ᵁ V) (s : Γ(Y', V)) (hs : (j.app V).hom s = 0) :
    (i.app U).hom ((X'.presheaf.map (homOfLE hU).op).hom ((a'.app V).hom s)) = 0 := by
  rw [app_presheaf_map i (homOfLE hU).op ((a'.app V).hom s),
    app_app_eq_zero_of_app_eq_zero ca V s hs, map_zero]

/-- **Hypothesis (2) of [Stacks Project, Tag 04FG] makes the two comorphisms agree on the
defining ideal of `Y ⊂ Y'`.** If the two maps `a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of
[Stacks Project, Tag 01R4] induced by `(a, a')` and `(a, b')` coincide, then `(a')^♯ s` and
`(b')^♯ s` agree, over the open `(b')⁻¹V ⊓ (a')⁻¹V`, for every section `s` of the defining ideal
sheaf of `j` over `V`.

Both comorphisms are read off their conormal classes: the map of [Stacks Project, Tag 01R4]
carries the conormal class of `s` to the conormal class of the image of `s`
(`Stacks.Conormal.conormalClass_immersionConormalSheafMap`), and for a first-order thickening the
conormal class of a section determines the section
(`Stacks.Conormal.firstOrderImmersionConormalSheafι_conormalClass_of_eq`). -/
theorem liftDiffSection_eq_zero_of_conormalSheafMap_eq (hi : i.ker ^ 2 = ⊥)
    (ca : i ≫ a' = a ≫ j) (cb : i ≫ b' = a ≫ j)
    (hC : Stacks.Immersion.immersionConormalSheafMap i j a a'
        (Stacks.Immersion.toShHom_square ca) =
      Stacks.Immersion.immersionConormalSheafMap i j a b'
        (Stacks.Immersion.toShHom_square cb))
    (V : Y'.Opens) (s : Γ(Y', V)) (hs : (j.app V).hom s = 0) :
    liftDiffSection a' b' V s = 0 := by
  have hle_a : liftPairOpen a' b' V ≤ a' ⁻¹ᵁ V := inf_le_right
  have hle_b : liftPairOpen a' b' V ≤ b' ⁻¹ᵁ V := inf_le_left
  have hL : i ⁻¹ᵁ (liftPairOpen a' b' V) = a ⁻¹ᵁ (j ⁻¹ᵁ V) := preimage_liftPairOpen ca cb V
  -- the conormal class of `s` under the map of [Stacks Project, Tag 01R4] for a lift `c'`, over
  -- the common open `(b')⁻¹V ⊓ (a')⁻¹V`, is the class of `(c')^♯ s`
  have key : ∀ {c' : X' ⟶ Y'} (cc : i ≫ c' = a ≫ j) (hle : liftPairOpen a' b' V ≤ c' ⁻¹ᵁ V),
      (((modulePullbackPushforwardAdjunction a.toLRSHom.toShHom).homEquiv _ _
          (Stacks.Immersion.immersionConormalSheafMap i j a c'
            (Stacks.Immersion.toShHom_square cc))).val.app (op (j ⁻¹ᵁ V)))
        (Stacks.Conormal.conormalClass j V le_rfl s hs) =
        Stacks.Conormal.conormalClass i (liftPairOpen a' b' V) hL.ge
          ((X'.presheaf.map (homOfLE hle).op).hom ((c'.app V).hom s))
          (app_map_app_eq_zero_of_app_eq_zero cc V hle s hs) := fun {c'} cc hle ↦ by
    have hsq := preimage_square cc V
    have hA := Stacks.Conormal.conormalClass_immersionConormalSheafMap i j a c' cc V
      (a ⁻¹ᵁ (j ⁻¹ᵁ V)) hsq.ge le_rfl s hs
    have hr := Stacks.Conormal.conormalClass_restrict i (c' ⁻¹ᵁ V) (liftPairOpen a' b' V)
      hle hsq.ge hL.ge le_rfl ((c'.app V).hom s) (app_app_eq_zero_of_app_eq_zero cc V s hs)
      (app_map_app_eq_zero_of_app_eq_zero cc V hle s hs)
    exact ((module_map_self le_rfl _).symm.trans hA).trans
      ((module_map_self le_rfl _).symm.trans hr)
  have ha := key ca hle_a
  rw [hC] at ha
  have hkey := ha.symm.trans (key cb hle_b)
  have hι := congrArg
    (fun m ↦ (Stacks.Thickenings.firstOrderImmersionConormalSheafι i hi).val.app
      (op (liftPairOpen a' b' V))
      ((Stacks.Conormal.conormalSheaf i).val.map (homOfLE hL.le).op m)) hkey
  rw [Stacks.Conormal.firstOrderImmersionConormalSheafι_conormalClass_of_eq i hi
      (liftPairOpen a' b' V) hL.ge hL _ _,
    Stacks.Conormal.firstOrderImmersionConormalSheafι_conormalClass_of_eq i hi
      (liftPairOpen a' b' V) hL.ge hL _ _] at hι
  change (a'.appLE V (liftPairOpen a' b' V) hle_a).hom s -
    (b'.appLE V (liftPairOpen a' b' V) hle_b).hom s = 0
  rw [Scheme.Hom.appLE, Scheme.Hom.appLE, CommRingCat.comp_apply, CommRingCat.comp_apply, hι,
    sub_self]

/-! ### The difference map kills the first arrow of the conormal sequence -/

/-- **The difference derivation vanishes on the defining ideal of `Y ⊂ Y'`.** This is
`Stacks.Thickenings.liftDiffSection_eq_zero_of_conormalSheafMap_eq` read on the derivation of
[Stacks Project, Tag 04FL]: its value is the conormal class of the difference, and the difference
itself is zero. -/
theorem liftDifferenceDerivation_d_eq_zero (hi : i.ker ^ 2 = ⊥) (hq : b' ≫ q = a' ≫ q)
    (ca : i ≫ a' = a ≫ j) (cb : i ≫ b' = a ≫ j)
    (hC : Stacks.Immersion.immersionConormalSheafMap i j a a'
        (Stacks.Immersion.toShHom_square ca) =
      Stacks.Immersion.immersionConormalSheafMap i j a b'
        (Stacks.Immersion.toShHom_square cb))
    (V : Y'.Opens) (s : Γ(Y', V)) (hs : (j.app V).hom s = 0) :
    (liftDifferenceDerivation hq ca cb).d (X := op V) s = 0 := by
  rw [liftDifferenceDerivation_d, Stacks.Conormal.conormalClass_congr i
      (liftPairOpen a' b' V) (le_preimage_liftPairOpen ca cb V)
      (liftDiffSection_eq_zero_of_conormalSheafMap_eq hi ca cb hC V s hs) _ (map_zero _)]
  exact Stacks.Conormal.conormalClass_zero i (liftPairOpen a' b' V)
    (le_preimage_liftPairOpen ca cb V) (map_zero _)

/-- **The difference map kills the derivation that defines the first arrow of the conormal
sequence of `j`.** For a section `x` of the defining ideal sheaf of the closed factor of `j`
over an open `W` of the coborder neighbourhood, the value of
`Stacks.Thickenings.differenceDerivationMap` on `1 ⊗ d x` vanishes.

The open `W` is the preimage of `V = ι(W)`, so `x` comes from a section `s` of `𝒪_{Y'}` over
`V`; that section is killed by `j^♯`, and the value in question is, after a restriction along an
equality of opens, the value of the difference derivation of [Stacks Project, Tag 04FL] on `s`,
which vanishes by `Stacks.Thickenings.liftDifferenceDerivation_d_eq_zero`. -/
theorem differenceDerivationMap_conormalDerivation_d_eq_zero (hi : i.ker ^ 2 = ⊥)
    (hq : b' ≫ q = a' ≫ q) (ca : i ≫ a' = a ≫ j) (cb : i ≫ b' = a ≫ j)
    (hC : Stacks.Immersion.immersionConormalSheafMap i j a a'
        (Stacks.Immersion.toShHom_square ca) =
      Stacks.Immersion.immersionConormalSheafMap i j a b'
        (Stacks.Immersion.toShHom_square cb))
    (W : (j.coborderRange.toScheme).Opens) (x : Γ(j.coborderRange.toScheme, W))
    (hx : (j.liftCoborder.app W).hom x = 0) :
    ((differenceDerivationMap q hq ca cb).val.app (op (j.liftCoborder ⁻¹ᵁ W))).hom
        ((Stacks.ConormalSequenceRight.conormalDerivation j q).d (X := op W) x) = 0 := by
  have hpre : j.coborderRange.ι ⁻¹ᵁ (j.coborderRange.ι ''ᵁ W) = W :=
    Scheme.Hom.preimage_image_eq _ W
  have hfac : j.liftCoborder ⁻¹ᵁ (j.coborderRange.ι ⁻¹ᵁ (j.coborderRange.ι ''ᵁ W)) =
      j ⁻¹ᵁ (j.coborderRange.ι ''ᵁ W) :=
    congrArg (fun f : Y ⟶ Y' ↦ f ⁻¹ᵁ (j.coborderRange.ι ''ᵁ W)) j.liftCoborder_ι
  have hjV : j ⁻¹ᵁ (j.coborderRange.ι ''ᵁ W) = j.liftCoborder ⁻¹ᵁ W :=
    hfac.symm.trans (congrArg (fun U : (j.coborderRange.toScheme).Opens ↦
      j.liftCoborder ⁻¹ᵁ U) hpre)
  -- the section of `𝒪_{Y'}` that `x` comes from
  have hιs : (j.coborderRange.ι.app (j.coborderRange.ι ''ᵁ W)).hom
        ((j.coborderRange.ι.appIso W).inv x) =
      ((j.coborderRange.toScheme).presheaf.map (eqToHom hpre).op).hom x :=
    (CommRingCat.comp_apply _ _ x).symm.trans
      (ConcreteCategory.congr_hom (Scheme.Hom.appIso_inv_app j.coborderRange.ι W) x)
  have hjs : (j.app (j.coborderRange.ι ''ᵁ W)).hom ((j.coborderRange.ι.appIso W).inv x) = 0 := by
    have h := congrArg
      (fun φ : Γ(Y', j.coborderRange.ι ''ᵁ W) ⟶
          Γ(Y, j.liftCoborder ⁻¹ᵁ (j.coborderRange.ι ⁻¹ᵁ (j.coborderRange.ι ''ᵁ W))) ↦
        φ.hom ((j.coborderRange.ι.appIso W).inv x))
      (Scheme.Hom.congr_app j.liftCoborder_ι (j.coborderRange.ι ''ᵁ W))
    simp only [Scheme.Hom.comp_app, CommRingCat.comp_apply] at h
    rw [hιs, app_presheaf_map j.liftCoborder (eqToHom hpre).op x, hx, map_zero] at h
    exact presheaf_map_injective (eqToHom hfac).op (eqToHom hfac.symm).op
      (h.symm.trans (map_zero _).symm)
  -- the value of the derivation on `ι^♯ s` is the restriction of its value on `x`
  have hd : (Stacks.ConormalSequenceRight.conormalDerivation j q).d
        (X := op (j.coborderRange.ι ⁻¹ᵁ (j.coborderRange.ι ''ᵁ W)))
        ((j.coborderRange.ι.app (j.coborderRange.ι ''ᵁ W)).hom
          ((j.coborderRange.ι.appIso W).inv x)) =
      ((Scheme.Modules.pushforward j.liftCoborder).obj
            ((Scheme.Modules.pullback j).obj (Scheme.Hom.relativeDifferentials q))).val.map
        (eqToHom hpre).op
        ((Stacks.ConormalSequenceRight.conormalDerivation j q).d (X := op W) x) := by
    rw [hιs]
    exact (Stacks.ConormalSequenceRight.conormalDerivation j q).d_map (eqToHom hpre).op x
  -- the restriction of the value on `x` to `j⁻¹V` is the unit image of `d s`
  have hkey : ((Scheme.Modules.pullback j).obj (Scheme.Hom.relativeDifferentials q)).val.map
        (homOfLE hjV.le).op
        ((Stacks.ConormalSequenceRight.conormalDerivation j q).d (X := op W) x) =
      (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
          (Scheme.Hom.relativeDifferentials q)).val.app
        (op (j.coborderRange.ι ''ᵁ W))).hom
        ((Scheme.Hom.universalRelativeDerivation q).d
          ((j.coborderRange.ι.appIso W).inv x)) := by
    rw [← map_conormalDerivation_d_app j q (j.coborderRange.ι ''ᵁ W) hfac.ge
      ((j.coborderRange.ι.appIso W).inv x), hd]
    exact (module_map_map (((Opens.map j.liftCoborder.base).map (eqToHom hpre)).op)
      (homOfLE hfac.ge).op (homOfLE hjV.le).op _).symm
  -- conclude by restricting along the equality of opens
  refine module_map_injective_of_le hjV.le hjV.ge ?_
  rw [map_zero]
  refine Eq.trans (modules_naturality_apply (differenceDerivationMap q hq ca cb) hjV.le
    ((Stacks.ConormalSequenceRight.conormalDerivation j q).d (X := op W) x)).symm ?_
  rw [hkey]
  exact (differenceDerivationMap_unit_d q hq ca cb (j.coborderRange.ι ''ᵁ W)
      ((j.coborderRange.ι.appIso W).inv x)).trans
    (liftDifferenceDerivation_d_eq_zero q hi hq ca cb hC (j.coborderRange.ι ''ᵁ W)
      ((j.coborderRange.ι.appIso W).inv x) hjs)

/-! ### The descent along the conormal sequence -/

/-- **The transpose of the first arrow of the conormal sequence, followed by the difference map,
is zero.** On a section `x` of the defining ideal sheaf of the closed factor of `j` the composite
is the value of the difference map on `1 ⊗ d x`, which vanishes by
`Stacks.Thickenings.differenceDerivationMap_conormalDerivation_d_eq_zero`. -/
theorem conormalDifferentialTranspose_comp_differenceDerivationMap_eq (hi : i.ker ^ 2 = ⊥)
    (hq : b' ≫ q = a' ≫ q) (ca : i ≫ a' = a ≫ j) (cb : i ≫ b' = a ≫ j)
    (hC : Stacks.Immersion.immersionConormalSheafMap i j a a'
        (Stacks.Immersion.toShHom_square ca) =
      Stacks.Immersion.immersionConormalSheafMap i j a b'
        (Stacks.Immersion.toShHom_square cb)) :
    Stacks.ConormalSequenceRight.conormalDifferentialTranspose j q ≫
        (Scheme.Modules.pushforward j.liftCoborder).map (differenceDerivationMap q hq ca cb) =
      Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalComparison j ≫
        (modulePushforward j.liftCoborder.toLRSHom.toShHom).map
          (0 : (Scheme.Modules.pullback j.liftCoborder).obj
              (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdeal j).toSheafOfModules ⟶
            (Scheme.Modules.pushforward a).obj (Stacks.Conormal.conormalSheaf i)) := by
  ext W x
  obtain ⟨W⟩ := W
  have hR : ((Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalComparison j ≫
        (modulePushforward j.liftCoborder.toLRSHom.toShHom).map
          (0 : (Scheme.Modules.pullback j.liftCoborder).obj
              (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdeal j).toSheafOfModules ⟶
            (Scheme.Modules.pushforward a).obj
              (Stacks.Conormal.conormalSheaf i))).val.app (op W)).hom x = 0 :=
    (congrArg (fun m ↦
        ((Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalComparison j ≫ m).val.app
          (op W)).hom x)
      (Functor.map_zero (modulePushforward j.liftCoborder.toLRSHom.toShHom)
        ((Scheme.Modules.pullback j.liftCoborder).obj
          (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdeal j).toSheafOfModules)
        ((Scheme.Modules.pushforward a).obj (Stacks.Conormal.conormalSheaf i)))).trans rfl
  refine Eq.trans ?_ hR.symm
  have e1 : ((Stacks.ConormalSequenceRight.conormalDifferentialTranspose j q ≫
          (Scheme.Modules.pushforward j.liftCoborder).map
            (differenceDerivationMap q hq ca cb)).val.app (op W)).hom x =
      ((differenceDerivationMap q hq ca cb).val.app (op (j.liftCoborder ⁻¹ᵁ W))).hom
        (((Stacks.ConormalSequenceRight.conormalDifferentialTranspose j q).val.app
          (op W)).hom x) := rfl
  have e2 : (((Stacks.ConormalSequenceRight.conormalDifferentialTranspose j q).val.app
        (op W)).hom x) =
      (Stacks.ConormalSequenceRight.conormalDerivation j q).d (X := op W) x.1 :=
    Stacks.ConormalSequenceRight.idealDerivationHom_val_app _ _ _ _ (op W) x
  rw [e1, e2]
  exact differenceDerivationMap_conormalDerivation_d_eq_zero q hi hq ca cb hC W x.1 x.2

/-- **The difference map kills the first arrow of the conormal sequence of `j`**, which is
hypothesis (2) of [Stacks Project, Tag 04FG] in the form the descent consumes.

A morphism out of the conormal sheaf is determined by its composite with the quotient map from
the defining ideal sheaf
(`Stacks.AlgebraicGeometry.RegularIdealSheaf.existsUnique_hom_conormalComparison`), and that
composite is `Stacks.Thickenings.conormalDifferentialTranspose_comp_differenceDerivationMap_eq`. -/
theorem conormalDifferential_comp_differenceDerivationMap (hi : i.ker ^ 2 = ⊥)
    (hq : b' ≫ q = a' ≫ q) (ca : i ≫ a' = a ≫ j) (cb : i ≫ b' = a ≫ j)
    (hC : Stacks.Immersion.immersionConormalSheafMap i j a a'
        (Stacks.Immersion.toShHom_square ca) =
      Stacks.Immersion.immersionConormalSheafMap i j a b'
        (Stacks.Immersion.toShHom_square cb)) :
    Stacks.ConormalSequenceRight.conormalDifferential j q ≫ differenceDerivationMap q hq ca cb =
      (0 : (Scheme.Modules.pullback j.liftCoborder).obj
          (Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdeal j).toSheafOfModules ⟶
        (Scheme.Modules.pushforward a).obj (Stacks.Conormal.conormalSheaf i)) :=
  (Stacks.AlgebraicGeometry.RegularIdealSheaf.existsUnique_hom_conormalComparison j _).unique
    (by
      refine Eq.trans ?_
        (conormalDifferentialTranspose_comp_differenceDerivationMap_eq q hi hq ca cb hC)
      refine Eq.trans (congrArg
        (fun m ↦ Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalComparison j ≫ m)
        ((modulePushforward j.liftCoborder.toLRSHom.toShHom).map_comp
          (Stacks.ConormalSequenceRight.conormalDifferential j q)
          (differenceDerivationMap q hq ca cb))) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      exact congrArg
        (fun m ↦ m ≫ (modulePushforward j.liftCoborder.toLRSHom.toShHom).map
          (differenceDerivationMap q hq ca cb))
        (Stacks.ConormalSequenceRight.conormalComparison_comp_conormalDifferential j q))
    rfl

/-- **The derivation `D` of [Stacks Project, Tag 04FG] at sheaf level, as a morphism out of
`Ω_{Y/S}`.** The difference map `j^*Ω_{Y'/S} ⟶ a_*𝒞_{X/X'}` kills the first arrow of the
conormal sequence of `j`, and `Ω_{Y/S}` is the cokernel of that arrow
(`Stacks.ConormalSequenceRight.conormalShortComplex_exact`), so the difference map descends. -/
def differenceDerivationHom (hi : i.ker ^ 2 = ⊥) (hq : b' ≫ q = a' ≫ q)
    (ca : i ≫ a' = a ≫ j) (cb : i ≫ b' = a ≫ j)
    (hC : Stacks.Immersion.immersionConormalSheafMap i j a a'
        (Stacks.Immersion.toShHom_square ca) =
      Stacks.Immersion.immersionConormalSheafMap i j a b'
        (Stacks.Immersion.toShHom_square cb)) :
    Scheme.Hom.relativeDifferentials (j ≫ q) ⟶
      (Scheme.Modules.pushforward a).obj (Stacks.Conormal.conormalSheaf i) :=
  haveI : Epi (Stacks.ConormalSequenceRight.conormalShortComplex j q).g :=
    Stacks.ConormalSequenceRight.epi_conormalShortComplex_g j q
  (Stacks.ConormalSequenceRight.conormalShortComplex_exact j q).gIsCokernel.desc
    (Limits.CokernelCofork.ofπ (differenceDerivationMap q hq ca cb)
      (conormalDifferential_comp_differenceDerivationMap q hi hq ca cb hC))

/-- **The descent recovers the difference map.** Composing
`Stacks.Thickenings.differenceDerivationHom` with the canonical map
`j^*Ω_{Y'/S} ⟶ Ω_{Y/S}` of [Stacks Project, Tag 01UV] gives back
`Stacks.Thickenings.differenceDerivationMap`. -/
theorem relativeDifferentialsMap_comp_differenceDerivationHom (hi : i.ker ^ 2 = ⊥)
    (hq : b' ≫ q = a' ≫ q) (ca : i ≫ a' = a ≫ j) (cb : i ≫ b' = a ≫ j)
    (hC : Stacks.Immersion.immersionConormalSheafMap i j a a'
        (Stacks.Immersion.toShHom_square ca) =
      Stacks.Immersion.immersionConormalSheafMap i j a b'
        (Stacks.Immersion.toShHom_square cb)) :
    Scheme.Hom.relativeDifferentialsMap j q (j ≫ q) (𝟙 S) (by simp) ≫
        differenceDerivationHom q hi hq ca cb hC =
      differenceDerivationMap q hq ca cb :=
  have : Epi (Stacks.ConormalSequenceRight.conormalShortComplex j q).g :=
    Stacks.ConormalSequenceRight.epi_conormalShortComplex_g j q
  (Stacks.ConormalSequenceRight.conormalShortComplex_exact j q).gIsCokernel.fac
    (Limits.CokernelCofork.ofπ (differenceDerivationMap q hq ca cb)
      (conormalDifferential_comp_differenceDerivationMap q hi hq ca cb hC))
    Limits.WalkingParallelPair.one

/-! ### The difference derivation of Tag 04FG, at sheaf level -/

/-- **The `𝒪_S`-derivation `D : 𝒪_Y ⟶ a_*𝒞_{X/X'}` of [Stacks Project, Tag 04FG], at sheaf
level.** Let `i : X ⟶ X'` be a first-order thickening, let `j : Y ⟶ Y'` be an immersion with
structure morphism `q : Y' ⟶ S`, and let `(a, a')` and `(a, b')` be two morphisms of thickenings
over `S` with the same reduction `a` — hypothesis (1) of the source — whose two induced maps
`a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 01R4] agree — hypothesis (2). Then the
difference `(a')^♯ - (b')^♯` factors through this derivation; the factorization is
`Stacks.Thickenings.firstOrderImmersionConormalSheafι_differenceDerivation_d`.

It is `Stacks.Thickenings.differenceDerivationHom` composed with the universal relative
derivation of `Y` over `S`, so that it is an `𝒪_S`-derivation by construction. -/
@[stacks 04FG "the derivation D, for arbitrary X' and Y'"]
def differenceDerivation (hi : i.ker ^ 2 = ⊥) (hq : b' ≫ q = a' ≫ q) (ca : i ≫ a' = a ≫ j)
    (cb : i ≫ b' = a ≫ j)
    (hC : Stacks.Immersion.immersionConormalSheafMap i j a a'
        (Stacks.Immersion.toShHom_square ca) =
      Stacks.Immersion.immersionConormalSheafMap i j a b'
        (Stacks.Immersion.toShHom_square cb)) :
    SheafOfModules.SheafDerivation (inverseImageStructureMap (j ≫ q))
      ((Scheme.Modules.pushforward a).obj (Stacks.Conormal.conormalSheaf i)) :=
  (Scheme.Hom.universalRelativeDerivation (j ≫ q)).postcomp
    (differenceDerivationHom q hi hq ca cb hC).val

/-- **The difference derivation on a section pulled back from `𝒪_{Y'}`.** On `j^♯ s` it takes the
value the difference derivation of [Stacks Project, Tag 04FL] takes on `s`, namely the conormal
class of `(a')^♯ s - (b')^♯ s`.

This is `Stacks.Thickenings.relativeDifferentialsMap_comp_differenceDerivationHom` read on
sections, using that the canonical map `j^*Ω_{Y'/S} ⟶ Ω_{Y/S}` sends `1 ⊗ d_{Y'/S} s` to
`d_{Y/S} (j^♯ s)`. -/
theorem differenceDerivation_d_app (hi : i.ker ^ 2 = ⊥) (hq : b' ≫ q = a' ≫ q)
    (ca : i ≫ a' = a ≫ j) (cb : i ≫ b' = a ≫ j)
    (hC : Stacks.Immersion.immersionConormalSheafMap i j a a'
        (Stacks.Immersion.toShHom_square ca) =
      Stacks.Immersion.immersionConormalSheafMap i j a b'
        (Stacks.Immersion.toShHom_square cb))
    (V : Y'.Opens) (s : Γ(Y', V)) :
    (differenceDerivation q hi hq ca cb hC).d (X := op (j ⁻¹ᵁ V)) ((j.app V).hom s) =
      (liftDifferenceDerivation hq ca cb).d (X := op V) s := by
  have h3 : (Scheme.Hom.universalRelativeDerivation (j ≫ q)).d ((j.app V).hom s) =
      ((Scheme.Hom.relativeDifferentialsMap j q (j ≫ q) (𝟙 S) (by simp)).val.app
          (op (j ⁻¹ᵁ V))).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
            (Scheme.Hom.relativeDifferentials q)).val.app (op V)).hom
          ((Scheme.Hom.universalRelativeDerivation q).d s)) := by
    rw [← Scheme.Hom.relativeDifferentialsMap_app_d (f := j) (p := q) (p' := j ≫ q)
      (𝟙 S) (by simp) V s, Adjunction.homEquiv_unit]
    rfl
  refine Eq.trans ?_ (differenceDerivationMap_unit_d q hq ca cb V s)
  refine Eq.trans (congrArg (fun z ↦
      ((differenceDerivationHom q hi hq ca cb hC).val.app (op (j ⁻¹ᵁ V))).hom z) h3) ?_
  exact congrArg (fun m : (Scheme.Modules.pullback j).obj (Scheme.Hom.relativeDifferentials q) ⟶
      (Scheme.Modules.pushforward a).obj (Stacks.Conormal.conormalSheaf i) ↦
    (m.val.app (op (j ⁻¹ᵁ V))).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
          (Scheme.Hom.relativeDifferentials q)).val.app (op V)).hom
        ((Scheme.Hom.universalRelativeDerivation q).d s)))
    (relativeDifferentialsMap_comp_differenceDerivationHom q hi hq ca cb hC)

/-- **The factorization of [Stacks Project, Tag 04FG], at sheaf level.** The difference
`(a')^♯ s - (b')^♯ s` of the two comorphisms, on a section `s` of `𝒪_{Y'}` over `V` and read over
the open `(b')⁻¹V ⊓ (a')⁻¹V` of `X'` where both are defined, is the image of
`D (j^♯ s)` under the inclusion `𝒞_{X/X'} ⟶ 𝒪_{X'}` of the conormal sheaf of the first-order
thickening `i`.

That is the composite `𝒪_{Y'} ⟶ 𝒪_Y --D--> a_*𝒞_{X/X'} ⟶ a_*𝒪_{X'}` of the source. -/
@[stacks 04FG "the factorization, for arbitrary X' and Y'"]
theorem firstOrderImmersionConormalSheafι_differenceDerivation_d (hi : i.ker ^ 2 = ⊥)
    (hq : b' ≫ q = a' ≫ q) (ca : i ≫ a' = a ≫ j) (cb : i ≫ b' = a ≫ j)
    (hC : Stacks.Immersion.immersionConormalSheafMap i j a a'
        (Stacks.Immersion.toShHom_square ca) =
      Stacks.Immersion.immersionConormalSheafMap i j a b'
        (Stacks.Immersion.toShHom_square cb))
    (V : Y'.Opens) (s : Γ(Y', V)) :
    (Stacks.Thickenings.firstOrderImmersionConormalSheafι i hi).val.app
        (op (liftPairOpen a' b' V))
        ((Stacks.Conormal.conormalSheaf i).val.map
          (homOfLE (preimage_liftPairOpen ca cb V).le).op
          ((differenceDerivation q hi hq ca cb hC).d (X := op (j ⁻¹ᵁ V))
            ((j.app V).hom s))) =
      (a'.appLE V (liftPairOpen a' b' V) inf_le_right).hom s -
        (b'.appLE V (liftPairOpen a' b' V) inf_le_left).hom s := by
  rw [differenceDerivation_d_app q hi hq ca cb hC V s]
  exact firstOrderImmersionConormalSheafι_liftDifferenceDerivation_d hi hq ca cb V s

/-! ### The datum `θ` and the action of Tag 0CK1 -/

omit [IsImmersion j] in
/-- **A conormal section read inside `𝒪_{X'}`, restricted to a smaller open.** The restriction of
`Stacks.Thickenings.conormalSectionι` to an open `U ≤ (a')⁻¹V` whose preimage under `i` is still
`a⁻¹j⁻¹V` is the inclusion of the conormal sheaf read over `U`. -/
theorem map_conormalSectionι (hi : i.ker ^ 2 = ⊥) (ca : i ≫ a' = a ≫ j) (V : Y'.Opens)
    {U : X'.Opens} (hU : U ≤ a' ⁻¹ᵁ V) (hUi : i ⁻¹ᵁ U = a ⁻¹ᵁ (j ⁻¹ᵁ V))
    (m : (Stacks.Conormal.conormalSheaf i).val.obj (op (a ⁻¹ᵁ (j ⁻¹ᵁ V)))) :
    (X'.presheaf.map (homOfLE hU).op).hom (conormalSectionι hi ca V m) =
      (Stacks.Thickenings.firstOrderImmersionConormalSheafι i hi).val.app (op U)
        ((Stacks.Conormal.conormalSheaf i).val.map (homOfLE hUi.le).op m) := by
  have hnat : (Stacks.Thickenings.firstOrderImmersionConormalSheafι i hi).val.app (op U)
        ((Stacks.Conormal.conormalSheaf i).val.map (homOfLE (i.preimage_mono hU)).op
          ((Stacks.Conormal.conormalSheaf i).val.map
            (eqToHom (preimage_square ca V)).op m)) =
      (X'.presheaf.map (homOfLE hU).op).hom
        ((Stacks.Thickenings.firstOrderImmersionConormalSheafι i hi).val.app (op (a' ⁻¹ᵁ V))
          ((Stacks.Conormal.conormalSheaf i).val.map
            (eqToHom (preimage_square ca V)).op m)) :=
    PresheafOfModules.naturality_apply
      (Stacks.Thickenings.firstOrderImmersionConormalSheafι i hi).val (homOfLE hU).op _
  exact hnat.symm.trans (congrArg
    (fun n ↦ (Stacks.Thickenings.firstOrderImmersionConormalSheafι i hi).val.app (op U) n)
    (module_map_map (eqToHom (preimage_square ca V)).op (homOfLE (i.preimage_mono hU)).op
      (homOfLE hUi.le).op m))

omit [IsImmersion j] in
/-- **The derivation of Equation [Stacks Project, Tag 04BV] attached to a transposed map.** For
`ψ : Ω_{Y/S} ⟶ a_*𝒞_{X/X'}`, the derivation `Stacks.Thickenings.derivationSectionι` of the
transpose of `ψ` is `ψ` applied to the universal differential, read inside `𝒪_{X'}`. -/
theorem derivationSectionι_homEquiv_symm (hi : i.ker ^ 2 = ⊥) (ca : i ≫ a' = a ≫ j)
    (ψ : Scheme.Hom.relativeDifferentials (j ≫ q) ⟶
      (Scheme.Modules.pushforward a).obj (Stacks.Conormal.conormalSheaf i))
    (V : Y'.Opens) (y : Γ(Y, j ⁻¹ᵁ V)) :
    derivationSectionι hi q ca
        (((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
          (Scheme.Hom.relativeDifferentials (j ≫ q))
          (Stacks.Conormal.conormalSheaf i)).symm ψ) V y =
      conormalSectionι hi ca V ((ψ.val.app (op (j ⁻¹ᵁ V))).hom
        ((Scheme.Hom.universalRelativeDerivation (j ≫ q)).d y)) := by
  rw [derivationSectionι_eq, Equiv.apply_symm_apply]

/-- **The datum `θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}` of the difference of two lifts.** It is
`Stacks.Thickenings.differenceDerivationHom` transposed along `a^* ⊣ a_*`; equivalently, it is
the map that the universal property of `Ω_{Y/S}` attaches to the `𝒪_S`-derivation
`Stacks.Thickenings.differenceDerivation`. -/
def differenceDerivationTheta (hi : i.ker ^ 2 = ⊥) (hq : b' ≫ q = a' ≫ q)
    (ca : i ≫ a' = a ≫ j) (cb : i ≫ b' = a ≫ j)
    (hC : Stacks.Immersion.immersionConormalSheafMap i j a a'
        (Stacks.Immersion.toShHom_square ca) =
      Stacks.Immersion.immersionConormalSheafMap i j a b'
        (Stacks.Immersion.toShHom_square cb)) :
    (Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials (j ≫ q)) ⟶
      Stacks.Conormal.conormalSheaf i :=
  ((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
    (Scheme.Hom.relativeDifferentials (j ≫ q)) (Stacks.Conormal.conormalSheaf i)).symm
    (differenceDerivationHom q hi hq ca cb hC)

/-- **The derivation of Equation [Stacks Project, Tag 04BV] attached to
`Stacks.Thickenings.differenceDerivationTheta`.** On a section pulled back from `𝒪_{Y'}` it is
the difference derivation of [Stacks Project, Tag 04FL], read inside `𝒪_{X'}` along a lift `c'`
of `a` — any lift, since the conormal sheaf is read through `i` alone. -/
theorem derivationSectionι_differenceDerivationTheta (hi : i.ker ^ 2 = ⊥)
    (hq : b' ≫ q = a' ≫ q) (ca : i ≫ a' = a ≫ j) (cb : i ≫ b' = a ≫ j)
    (hC : Stacks.Immersion.immersionConormalSheafMap i j a a'
        (Stacks.Immersion.toShHom_square ca) =
      Stacks.Immersion.immersionConormalSheafMap i j a b'
        (Stacks.Immersion.toShHom_square cb))
    {c' : X' ⟶ Y'} (cc : i ≫ c' = a ≫ j) (V : Y'.Opens) (s : Γ(Y', V)) :
    derivationSectionι hi q cc (differenceDerivationTheta q hi hq ca cb hC) V
        ((j.app V).hom s) =
      conormalSectionι hi cc V ((liftDifferenceDerivation hq ca cb).d (X := op V) s) := by
  refine (derivationSectionι_homEquiv_symm q hi cc (differenceDerivationHom q hi hq ca cb hC) V
    ((j.app V).hom s)).trans (congrArg (conormalSectionι hi cc V) ?_)
  exact differenceDerivation_d_app q hi hq ca cb hC V s

/-- **The difference of two lifts is the action of a derivation datum**,
[Stacks Project, Tag 0CK1] read from right to left: for two lifts `a'`, `b'` of the same `a`
whose induced maps of conormal sheaves agree, `b'` is `θ ⬝ a'` for
`θ = Stacks.Thickenings.differenceDerivationTheta` attached to the pair `(b', a')`.

This is the factorization of [Stacks Project, Tag 04FG] rewritten in the comorphism form
`Stacks.Thickenings.IsDerivationAction`: the two sides are compared over the open
`(a')⁻¹V ⊓ (b')⁻¹V`, which is `(b')⁻¹V` because the two lifts have the same underlying map. -/
theorem isDerivationAction_differenceDerivationTheta (hi : i.ker ^ 2 = ⊥)
    (hq : b' ≫ q = a' ≫ q) (ca : i ≫ a' = a ≫ j) (cb : i ≫ b' = a ≫ j)
    (hC : Stacks.Immersion.immersionConormalSheafMap i j a a'
        (Stacks.Immersion.toShHom_square ca) =
      Stacks.Immersion.immersionConormalSheafMap i j a b'
        (Stacks.Immersion.toShHom_square cb)) :
    IsDerivationAction hi q ca cb
      (differenceDerivationTheta q hi hq.symm cb ca hC.symm) := by
  intro V s
  have hLa : liftPairOpen b' a' V ≤ a' ⁻¹ᵁ V := inf_le_left
  have hLb : liftPairOpen b' a' V ≤ b' ⁻¹ᵁ V := inf_le_right
  have hpre : b' ⁻¹ᵁ V = a' ⁻¹ᵁ V :=
    preimage_eq_of_comp_eq (surjective_of_ker_sq_eq_bot hi) (cb.trans ca.symm) V
  have hbL : b' ⁻¹ᵁ V ≤ liftPairOpen b' a' V := le_inf hpre.le le_rfl
  refine presheaf_map_injective (homOfLE hLb).op (homOfLE hbL).op ?_
  have htr : ∀ t : Γ(X', a' ⁻¹ᵁ V),
      (X'.presheaf.map (homOfLE hLb).op).hom
          ((X'.presheaf.map (eqToHom hpre).op).hom t) =
        (X'.presheaf.map (homOfLE hLa).op).hom t := fun t ↦
    presheaf_map_map (eqToHom hpre).op (homOfLE hLb).op (homOfLE hLa).op t
  rw [htr, map_add,
    derivationSectionι_differenceDerivationTheta q hi hq.symm cb ca hC.symm ca V s,
    map_conormalSectionι hi ca V hLa (preimage_liftPairOpen cb ca V)
      ((liftDifferenceDerivation hq.symm cb ca).d (X := op V) s)]
  refine Eq.trans (congrArg
    (fun z ↦ (X'.presheaf.map (homOfLE hLa).op).hom ((a'.app V).hom s) + z)
    (firstOrderImmersionConormalSheafι_liftDifferenceDerivation_d hi hq.symm cb ca V s)) ?_
  change (X'.presheaf.map (homOfLE hLa).op).hom ((a'.app V).hom s) +
      ((b'.appLE V (liftPairOpen b' a' V) hLb).hom s -
        (a'.appLE V (liftPairOpen b' a' V) hLa).hom s) =
    (X'.presheaf.map (homOfLE hLb).op).hom ((b'.app V).hom s)
  rw [Scheme.Hom.appLE, Scheme.Hom.appLE, CommRingCat.comp_apply, CommRingCat.comp_apply]
  abel

/-- **Two lifts of the same morphism inducing the same map of conormal sheaves differ by a
derivation datum.** This is the converse direction of the "simple transitivity" half of
[Stacks Project, Tag 04FJ]: every `b'` as in [Stacks Project, Tag 04FG] is `θ ⬝ a'` for some
`θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}`.

The existence half, that every `θ` does act, is
`Stacks.Thickenings.existsUnique_isDerivationAction`. -/
theorem exists_isDerivationAction (hi : i.ker ^ 2 = ⊥) (hq : b' ≫ q = a' ≫ q)
    (ca : i ≫ a' = a ≫ j) (cb : i ≫ b' = a ≫ j)
    (hC : Stacks.Immersion.immersionConormalSheafMap i j a a'
        (Stacks.Immersion.toShHom_square ca) =
      Stacks.Immersion.immersionConormalSheafMap i j a b'
        (Stacks.Immersion.toShHom_square cb)) :
    ∃ θ : (Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials (j ≫ q)) ⟶
      Stacks.Conormal.conormalSheaf i, IsDerivationAction hi q ca cb θ :=
  ⟨differenceDerivationTheta q hi hq.symm cb ca hC.symm,
    isDerivationAction_differenceDerivationTheta q hi hq ca cb hC⟩

end Difference

end Stacks.Thickenings

end
