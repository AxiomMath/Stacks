module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Pushout.ColimitSections
public import StacksFrontier.AlgebraicGeometry.Pushout.Gluing

/-!
# Sections of an arbitrary pushout square along a closed immersion and an integral morphism

The pushout `Y ⨿_Z X` of a closed immersion `i : Z ⟶ X` and an integral morphism `j : Z ⟶ Y`
is constructed in `StacksFrontier.AlgebraicGeometry.Pushout.Gluing` as a specific scheme, and its
structure sheaf is identified there as a fibre product of sections.  This file transports that
identification to an *arbitrary* pushout square on `i` and `j`, which is the form in which it
gets used, and draws two consequences: away from the image of `Y` the canonical map from `X` is
an isomorphism, both on sections and as a morphism of schemes.

## Main results

* `AlgebraicGeometry.structureSheaf_isPullback_of_isPushout`: the ring of sections of any
  pushout of `i` and `j` is the fibre product of the rings of sections on `X` and `Y` over the
  one on `Z`.
* `AlgebraicGeometry.fiber_preimage_subset_affine_of_isAffineHom`: an affine map out of `X`
  supplies the affine-neighbourhood condition of
  `AlgebraicGeometry.PushoutAlongClosedImmersionAndIntegralSituation` for free.
* `AlgebraicGeometry.isIso_app_of_isPushout_of_preimage_eq_bot` and
  `AlgebraicGeometry.isIso_morphismRestrict_of_isPushout_of_preimage_eq_bot`: over an open
  disjoint from the image of `Y`, the canonical map from `X` is an isomorphism.
* `AlgebraicGeometry.pushoutInl_isIso_morphismRestrict`: the same for the chosen pushout.

The file also collects the small facts about `AlgebraicGeometry.Scheme.Hom.appLE` which the
pushout files above it share, among them
`AlgebraicGeometry.of_forall_appLE_preimage`, by which a property of morphisms detected on
sections over affine opens is checked on the maps induced over the inverse images of affine
opens along two affine morphisms.

## Implementation notes

An arbitrary pushout square is compared with the chosen one of
`AlgebraicGeometry.pushoutAlongClosedImmersionAndIntegral` through
`CategoryTheory.IsPushout.isoIsPushout`.  The affine-neighbourhood condition of the standing
situation is not a property of `i` and `j` alone, so it is carried as a hypothesis; the base of
the auxiliary situation is taken to be the pushout itself, for which the two commuting triangles
are `rfl` and the square's own commutativity.

## References

* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Small facts about sections of a morphism -/

/-- Composing the sections of a morphism over an open with an equality of opens gives the
restriction map to the open on the other side of the equality. -/
theorem app_comp_eqToHom_eq_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (h : f ⁻¹ᵁ U = V) (e : V ≤ f ⁻¹ᵁ U) :
    f.app U ≫ eqToHom (congrArg (fun W ↦ Γ(X, W)) h) = f.appLE U V e := by
  subst h
  simp [Scheme.Hom.app_eq_appLE]

/-- Equal morphisms of schemes induce equal maps on sections. -/
theorem appLE_eq_appLE_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (ef : V ≤ f ⁻¹ᵁ U) (eg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V ef = g.appLE U V eg := by
  subst h
  rfl

/-- A closed immersion is surjective on sections over an affine open, also after replacing the
inverse image by an equal open. -/
theorem appLE_surjective_of_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens}
    (h : f ⁻¹ᵁ U = V) (e : V ≤ f ⁻¹ᵁ U) :
    Function.Surjective (f.appLE U V e).hom := by
  subst h
  rw [Scheme.Hom.appLE_eq_app]
  exact f.app_surjective _ hU

/-- In a commuting square of schemes, the inverse image of an open contained in the inverse
image of `U` is contained in the inverse image of the inverse image of `U`. -/
theorem preimage_le_preimage_of_comm {X Y A B : Scheme.{u}} {f : X ⟶ Y} {h : A ⟶ B}
    {a : Y ⟶ B} {b : X ⟶ A} (comm : b ≫ h = f ≫ a) {U : B.Opens} {V : A.Opens}
    (e : V ≤ h ⁻¹ᵁ U) : b ⁻¹ᵁ V ≤ f ⁻¹ᵁ (a ⁻¹ᵁ U) := by
  simpa only [← Scheme.Hom.comp_preimage, comm] using b.preimage_mono e

/-- A property of morphisms of schemes which is detected on sections over affine opens holds for
`f` as soon as it holds for the maps on sections induced by `f` over the inverse images of
affine opens along two affine morphisms sitting in a commuting square with `f`. -/
theorem of_forall_appLE_preimage {P : MorphismProperty Scheme.{u}}
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    [HasRingHomProperty P Q]
    (hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q)
    {X Y A B : Scheme.{u}} (f : X ⟶ Y) (h : A ⟶ B) (a : Y ⟶ B) (b : X ⟶ A)
    [IsAffineHom a] [IsAffineHom b] (comm : b ≫ h = f ≫ a)
    (H : ∀ (U : B.Opens) (V : A.Opens), IsAffineOpen U → IsAffineOpen V →
      ∀ e : V ≤ h ⁻¹ᵁ U,
        Q (f.appLE (a ⁻¹ᵁ U) (b ⁻¹ᵁ V) (preimage_le_preimage_of_comm comm e)).hom) :
    P f := by
  rw [HasRingHomProperty.iff_exists_appLE (P := P) hQ]
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show h (b x) ∈ (⊤ : B.Opens) from trivial)
  obtain ⟨V, hV, hxV, e⟩ := exists_isAffineOpen_mem_and_subset (show b x ∈ h ⁻¹ᵁ U from hxU)
  exact ⟨⟨a ⁻¹ᵁ U, hU.preimage a⟩, ⟨b ⁻¹ᵁ V, hV.preimage b⟩, hxV,
    preimage_le_preimage_of_comm comm e, H U V hU hV e⟩

/-- The identification of the sections of a pushout as a fibre product, for an arbitrary
pushout square on a closed immersion `i : Z ⟶ X` and an integral morphism `j : Z ⟶ Y`.  The
affine-neighbourhood condition of
`AlgebraicGeometry.PushoutAlongClosedImmersionAndIntegralSituation` is carried as a hypothesis;
the maps on sections are those of the given square.

This is the content of the last assertion of [Stacks Project, Tag 0E25]. -/
theorem structureSheaf_isPullback_of_isPushout
    {X Y Z P : Scheme.{u}} {i : Z ⟶ X} {j : Z ⟶ Y}
    {a : X ⟶ P} {b : Y ⟶ P} [IsClosedImmersion i] [IsIntegralHom j]
    (h : IsPushout i j a b)
    (hAffine : ∀ y : Y, ∃ V : X.Opens, IsAffineOpen V ∧ ∀ z : Z, j z = y → i z ∈ V)
    (U : P.Opens) :
    let e : i ⁻¹ᵁ (a ⁻¹ᵁ U) = j ⁻¹ᵁ (b ⁻¹ᵁ U) :=
      congrArg (fun f : Z ⟶ P ↦ f ⁻¹ᵁ U) h.w
    IsPullback (b.app U) (a.app U) (j.app (b ⁻¹ᵁ U))
      (i.app (a ⁻¹ᵁ U) ≫ eqToHom (congrArg (fun V ↦ Γ(Z, V)) e)) := by
  let s : PushoutAlongClosedImmersionAndIntegralSituation.{u} :=
    { S := P, X := X, Y := Y, Z := Z
      pX := a, pY := b, pZ := i ≫ a
      i := i, j := j
      i_over := rfl, j_over := h.w.symm
      fiber_preimage_subset_affine := hAffine }
  let hP := (pushoutAlongClosedImmersionAndIntegral s).isPushout
  let e := hP.isoIsPushout X Y h
  have ha : pushoutInl s ≫ e.hom = a := IsPushout.inl_isoIsPushout_hom X Y hP h
  have hb : pushoutInr s ≫ e.hom = b := IsPushout.inr_isoIsPushout_hom X Y hP h
  have hpb := pushoutStructureSheaf_isPullback s (e.hom ⁻¹ᵁ U)
  have hpb' : ∀ hw : i ≫ (pushoutInl s ≫ e.hom) = j ≫ (pushoutInr s ≫ e.hom),
      IsPullback ((pushoutInr s ≫ e.hom).app U) ((pushoutInl s ≫ e.hom).app U)
        (j.app ((pushoutInr s ≫ e.hom) ⁻¹ᵁ U))
        (i.app ((pushoutInl s ≫ e.hom) ⁻¹ᵁ U) ≫
          eqToHom (congrArg (fun V ↦ Γ(Z, V))
            (congrArg (fun f : Z ⟶ P ↦ f ⁻¹ᵁ U) hw))) := by
    intro _
    apply hpb.of_iso' (asIso (e.hom.app U)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp [Scheme.Hom.comp_app]
    · simp [Scheme.Hom.comp_app]
    all_goals simp only [Iso.refl_hom, Category.id_comp]; rfl
  rw [ha, hb] at hpb'
  exact hpb' h.w

/-- An affine morphism out of `X` to a common target supplies the affine-neighbourhood condition
of `AlgebraicGeometry.PushoutAlongClosedImmersionAndIntegralSituation`: pull back an affine
neighbourhood of the image of `y`.

This is the special case of the hypothesis of [Stacks Project, Tag 0ECI] that occurs when the
two morphisms are already given a common affine target. -/
theorem fiber_preimage_subset_affine_of_isAffineHom
    {X Y Z P : Scheme.{u}} {i : Z ⟶ X} {j : Z ⟶ Y}
    {a : X ⟶ P} {b : Y ⟶ P} [IsAffineHom a] (h : CommSq i j a b) :
    ∀ y : Y, ∃ V : X.Opens, IsAffineOpen V ∧ ∀ z : Z, j z = y → i z ∈ V := by
  intro y
  obtain ⟨V, hV, hy, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show b y ∈ (⊤ : P.Opens) from trivial)
  refine ⟨a ⁻¹ᵁ V, hV.preimage a, ?_⟩
  intro z hz
  change a (i z) ∈ V
  rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply, hz]
  exact hy

/-- The sections of a pushout square form a fibre product whenever the canonical map out of `X`
is already known to be affine, with no further hypothesis.

This is [Stacks Project, Tag 0E25] in the shape in which the affine-neighbourhood condition of
[Stacks Project, Tag 0ECI] is automatic. -/
theorem structureSheaf_isPullback_of_isPushout_of_isAffineHom
    {X Y Z P : Scheme.{u}} {i : Z ⟶ X} {j : Z ⟶ Y}
    {a : X ⟶ P} {b : Y ⟶ P} [IsClosedImmersion i] [IsIntegralHom j]
    [IsAffineHom a] (h : IsPushout i j a b) (U : P.Opens) :
    let e : i ⁻¹ᵁ (a ⁻¹ᵁ U) = j ⁻¹ᵁ (b ⁻¹ᵁ U) :=
      congrArg (fun f : Z ⟶ P ↦ f ⁻¹ᵁ U) h.w
    IsPullback (b.app U) (a.app U) (j.app (b ⁻¹ᵁ U))
      (i.app (a ⁻¹ᵁ U) ≫ eqToHom (congrArg (fun V ↦ Γ(Z, V)) e)) :=
  structureSheaf_isPullback_of_isPushout h
    (fiber_preimage_subset_affine_of_isAffineHom h.toCommSq) U

/-- Over an open disjoint from the image of `Y`, the canonical map from `X` to a pushout is an
isomorphism on sections.  This is the local picture of the construction of
[Stacks Project, Tag 0E25]: away from `Y` nothing is glued. -/
theorem isIso_app_of_isPushout_of_preimage_eq_bot
    {X Y Z P : Scheme.{u}} {i : Z ⟶ X} {j : Z ⟶ Y}
    {a : X ⟶ P} {b : Y ⟶ P} [IsClosedImmersion i] [IsIntegralHom j]
    [IsAffineHom a] (h : IsPushout i j a b) (U : P.Opens)
    (hU : b ⁻¹ᵁ U = ⊥) : IsIso (a.app U) := by
  have : Subsingleton Γ(Y, b ⁻¹ᵁ U) := by rw [hU]; infer_instance
  have : Subsingleton Γ(Z, j ⁻¹ᵁ (b ⁻¹ᵁ U)) := by
    rw [hU, Scheme.Hom.preimage_bot]
    infer_instance
  have : IsIso (j.app (b ⁻¹ᵁ U)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩
  exact (structureSheaf_isPullback_of_isPushout_of_isAffineHom h U).isIso_snd_of_isIso

/-- Over an open disjoint from the image of `Y`, the canonical map from `X` to a pushout
restricts to an isomorphism of schemes.  This is the scheme-level form of
`AlgebraicGeometry.isIso_app_of_isPushout_of_preimage_eq_bot`, obtained by testing on affine
opens. -/
theorem isIso_morphismRestrict_of_isPushout_of_preimage_eq_bot
    {X Y Z P : Scheme.{u}} {i : Z ⟶ X} {j : Z ⟶ Y}
    {a : X ⟶ P} {b : Y ⟶ P} [IsClosedImmersion i] [IsIntegralHom j]
    [IsAffineHom a] (h : IsPushout i j a b) (U : P.Opens)
    (hU : b ⁻¹ᵁ U = ⊥) : IsIso (a ∣_ U) :=
  Stacks.Pushout.isIso_morphismRestrict_of_forall_isIso_app a U fun W _ hWU ↦
    isIso_app_of_isPushout_of_preimage_eq_bot h W
      (le_bot_iff.mp ((b.preimage_mono hWU).trans_eq hU))

/-- The chosen pushout of [Stacks Project, Tag 0E25] agrees with `X` over every open disjoint
from the image of `Y`. -/
theorem pushoutInl_isIso_morphismRestrict
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
    (U : (pushoutScheme s).Opens) (hU : pushoutInr s ⁻¹ᵁ U = ⊥) :
    IsIso (pushoutInl s ∣_ U) :=
  isIso_morphismRestrict_of_isPushout_of_preimage_eq_bot
    (pushoutAlongClosedImmersionAndIntegral s).isPushout U hU

/-- Restricting the canonical map from `X` to an open of the pushout of
[Stacks Project, Tag 0E25] uses exactly the original maps on sections, transported along the
corresponding equality of opens. -/
theorem pushoutInl_morphismRestrict_app
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
    (U : (pushoutScheme s).Opens) (V : U.toScheme.Opens) :
    (pushoutInl s ∣_ U).app V = (pushoutInl s).app (U.ι ''ᵁ V) ≫
      s.X.presheaf.map (eqToHom (image_morphismRestrict_preimage (pushoutInl s) U V)).op :=
  morphismRestrict_app _ _ _

end AlgebraicGeometry

end
