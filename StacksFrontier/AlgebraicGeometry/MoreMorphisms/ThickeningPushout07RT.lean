module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGlobal

/-!
# Pushouts along a thickening and an affine morphism: the map from `Y` and the structure sheaf

Let `i : X ⟶ X'` be a thickening of schemes and `f : X ⟶ Y` an affine morphism.
[Stacks Project, Tag 07RT] makes four assertions about the pushout `Y' = Y ⨿_X X'`: that it
exists, that `Y ⟶ Y'` is again a thickening, that the pushout square is simultaneously
cartesian, and that `𝒪_{Y'}` is the fibre product `𝒪_Y ×_{f_*𝒪_X} f'_*𝒪_{X'}`.

`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGlobal` proves the first and the
third, each granted [Stacks Project, Tag 06AD] — *a thickening of an affine scheme is affine* —
as an explicit universally quantified hypothesis `H`.  This file proves the remaining two, the
second and the fourth, with the same hypothesis in the same form, so that the four statements
compose.

## Main results

* `Stacks.Pushout.isPullback_app_of_isPushout_forgetToLocallyRingedSpace` is the fourth
  assertion of Tag 07RT for an arbitrary scheme carrying the pushout square: over every open of
  the apex the square of rings of sections is cartesian.  It needs neither `H` nor any
  hypothesis on `i` and `f`, only that the square be cocartesian one layer down, in locally
  ringed spaces.
* `Stacks.Pushout.surjective_of_isPushout_base_of_isThickening`: the map from `Y` into such a
  pushout is surjective on points.
* `Stacks.Pushout.isClosedImmersion_morphismRestrict_of_isPushout`: over an open of the apex
  with affine preimages, the map from `Y` restricts to a closed immersion, and that open is
  affine.
* `Stacks.Pushout.isThickening_of_isPushout_forgetToLocallyRingedSpace`: the two previous
  results assembled, for an arbitrary scheme carrying the pushout square: the map from `Y` is a
  thickening.
* `Stacks.Pushout.pushout_inr_isThickening` and
  `Stacks.Pushout.pushout_structureSheaf_isPullback` are the second and fourth assertions of
  Tag 07RT for Mathlib's canonical pushout, granted Tag 06AD.

## Implementation notes

**The fourth assertion is not proved again.**  For a pushout square of presheafed spaces over
`CommRingCat` it is already `Stacks.Pushout.isPullback_app_of_isPushout_right`, proved in
`StacksFrontier.AlgebraicGeometry.Pushout.SectionsComparison` by computing the sections of the
colimit.  All that is needed here is to carry a cocartesian square of *locally ringed* spaces
down to presheafed spaces along `Stacks.Pushout.lrsToPresheafedSpace`, which is exactly how
`Stacks.Pushout.exists_affineChart_of_isPushout_of_isClosedImmersion` already uses that lemma,
and to recognise the component of a morphism of presheafed spaces at an open as
`AlgebraicGeometry.Scheme.Hom.app`, which holds by definition.  This is why the statement
carries no hypothesis on `i` or `f`: the cocartesian square of locally ringed spaces is all of
the input.

**The second assertion splits along the two halves of being a thickening.**  Surjectivity is
global and needs no charts: a thickening is surjective on points, so in the pushout of
`Y ← X → X'` every point coming from `X'` already comes from `X`, hence from `Y`.  This is the
argument that
`Stacks.Pushout.exists_opens_isAffineOpen_preimage_of_isThickening` runs internally to find a
point of `Y` over a given point of the apex; it is isolated here as
`Stacks.Pushout.surjective_of_isPushout_base_of_isThickening`.

Being a closed immersion, by contrast, is proved from the affine charts, since it is
Zariski-local at the target: over an open `W` of the apex with affine preimages, the chart of
`Stacks.Pushout.exists_affineChart_of_isPushout_of_isClosedImmersion` presents the restriction
of the map from `Y` as a closed immersion followed by an isomorphism onto `W`.  Note that the
chart lemma's own `IsClosedImmersion` conclusion is what is used; the scheme-level chart
`Stacks.Pushout.exists_chart_of_isPushout_forgetToLocallyRingedSpace` discards it, which is why
`Stacks.Pushout.isClosedImmersion_morphismRestrict_of_isPushout` goes back to the
locally-ringed-space chart.  Only `IsClosedImmersion i` is needed for it: the surjectivity half
of being a thickening enters nowhere.

**The hypothesis `H`.**  It is [Stacks Project, Tag 06AD], exactly as in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGlobal`, and it enters at a single
point: that file's `Stacks.Pushout.isAffineOpen_opensCongr_preimage_of_isThickening`, used to see
that the open of `X'` matching `f ⁻¹ᵁ V` is affine.  Nothing is assumed by it.  Tag 06AD is a
theorem, `Stacks.Thickenings.isAffine_of_isThickening` in
`StacksFrontier.AlgebraicGeometry.Thickenings.Affine`, proved through finite surjective morphisms
rather than through the cohomological route of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffine`;
`Stacks.Thickenings.forall_isAffine_of_isThickening` is the universally quantified form that `H`
wants.  So the two assertions below hold for every instance of Tag 07RT.  They are restated with
`H` discharged, for an arbitrary thickening, in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutUnconditional`, which is where all
four assertions of the tag are stated with no hypothesis beyond its geometric data; for a
thickening of *finite* order,
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutFiniteOrder` discharges `H` by the
adic filtration instead.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Pushout

open Stacks.Thickenings

/-! ### The structure sheaf of a pushout -/

/-- **Stacks Project, Tag 07RT, fourth assertion, for an arbitrary scheme carrying the pushout
square.**  Let `i`, `j`, `A`, `B` be a square of schemes which is cocartesian in locally ringed
spaces.  Over every open `U` of the apex the square of rings of sections is cartesian:
`Γ(Q, U) = Γ(Y, B ⁻¹ᵁ U) ×_{Γ(Z, _)} Γ(X, A ⁻¹ᵁ U)`.

The transport `eqToHom` identifies the two preimages of `U` in `Z`, which agree because the
square commutes; `hX` is that equality, taken as a hypothesis so that the statement can be used
with either of its two proofs.

This is `Stacks.Pushout.isPullback_app_of_isPushout_right` for presheafed spaces, carried along
`Stacks.Pushout.lrsToPresheafedSpace`. -/
theorem isPullback_app_of_isPushout_forgetToLocallyRingedSpace {X Y Z Q : Scheme.{u}}
    {i : Z ⟶ X} {j : Z ⟶ Y} {A : X ⟶ Q} {B : Y ⟶ Q}
    (h : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map j) (Scheme.forgetToLocallyRingedSpace.map A)
      (Scheme.forgetToLocallyRingedSpace.map B))
    (U : Q.Opens) (hX : i ⁻¹ᵁ (A ⁻¹ᵁ U) = j ⁻¹ᵁ (B ⁻¹ᵁ U)) :
    IsPullback (B.app U) (A.app U) (j.app (B ⁻¹ᵁ U))
      (i.app (A ⁻¹ᵁ U) ≫ eqToHom (congrArg (fun V : Z.Opens ↦ Γ(Z, V)) hX)) := by
  have H := isPullback_app_of_isPushout_right (h.map lrsToPresheafedSpace) U (congrArg op hX)
  rwa [eqToHom_map] at H

/-! ### The map from `Y` is a thickening -/

variable {X X' Y : Scheme.{u}}

/-- **The map from `Y` into a pushout along a thickening is surjective on points.**  A thickening
is surjective, so a point of the apex coming from `X'` already comes from `X`, hence from `Y`;
and the apex is covered by the images of `X'` and `Y` because its space is a quotient of their
sum. -/
theorem surjective_of_isPushout_base_of_isThickening {i : X ⟶ X'} (hi : IsThickening i)
    (f : X ⟶ Y) {P : LocallyRingedSpace.{u}}
    {a : Scheme.forgetToLocallyRingedSpace.obj X' ⟶ P}
    {b : Scheme.forgetToLocallyRingedSpace.obj Y ⟶ P}
    (hbase : IsPushout (Scheme.forgetToLocallyRingedSpace.map i).base
      (Scheme.forgetToLocallyRingedSpace.map f).base a.base b.base) :
    Function.Surjective b.base := by
  have := hi.1
  have hinj : Function.Injective (Scheme.forgetToLocallyRingedSpace.map i).base :=
    i.isClosedEmbedding.injective
  have hcross : ∀ z : X, a.base ((Scheme.forgetToLocallyRingedSpace.map i).base z) =
      b.base ((Scheme.forgetToLocallyRingedSpace.map f).base z) := fun z ↦
    (ConcreteCategory.comp_apply _ _ z).symm.trans
      ((ConcreteCategory.congr_hom hbase.w z).trans (ConcreteCategory.comp_apply _ _ z))
  intro p
  obtain ⟨s, hs⟩ := (isQuotientMap_sum_of_isPushout _ _ hinj hbase).surjective p
  rcases s with x | y
  · obtain ⟨z, hz⟩ := hi.2 x
    exact ⟨(Scheme.forgetToLocallyRingedSpace.map f).base z,
      ((hcross z).symm.trans (congrArg a.base hz)).trans hs⟩
  · exact ⟨y, hs⟩

/-- **Over an open of the apex with affine preimages, the map from `Y` is a closed immersion.**
The chart of `Stacks.Pushout.exists_affineChart_of_isPushout_of_isClosedImmersion` presents the
restriction `B ∣_ W` as the closed immersion from `V = B ⁻¹ᵁ W` into the affine model followed by
an isomorphism of that model onto `W`; in particular `W` is affine.

Only `IsClosedImmersion i` is used, exactly as in the chart lemma. -/
theorem isClosedImmersion_morphismRestrict_of_isPushout {X Y Z Q : Scheme.{u}}
    (i : Z ⟶ X) (j : Z ⟶ Y) (A : X ⟶ Q) (B : Y ⟶ Q) [IsClosedImmersion i]
    (h : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map j) (Scheme.forgetToLocallyRingedSpace.map A)
      (Scheme.forgetToLocallyRingedSpace.map B))
    (hw : i ≫ A = j ≫ B) (W : Q.Opens)
    (hU : IsAffineOpen (A ⁻¹ᵁ W)) (hV : IsAffineOpen (B ⁻¹ᵁ W)) :
    IsClosedImmersion (B ∣_ W) ∧ IsAffine W.toScheme := by
  obtain ⟨R, α, β, g, hβ, -, -, hgb, hgoi, hgr⟩ :=
    exists_affineChart_of_isPushout_of_isClosedImmersion i j h W (A ⁻¹ᵁ W) (B ⁻¹ᵁ W) rfl rfl
      hU hV (preimage_preimage_eq_of_comm i j A B hw W)
  obtain ⟨gS, hgS⟩ : ∃ gS : Spec R ⟶ Q, Scheme.forgetToLocallyRingedSpace.map gS = g :=
    ⟨Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimage g,
      Scheme.fullyFaithfulForgetToLocallyRingedSpace.map_preimage _⟩
  have hoi : IsOpenImmersion gS := by rw [← hgS] at hgoi; exact hgoi
  have hrange : Set.range gS.base = Set.range (W.ι).base :=
    (congrArg (fun k : Scheme.forgetToLocallyRingedSpace.obj (Spec R) ⟶
      Scheme.forgetToLocallyRingedSpace.obj Q ↦ Set.range k.base) hgS).trans
      (hgr.trans (Scheme.Opens.range_ι W).symm)
  obtain ⟨e, he⟩ : ∃ e : Spec R ≅ W.toScheme, e.hom ≫ W.ι = gS :=
    ⟨IsOpenImmersion.isoOfRangeEq gS W.ι hrange,
      IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩
  have hβe : β ≫ e.hom = B ∣_ W := by
    rw [← cancel_mono W.ι, Category.assoc, he, morphismRestrict_ι]
    exact Scheme.forgetToLocallyRingedSpace.map_injective
      (by rw [Scheme.forgetToLocallyRingedSpace.map_comp,
        Scheme.forgetToLocallyRingedSpace.map_comp, hgS, hgb])
  refine ⟨?_, .of_isIso e.inv⟩
  rw [← hβe]
  exact inferInstanceAs (IsClosedImmersion (β ≫ e.hom))

/-- **Stacks Project, Tag 07RT, second assertion, for an arbitrary scheme carrying the pushout
square.**  If the square of `i : X ⟶ X'` a thickening, `f : X ⟶ Y`, `A` and `B` is cocartesian in
locally ringed spaces and every point of the apex lies in an open with affine preimages, then
`B : Y ⟶ Q` is a thickening.

Surjectivity is `Stacks.Pushout.surjective_of_isPushout_base_of_isThickening`; being a closed
immersion is Zariski-local at the target, and over each of the opens furnished by the chart
hypothesis it is
`Stacks.Pushout.isClosedImmersion_morphismRestrict_of_isPushout`. -/
theorem isThickening_of_isPushout_forgetToLocallyRingedSpace {i : X ⟶ X'} (hi : IsThickening i)
    (f : X ⟶ Y) {Q : Scheme.{u}} {A : X' ⟶ Q} {B : Y ⟶ Q}
    (h : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map f) (Scheme.forgetToLocallyRingedSpace.map A)
      (Scheme.forgetToLocallyRingedSpace.map B))
    (hch : ∀ p : Q, ∃ W : Q.Opens, p ∈ W ∧ IsAffineOpen (A ⁻¹ᵁ W) ∧ IsAffineOpen (B ⁻¹ᵁ W)) :
    IsThickening B := by
  have := hi.1
  have hw : i ≫ A = f ≫ B :=
    (IsPushout.of_map_of_faithful Scheme.forgetToLocallyRingedSpace h).w
  choose W hpW hWA hWB using hch
  refine ⟨IsZariskiLocalAtTarget.of_iSup_eq_top W ?_ fun p ↦
    (isClosedImmersion_morphismRestrict_of_isPushout i f A B h hw (W p) (hWA p) (hWB p)).1,
    surjective_of_isPushout_base_of_isThickening hi f (isPushout_base_of_isPushout h)⟩
  refine top_le_iff.mp fun p _ ↦ ?_
  exact Opens.mem_iSup.mpr ⟨p, hpW p⟩

/-! ### The two assertions for Mathlib's canonical pushout, granted Tag 06AD -/

/-- **The pushout of a thickening and an affine morphism, with its cocartesian square one layer
down.**  This is the construction of
`Stacks.Pushout.exists_isPushout_isPullback_of_isThickening`, retaining the cocartesian square
of *locally ringed* spaces and the chart condition instead of the two assertions read off them;
those are what the second and fourth assertions of [Stacks Project, Tag 07RT] are proved
from. -/
theorem exists_isPushout_forgetToLocallyRingedSpace_of_isThickening
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] :
    ∃ (Q : Scheme.{u}) (A : X' ⟶ Q) (B : Y ⟶ Q),
      IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
        (Scheme.forgetToLocallyRingedSpace.map f)
        (Scheme.forgetToLocallyRingedSpace.map A)
        (Scheme.forgetToLocallyRingedSpace.map B) ∧
      ∀ p : Q, ∃ W : Q.Opens, p ∈ W ∧ IsAffineOpen (A ⁻¹ᵁ W) ∧ IsAffineOpen (B ⁻¹ᵁ W) := by
  have := hi.1
  have hcol : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map f)
      (colimit.ι (span (Scheme.forgetToLocallyRingedSpace.map i)
        (Scheme.forgetToLocallyRingedSpace.map f)) WalkingSpan.left)
      (colimit.ι (span (Scheme.forgetToLocallyRingedSpace.map i)
        (Scheme.forgetToLocallyRingedSpace.map f)) WalkingSpan.right) :=
    IsPushout.of_isColimit_cocone (colimit.isColimit
      (span (Scheme.forgetToLocallyRingedSpace.map i)
        (Scheme.forgetToLocallyRingedSpace.map f)))
  exact exists_scheme_isPushout_of_isPushout i f hcol
    (exists_opens_isAffineOpen_preimage_of_isThickening H hi f
      (isPushout_base_of_isPushout hcol))

/-- **Stacks Project, Tag 07RT, second assertion, granted Tag 06AD.**  The map from `Y` into the
pushout of a thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` is again a thickening,
stated for Mathlib's canonical pushout. -/
theorem pushout_inr_isThickening
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] [HasPushout i f] :
    IsThickening (pushout.inr i f) := by
  obtain ⟨Q, A, B, hcol, hch⟩ :=
    exists_isPushout_forgetToLocallyRingedSpace_of_isThickening H i f hi
  have hpo : IsPushout i f A B :=
    IsPushout.of_map_of_faithful Scheme.forgetToLocallyRingedSpace hcol
  obtain ⟨hci, hsurj⟩ := isThickening_of_isPushout_forgetToLocallyRingedSpace hi f hcol hch
  have : Surjective B := ⟨hsurj⟩
  rw [← hpo.inr_isoPushout_hom]
  exact ⟨inferInstance, (B ≫ hpo.isoPushout.hom).surjective⟩

/-- **Stacks Project, Tag 07RT, fourth assertion, granted Tag 06AD.**  On every open `U` of the
pushout of a thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y`, the ring of sections is
the fibre product of the rings of sections over the two preimages of `U` in `Y` and `X'` above
the ring of sections over their common preimage in `X`. -/
theorem pushout_structureSheaf_isPullback
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    (U : (pushout i f).Opens) :
    IsPullback ((pushout.inr i f).app U) ((pushout.inl i f).app U)
      (f.app (pushout.inr i f ⁻¹ᵁ U))
      (i.app (pushout.inl i f ⁻¹ᵁ U) ≫ eqToHom (congrArg (fun V : X.Opens ↦ Γ(X, V))
        (congrArg (fun g : X ⟶ pushout i f ↦ g ⁻¹ᵁ U)
          (pushout.condition (f := i) (g := f))))) := by
  obtain ⟨Q, A, B, hcol, -⟩ :=
    exists_isPushout_forgetToLocallyRingedSpace_of_isThickening H i f hi
  have hpo : IsPushout i f A B :=
    IsPushout.of_map_of_faithful Scheme.forgetToLocallyRingedSpace hcol
  have hcol' : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map f)
      (Scheme.forgetToLocallyRingedSpace.map (pushout.inl i f))
      (Scheme.forgetToLocallyRingedSpace.map (pushout.inr i f)) :=
    hcol.of_iso' (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Scheme.forgetToLocallyRingedSpace.mapIso hpo.isoPushout).symm
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by rw [Iso.symm_hom, Functor.mapIso_inv, Iso.refl_hom, Category.id_comp,
        ← Scheme.forgetToLocallyRingedSpace.map_comp, hpo.inl_isoPushout_inv])
      (by rw [Iso.symm_hom, Functor.mapIso_inv, Iso.refl_hom, Category.id_comp,
        ← Scheme.forgetToLocallyRingedSpace.map_comp, hpo.inr_isoPushout_inv])
  exact isPullback_app_of_isPushout_forgetToLocallyRingedSpace hcol' U
    (congrArg (fun g : X ⟶ pushout i f ↦ g ⁻¹ᵁ U) (pushout.condition (f := i) (g := f)))

end Stacks.Pushout

end
