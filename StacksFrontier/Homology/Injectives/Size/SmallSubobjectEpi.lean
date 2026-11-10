module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Small subobjects mapping onto a quotient

Let `C` be a Grothendieck abelian category with generator `U = separator C`, let the size `|M|`
of an object `M` be the cardinality of its set of subobjects, and let `c(κ) = |⨁_{α ∈ κ} U|`.
For every epimorphism `π : M ⟶ N` there is a subobject `M' ⊆ M` such that the composite
`M' ⟶ M ⟶ N` is an epimorphism and `|M'| ≤ c(|N|)`.

Sizes are cardinals in `Cardinal.{max u v}`, and `C` is assumed Grothendieck abelian for
`max u v`-small index categories, so that coproducts indexed by sets of such cardinality exist.

## Main definitions

* `Stacks.Injectives.SmallSubobjectEpi.size`: the cardinality of `Subobject M`.
* `Stacks.Injectives.SmallSubobjectEpi.cardFn`: the size of the coproduct of `κ` copies of `U`.
* `Stacks.Injectives.SmallSubobjectEpi.subCoproductιMap`: the inclusion of the coproduct over a
  subset of the index set into the coproduct over the whole index set.

## Main results

* `Stacks.Injectives.SmallSubobjectEpi.exists_subobject_epi_size_le`: the statement above.
* `Stacks.Injectives.SmallSubobjectEpi.size_le_of_epi`: an epimorphism `X ⟶ Y` gives
  `|Y| ≤ |X|`.
* `Stacks.Injectives.SmallSubobjectEpi.exists_small_subfamily_epi`: an epimorphism from a
  coproduct of copies of `U` onto `N` restricts to an epimorphism from a sub-coproduct indexed by
  a set of cardinality at most `|N|`.

## References

* [Stacks Project, Tag 079J](https://stacks.math.columbia.edu/tag/079J)
* [Stacks Project, Tag 079C](https://stacks.math.columbia.edu/tag/079C)
-/

namespace Stacks.Injectives.SmallSubobjectEpi

open CategoryTheory CategoryTheory.Limits

universe v u w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{max u v} C]

/-- The *size* `|M|` of an object `M` of a Grothendieck abelian category is the cardinality of
its set of subobjects. The subobjects form a set because the category is locally small and
well-powered. -/
noncomputable def size (M : C) : Cardinal.{max u v} := Cardinal.mk (Subobject M)

/-- The cardinal function `c` attached to a generator `U`: `c κ` is the size of the coproduct of
`κ` copies of `U`, the cardinal `κ` being viewed as the index type `κ.out`. -/
noncomputable def cardFn (U : C) (κ : Cardinal.{max u v}) : Cardinal.{max u v} :=
  size (∐ fun (_ : κ.out) => U)

omit [Abelian C] [IsGrothendieckAbelian.{max u v, v, u} C] in
/-- If `U` is a separator, then for any object `X` the canonical map `∐_{f : U ⟶ X} U ⟶ X`
(`Sigma.desc id`) is an epimorphism. -/
theorem epi_sigmaDesc_of_isSeparator {U : C} (hU : IsSeparator U)
    (X : C) [HasCoproduct (fun (_ : (U ⟶ X)) => U)] :
    Epi (Sigma.desc (fun (f : U ⟶ X) => f)) := by
  rw [IsSeparator] at hU
  constructor
  intro Y f g hfg
  apply hU
  intro G hG h
  rw [ObjectProperty.singleton_iff] at hG
  obtain rfl : U = G := hG
  have hh : h = (Sigma.ι (fun (_ : (U ⟶ X)) => U) h) ≫ Sigma.desc (fun (f : U ⟶ X) => f) := by
    simp
  rw [hh, Category.assoc, hfg, Category.assoc]

/-- The coproduct of copies of `U` indexed by a `max u v`-small type exists. -/
private theorem hasCoproduct_of_small (U : C) (α : Type w) [Small.{max u v} α] :
    HasCoproduct (fun (_ : α) => U) := by
  have : HasCoproduct (fun (_ : Shrink.{max u v} α) => U) := inferInstance
  exact hasCoproduct_of_equiv_of_iso (fun (_ : Shrink.{max u v} α) => U)
    (fun (_ : α) => U) (equivShrink _) (fun _ => Iso.refl U)

/-- The coproduct of copies of `U` indexed by the morphisms `U ⟶ X` exists. -/
theorem hasCoproduct_homFamily (U X : C) : HasCoproduct (fun (_ : (U ⟶ X)) => U) :=
  hasCoproduct_of_small U _

omit [IsGrothendieckAbelian.{max u v, v, u} C] in
/-- If `e` is an epimorphism, then `imageSubobject (e ≫ g) = imageSubobject g`. -/
private theorem imageSubobject_epi_comp {W X Y : C} (e : W ⟶ X) [Epi e] (g : X ⟶ Y) :
    imageSubobject (e ≫ g) = imageSubobject g := by
  have : Mono (image.preComp e g) := by
    have : Mono (image.preComp e g ≫ image.ι g) := by rw [image.preComp_ι]; infer_instance
    exact mono_of_mono _ (image.ι g)
  have hrel : factorThruImage (e ≫ g) ≫ image.preComp e g = e ≫ factorThruImage g := by
    apply (cancel_mono (image.ι g)).mp
    rw [Category.assoc, image.preComp_ι, image.fac, Category.assoc, image.fac]
  have : Epi (image.preComp e g) := by
    have : Epi (factorThruImage (e ≫ g) ≫ image.preComp e g) := by
      rw [hrel]; exact epi_comp e (factorThruImage g)
    exact epi_of_epi (factorThruImage (e ≫ g)) (image.preComp e g)
  have : IsIso (image.preComp e g) := isIso_of_mono_of_epi _
  change Subobject.mk (image.ι (e ≫ g)) = Subobject.mk (image.ι g)
  exact Subobject.mk_eq_mk_of_comm (image.ι (e ≫ g)) (image.ι g)
    (asIso (image.preComp e g)) (image.preComp_ι e g)

omit [IsGrothendieckAbelian.{max u v, v, u} C] in
/-- The image of a subobject's (mono) arrow is the subobject itself. -/
private theorem imageSubobject_arrow_eq {Y : C} (b : Subobject Y) :
    imageSubobject b.arrow = b := by
  rw [imageSubobject_mono b.arrow, Subobject.mk_arrow]

omit [IsGrothendieckAbelian.{max u v, v, u} C] in
/-- For an epimorphism `f`, the image of the composite of the pullback of `b` along `f` with `f`
is `b`. -/
private theorem pullback_recover {X Y : C} (f : X ⟶ Y) [Epi f] (b : Subobject Y) :
    imageSubobject (((Subobject.pullback f).obj b).arrow ≫ f) = b := by
  have : Epi (pullback.fst b.arrow f) := Abelian.epi_pullback_of_epi_g b.arrow f
  rw [Subobject.pullback_obj f b,
    ← Subobject.underlyingIso_hom_comp_eq_mk (pullback.snd b.arrow f), Category.assoc,
    imageSubobject_epi_comp (Subobject.underlyingIso (pullback.snd b.arrow f)).hom
      (pullback.snd b.arrow f ≫ f), ← pullback.condition,
    imageSubobject_epi_comp (pullback.fst b.arrow f) b.arrow, imageSubobject_arrow_eq]

omit [IsGrothendieckAbelian.{max u v, v, u} C] in
/-- If `f : X ⟶ Y` is an epimorphism, then `size Y ≤ size X`. -/
theorem size_le_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : size Y ≤ size X :=
  Cardinal.mk_le_of_injective (f := (Subobject.pullback f).obj) fun b₁ b₂ h => by
    rw [← pullback_recover f b₁, h, pullback_recover]

/-- The canonical inclusion of a sub-coproduct: from the coproduct over a subset `S ⊆ ι`
into the coproduct over all of `ι`, sending the `s`-th summand to the `s.val`-th summand. -/
noncomputable def subCoproductιMap {ι : Type w} (U : C) (S : Set ι)
    [HasCoproduct (fun (_ : ι) => U)] [HasCoproduct (fun (_ : S) => U)] :
    (∐ fun (_ : S) => U) ⟶ (∐ fun (_ : ι) => U) :=
  Sigma.desc (fun s => Sigma.ι (fun (_ : ι) => U) s.val)

omit [Abelian C] [IsGrothendieckAbelian.{max u v, v, u} C] in
/-- If `i : A ⟶ B` is a monomorphism, then `size A ≤ size B`. -/
private theorem size_le_of_mono {A B : C} (i : A ⟶ B) [Mono i] : size A ≤ size B :=
  Cardinal.mk_le_of_injective (Subobject.map_obj_injective i)

omit [IsGrothendieckAbelian.{max u v, v, u} C] in
/-- For an injection `f : ι → J`, the map `∐_ι U ⟶ ∐_J U` sending the `a`-th summand to the
`f a`-th summand is a monomorphism. -/
private theorem mono_sigmaDesc_ι {U : C} {ι : Type w} {J : Type w'} (f : ι → J)
    (hf : Function.Injective f)
    [HasCoproduct (fun (_ : ι) => U)] [HasCoproduct (fun (_ : J) => U)] :
    Mono (Sigma.desc (fun a => Sigma.ι (fun (_ : J) => U) (f a))) := by
  classical
  have : IsSplitMono (Sigma.desc (fun a => Sigma.ι (fun (_ : J) => U) (f a))) := by
    refine ⟨⟨Sigma.desc (fun j => if h : ∃ a, f a = j then
      Sigma.ι (fun (_ : ι) => U) h.choose else 0), ?_⟩⟩
    apply Sigma.hom_ext
    intro a
    rw [← Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
    have hex : ∃ b, f b = f a := ⟨a, rfl⟩
    rw [dite_eq_left hex, Category.comp_id]
    congr 1
    exact hf hex.choose_spec
  infer_instance

/-- If `ι` has cardinality at most `size N` (after lifting universes), then the size of the
coproduct of `ι` copies of `U` is at most `cardFn U (size N)`. -/
theorem size_coproduct_le_cardFn (U N : C) (ι : Type w)
    [HasCoproduct (fun (_ : ι) => U)]
    (hι : Cardinal.lift.{max u v} (Cardinal.mk ι) ≤ Cardinal.lift.{w} (size N)) :
    size (∐ fun (_ : ι) => U) ≤ cardFn U (size N) := by
  rw [← Cardinal.mk_out (size N)] at hι
  obtain ⟨f⟩ := Cardinal.lift_mk_le'.mp hι
  have : Mono (Sigma.desc (fun a => Sigma.ι (fun (_ : (size N).out) => U) (f a))) :=
    mono_sigmaDesc_ι (U := U) (J := (size N).out) f f.injective
  exact size_le_of_mono
    (Sigma.desc (fun a => Sigma.ι (fun (_ : (size N).out) => U) (f a)))

omit [IsGrothendieckAbelian.{max u v, v, u} C] in
/-- A morphism is an epimorphism if and only if its image is `⊤`. -/
private theorem epi_iff_image_eq_top {X N : C} (h : X ⟶ N) :
    Epi h ↔ imageSubobject h = ⊤ := by
  constructor
  · intro _
    rw [← Subobject.isIso_arrow_iff_eq_top]
    have : Epi (imageSubobject h).arrow := by
      have he : Epi (factorThruImageSubobject h ≫ (imageSubobject h).arrow) := by
        rw [imageSubobject_arrow_comp]; infer_instance
      exact epi_of_epi (factorThruImageSubobject h) _
    exact isIso_of_mono_of_epi _
  · intro hh
    have := (Subobject.isIso_arrow_iff_eq_top _).mpr hh
    rw [← imageSubobject_arrow_comp h]
    exact epi_comp _ _

/-- The image of a morphism out of a coproduct is the supremum of the images of its
components. -/
private theorem image_sigma_eq_iSup {ι : Type w} {U N : C} [HasCoproduct (fun (_ : ι) => U)]
    (g : (∐ fun (_ : ι) => U) ⟶ N) :
    imageSubobject g = ⨆ i, imageSubobject (Sigma.ι (fun (_ : ι) => U) i ≫ g) := by
  refine le_antisymm ?_ (iSup_le fun i => imageSubobject_comp_le _ _)
  set T : Subobject N := ⨆ i, imageSubobject (Sigma.ι (fun (_ : ι) => U) i ≫ g)
  have hfac (i : ι) : T.Factors (Sigma.ι (fun (_ : ι) => U) i ≫ g) :=
    Subobject.factors_of_le _
      (le_iSup (fun i => imageSubobject (Sigma.ι (fun (_ : ι) => U) i ≫ g)) i)
      (by simpa using imageSubobject_factors_comp_self (Sigma.ι (fun (_ : ι) => U) i ≫ g) (𝟙 _))
  exact imageSubobject_le g (Sigma.desc fun i => T.factorThru _ (hfac i))
    (Sigma.hom_ext _ _ fun i => by simp)

/-- Given an epimorphism `g` from a coproduct of copies of `U` onto `N`, there is a subset `S` of
the index set with `#S ≤ size N` (after lifting universes) such that the restriction of `g` to
the coproduct over `S` is still an epimorphism. -/
theorem exists_small_subfamily_epi {ι : Type w} (U N : C)
    [HasCoproduct (fun (_ : ι) => U)]
    (g : (∐ fun (_ : ι) => U) ⟶ N) [Epi g] :
    ∃ (S : Set ι) (_ : HasCoproduct (fun (_ : S) => U)),
      Cardinal.lift.{max u v} (Cardinal.mk S) ≤ Cardinal.lift.{w} (size N) ∧
      Epi (subCoproductιMap U S ≫ g) := by
  set φ : ι → Subobject N := fun i => imageSubobject (Sigma.ι (fun (_ : ι) => U) i ≫ g) with hφ
  set T : Set (Subobject N) := Set.range φ
  have hpre : ∀ t : T, ∃ i : ι, φ i = t.val := fun t => t.2
  choose j hj using hpre
  set S : Set ι := Set.range j
  have hsup_top : (⨆ i, φ i) = ⊤ := by
    rw [hφ, ← image_sigma_eq_iSup g]
    exact (epi_iff_image_eq_top g).mp inferInstance
  have hsec : ∀ s : S, ∃ t : T, j t = s.val := by
    rintro ⟨x, t, rfl⟩; exact ⟨t, rfl⟩
  choose ts hts using hsec
  have hinj : Function.Injective (fun s : S => (ts s).val) := fun s s' hss =>
    Subtype.ext (by rw [← hts s, ← hts s', Subtype.ext hss])
  have hcard : Cardinal.lift.{max u v} (Cardinal.mk S) ≤ Cardinal.lift.{w} (size N) := by
    rw [size, Cardinal.lift_mk_le']
    exact ⟨⟨fun s => (ts s).val, hinj⟩⟩
  have hsmall : Small.{max u v} (S : Type w) := by
    obtain ⟨f⟩ := Cardinal.lift_mk_le'.mp hcard
    exact small_of_injective f.injective
  have hSc : HasCoproduct (fun (_ : S) => U) := hasCoproduct_of_small U S
  refine ⟨S, hSc, hcard, ?_⟩
  rw [epi_iff_image_eq_top, image_sigma_eq_iSup (subCoproductιMap U S ≫ g)]
  have hcomp : ∀ s : S, imageSubobject (Sigma.ι (fun (_ : S) => U) s ≫ (subCoproductιMap U S ≫ g))
      = φ s.val := by
    intro s
    congr 1
    rw [subCoproductιMap, ← Category.assoc, Sigma.ι_comp_desc]
  rw [iSup_congr hcomp]
  refine le_antisymm le_top ?_
  rw [← hsup_top]
  refine iSup_le fun i => ?_
  calc φ i = φ (j ⟨φ i, i, rfl⟩) := (hj ⟨φ i, i, rfl⟩).symm
    _ ≤ ⨆ s : S, φ s.val := le_iSup (fun s : S => φ s.val) ⟨j ⟨φ i, i, rfl⟩, _, rfl⟩

/-- Let `C` be a Grothendieck abelian category with generator `separator C`. For every
epimorphism `π : M ⟶ N` there is a subobject `M' ⊆ M` such that `M'.arrow ≫ π` is an
epimorphism and `size M' ≤ cardFn (separator C) (size N)`. -/
@[stacks 079J]
theorem exists_subobject_epi_size_le
    (M N : C) (π : M ⟶ N) [Epi π] :
    ∃ M' : Subobject M,
      Epi (M'.arrow ≫ π) ∧
      size ((M' : C)) ≤ cardFn (separator C) (size N) := by
  set U := separator C
  have : HasCoproduct (fun (_ : (U ⟶ M)) => U) := hasCoproduct_homFamily U M
  set e : (∐ fun (_ : (U ⟶ M)) => U) ⟶ M := Sigma.desc (fun f => f)
  have : Epi e := epi_sigmaDesc_of_isSeparator (isSeparator_separator C) M
  obtain ⟨S, hSc, hScard, hSepi⟩ := exists_small_subfamily_epi (ι := (U ⟶ M)) U N (e ≫ π)
  set q : (∐ fun (_ : S) => U) ⟶ M := subCoproductιMap U S ≫ e with hq
  refine ⟨imageSubobject q, ?_, ?_⟩
  · have : Epi (factorThruImageSubobject q ≫ (imageSubobject q).arrow ≫ π) := by
      rwa [← Category.assoc, imageSubobject_arrow_comp, hq, Category.assoc]
    exact epi_of_epi (factorThruImageSubobject q) _
  · exact (size_le_of_epi (factorThruImageSubobject q)).trans
      (size_coproduct_le_cardFn U N S hScard)

end Stacks.Injectives.SmallSubobjectEpi
