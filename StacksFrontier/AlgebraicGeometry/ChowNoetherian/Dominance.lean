module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Scheme-theoretic dominance of a dense chart, and the maps it determines

The Stacks proof of Chow's lemma over a Noetherian base (Tag 0200) glues finitely many proper
charts along a common dense open `U`. Every comparison it makes between two such charts is made
on `U` and then propagated, and the mechanism for propagating it is *scheme-theoretic
dominance*: a morphism `a` with `a.ker = ⊥` is an epimorphism against maps into a scheme that is
separated over the base.

## Main results

* `AlgebraicGeometry.isSchemeTheoreticallyDominant_toImage`: the canonical map to the
  scheme-theoretic image of a quasi-compact morphism is scheme-theoretically dominant.
* `AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_comp_isOpenImmersion`: dominance of
  `a ≫ b` descends to `a` when `b` is an open immersion.
* `AlgebraicGeometry.eq_of_comp_isSchemeTheoreticallyDominant`: two morphisms into a scheme
  separated over `S`, agreeing over `S` and after composition with a scheme-theoretically
  dominant map, are equal.
* `AlgebraicGeometry.isIso_pullbackLift_of_isProper_of_isDominant`: a proper morphism which on a
  dense open chart factors through an open immersion exhausts the whole fibre product.
* `AlgebraicGeometry.surjective_of_isProper_of_dense_section`: a proper morphism admitting a
  section over a dense open is surjective.

## Implementation notes

`eq_of_comp_isSchemeTheoreticallyDominant` is the usual equaliser argument, run in `Over S`: for
`q : X ⟶ S` separated the equaliser inclusion of two maps `Over.mk (f ≫ q) ⟶ Over.mk q` is a
closed immersion (`AlgebraicGeometry.isClosedImmersion_equalizer_ι_left`), the dominant map
factors through it, so its kernel ideal is `⊥` and it is an isomorphism; then cancel it.

`isSchemeTheoreticallyDominant_toImage` is proved from
`AlgebraicGeometry.Scheme.Hom.toImage_app_injective`, by checking the kernel ideal on the
preimages of the affine opens of the target, which cover the image.

## References

* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 01R9](https://stacks.math.columbia.edu/tag/01R9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {X Y Z S : Scheme.{u}}

/-- **The canonical map to the scheme-theoretic image of a quasi-compact morphism is
scheme-theoretically dominant.** -/
theorem isSchemeTheoreticallyDominant_toImage (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  let W : Y.affineOpens → f.image.affineOpens := fun U => ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩
  have hW : ⨆ U, (W U).1 = ⊤ :=
    f.imageι.iSup_preimage_eq_top (iSup_affineOpens_eq_top Y)
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top W hW fun U => ?_
  simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  apply (RingHom.injective_iff_ker_eq_bot (f.toImage.app (W U)).hom).mp
  simpa [W] using f.toImage_app_injective U

/-- **Scheme-theoretic dominance descends along an open immersion.** If `b` is an open immersion
and `a ≫ b` is quasi-compact and scheme-theoretically dominant, then so is `a`: the square
expressing `a` as the pullback of `a ≫ b` along `b` is cartesian, and `b` is flat. -/
theorem IsSchemeTheoreticallyDominant.of_comp_isOpenImmersion (a : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion b] [QuasiCompact (a ≫ b)] [IsSchemeTheoreticallyDominant (a ≫ b)] :
    IsSchemeTheoreticallyDominant a := by
  have H : Set.range (a ≫ b) ⊆ Set.range b := by
    rintro _ ⟨x, rfl⟩
    exact ⟨a x, rfl⟩
  have ht : IsOpenImmersion.lift b (a ≫ b) H = a := (cancel_mono b).mp (by simp)
  exact .of_isPullback (ht ▸ (IsOpenImmersion.isPullback_lift_id (a ≫ b) b H).flip)

/-- **A scheme-theoretically dominant map is an epimorphism against a separated target.** If
`a : T ⟶ V` is scheme-theoretically dominant, `q : X ⟶ S` is separated, and `f g : V ⟶ X` agree
over `S` and after composition with `a`, then `f = g`. -/
theorem eq_of_comp_isSchemeTheoreticallyDominant {T V : Scheme.{u}} (a : T ⟶ V)
    [IsSchemeTheoreticallyDominant a] (f g : V ⟶ X) (q : X ⟶ S) [IsSeparated q]
    (hbase : f ≫ q = g ≫ q) (heq : a ≫ f = a ≫ g) : f = g := by
  let F : Over.mk (f ≫ q) ⟶ Over.mk q := Over.homMk f
  let G : Over.mk (f ≫ q) ⟶ Over.mk q := Over.homMk g hbase.symm
  let e := equalizer.ι F G
  let a' : Over.mk (a ≫ f ≫ q) ⟶ Over.mk (f ≫ q) := Over.homMk a
  let t := equalizer.lift (f := F) (g := G) a' (by ext; exact heq)
  have ht : t.left ≫ e.left = a := by
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have hk : e.left.ker = ⊥ := le_bot_iff.mp <| calc
    e.left.ker ≤ (t.left ≫ e.left).ker := Scheme.Hom.le_ker_comp _ _
    _ = ⊥ := by rw [ht, a.ker_eq_bot]
  have : IsSeparated (Over.mk q).hom := inferInstanceAs (IsSeparated q)
  have : IsClosedImmersion e.left := isClosedImmersion_equalizer_ι_left F G
  have : IsIso e.left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  have : IsIso ((Over.forget S).map e) := this
  have : IsIso e := isIso_of_reflects_iso e (Over.forget S)
  exact congrArg Over.Hom.left ((cancel_epi e).mp (equalizer.condition F G))

/-- **A proper morphism agreeing with an open immersion on a dense chart exhausts the fibre
product.** If `a : V ⟶ Y` is a dominant open immersion, `b : V ⟶ U` is proper, `i : U ⟶ X` is an
open immersion, `p : Y ⟶ X` is separated and `a ≫ p = b ≫ i`, then the induced map
`V ⟶ Y ×_X U` is an isomorphism. -/
theorem isIso_pullbackLift_of_isProper_of_isDominant {V U : Scheme.{u}} (a : V ⟶ Y) (b : V ⟶ U)
    (i : U ⟶ X) (p : Y ⟶ X) [IsOpenImmersion a] [IsDominant a] [IsOpenImmersion i] [IsProper b]
    [IsSeparated p] (h : a ≫ p = b ≫ i) : IsIso (pullback.lift a b h) := by
  let t := pullback.lift a b h
  have ht : t ≫ pullback.fst p i = a := pullback.lift_fst _ _ _
  have : IsOpenImmersion (t ≫ pullback.fst p i) := ht ▸ inferInstance
  have : IsOpenImmersion t := IsOpenImmersion.of_comp t (pullback.fst p i)
  have : IsProper (t ≫ pullback.snd p i) := by
    change IsProper (pullback.lift a b h ≫ pullback.snd p i)
    rw [pullback.lift_snd]
    infer_instance
  have : IsProper t := IsProper.of_comp t (pullback.snd p i)
  have : IsDominant t := by
    constructor
    rw [denseRange_iff_closure_range,
      (pullback.fst p i).isEmbedding.closure_eq_preimage_closure_image]
    have he : pullback.fst p i '' Set.range t = Set.range a := by
      rw [← Set.range_comp, ← ht]
      rfl
    rw [he, a.denseRange.closure_range, Set.preimage_univ]
  have : Surjective t := inferInstance
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  ext x
  simp

/-- **A proper morphism admitting a section over a dense open is surjective.** If
`s : U ⟶ Y` satisfies `s ≫ π = U.ι` for a dense open `U` of `X`, then `π` is surjective. -/
theorem surjective_of_isProper_of_dense_section (π : Y ⟶ X) [IsProper π] (U : X.Opens)
    (s : U.toScheme ⟶ Y) (hπ : s ≫ π = U.ι) (hU : Dense (U : Set X)) : Surjective π := by
  have : IsDominant (s ≫ π) := hπ ▸ Opens.isDominant_ι hU
  have : IsDominant π := .of_comp s π
  infer_instance

end AlgebraicGeometry
