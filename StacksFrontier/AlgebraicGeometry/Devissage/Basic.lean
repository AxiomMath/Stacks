module

public import StacksFrontier.AlgebraicGeometry.HigherRank.Basic
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.LongExactSequence
public import StacksFrontier.AlgebraicGeometry.SerreCriterionH1.Hgroup
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Natural
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyGlue.AffineOpenVanishing
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Devissage
public import StacksFrontier.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.Basic

/-!
# The top of the dévissage for [Stacks, Tag 01YQ]: conditions (1) and (2) for `H¹`

The source's proof of [Stacks, Tag 01YQ] runs the dévissage [Stacks, Tag 01YM] on the property

    𝒫(ℱ) ⇔ H¹(X, ℱ) = 0

and then concludes by Serre's criterion [Stacks, Tag 01XF]. The chain of lemmas is four deep —
01YQ ← 01YM ← {01YL, 01YG} ← 01YE — and **this file is the step at the very top**: that
`𝒫 = H¹`-vanishing satisfies conditions (1) and (2) of
01YM, and that the resulting vanishing feeds Serre's criterion.

## What the library already provides, and where

* [Stacks, Tag 01XF] — `Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_ideal`, and for the
  cohomology used here `Stacks.SerreCriterionH1.isAffine_of_forall_isZero_hgroup_one_ideal`.
* [Stacks, Tag 01YM] on two named hypotheses —
  `Stacks.AlgebraicGeometry.Tag01YMHigherRank.property_higher_rank_of_criteria`, which takes
  [Stacks, Tag 01YE] (as `Tag01YEStalkBridge.HasGenericStalkIdealCoproductSub`) and [Stacks,
  Tag 01YL] (as `Tag01YMHigherRank.HasIrreducibleHigherRankCriterion`).
* The long exact cohomology sequence —
  `Stacks.SerreAffinenessCriterion.isZero_hgroup_of_shortExact`, which *is* 01YM's condition (1)
  for this `𝒫`, already in the shape the dévissage consumes.
* [Stacks, Tag 01XB] — `Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine`.
* [Stacks, Tag 089W] — `Stacks.AffineCohomologyPushforward.cohomologyPushforwardIsoApp`.
* [Stacks, Tag 01Y1] — `Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono`, which
  is what makes a quasi-coherent *subobject of `𝒪_X`* coherent on a Noetherian scheme and so
  brings Serre's criterion inside the dévissage's reach.

## Main results

* `isZero_obj_of_isZero_obj_of_retraction`: a functor preserving zero morphisms carries a retract
  of a zero object to a zero object. Stated with every typeclass argument a variable.
* `preservesZeroMorphisms_hfunctor`: `Hⁿ(U, -)` preserves zero morphisms, read off the δ-functor.
* `isZero_hgroup_terminal`: `Hⁿ(X, 0) = 0` — 01YM's `hzero`.
* `isZero_hgroup_of_isZero_hgroup_pi`: **01YM's condition (2)** for `𝒫 = H¹`-vanishing.
* `isZero_hgroup_pushforward_of_isAffine`: `Hᵖ(X, f_*ℱ) = 0` for `p > 0`, `f` affine and the
  source affine — [Stacks, Tag 089W] composed with [Stacks, Tag 01XB]. This is the ingredient
  the *remaining* obligation (below) is to be discharged with.
* `forall_isZero_hgroup_one_of_hgeneric`: `H¹(X, ℱ) = 0` for every coherent `ℱ`, from 01YE, 01YL
  and 01YM's condition (3) alone.
* `isZero_hgroup_one_subobject_unit`: the same vanishing on quasi-coherent subobjects of `𝒪_X`.
* `isAffine_of_isFinite_surjective_of_hgeneric`: **[Stacks, Tag 01YQ] with exactly three
  hypotheses — 01YE, 01YL, and 01YM's condition (3) for `H¹`.**

## What is not done

**No `stacks` attribute is attached and none is earned.** Tag 01YQ carries a single unlabelled
assertion, so there is no partial credit for that tag, and every theorem below carries
hypotheses the tag does not grant. Tags 01YE, 01YL, 01YM and 01YQ all remain open.

Three obligations remain between this file and 01YQ, and they are of very different sizes.

1. **01YM's condition (3) for `H¹` — the hypothesis `hgeneric` below.** This is the only place
   the finiteness and surjectivity of `f` are used. The coherent `𝒢` it asks for is supplied by
   [Stacks, Tag 01YO], proved and tagged as `exists_isCoherent_supp_pushforward_eq_range` in
   `Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport`,
   whose stalk-annihilation conclusion is *character for character*
   `Tag01YEStalkBridge.IsMaximalIdealAnnihilated` at the same point. What is then owed is
   condition (3)(c) for `𝒢' = 𝒥·𝒢`: its coherence is
   `Stacks.AlgebraicGeometry.IdealPowerSmul.isCoherent_idealPowSmul`; its sections condition is
   `Tag01YG.obj_idealPowSmul` at `n = 1`; the surjectivity on the stalk at `ξ` is
   `Stacks.AlgebraicGeometry.IdealPowerComparison.bijective_idealPowerMultiple_ι_app` over the
   opens inside `IdealPowerHomColimit.idealComplement 𝒥`; and `H¹(X, 𝒥·𝒢) = 0` is
   `isZero_hgroup_pushforward_of_isAffine` **once** `𝒥·f_*ℱ` is identified with
   `f_*((f⁻¹𝒥)·ℱ)`. [Stacks, Tag 01YP] is proved as
   `Stacks.AlgebraicGeometry.AffineIdealPushforward.ideal_smul_pushforward_sections_eq`, but
   **only as an equality of section submodules on each affine open**; promoting it to the
   isomorphism of module sheaves that [Stacks, Tag 089W] consumes is what remains of this
   obligation.
2. **[Stacks, Tag 01YL].** Not derivable from 01YE plus the existing dévissage machinery: the
   01YH route to its top stratum goes through the two-out-of-three extension property, which
   01YL's condition (1) does not grant, and through multiplicity one, which is what 01YL's
   condition (2) exists to remove. The load-bearing missing statement is that a nonzero
   quasi-coherent sheaf of ideals on an integral scheme has full support, which is also the
   blocker for 01YH's own top stratum.
3. **[Stacks, Tag 01YE].** The deepest layer, and the one everything else waits on — proving it
   also discharges Tag 01YG outright, via
   `Tag01YEStalkBridge.property_of_hasGenericStalkIdealCoproductSub`. Of the six lemmas its
   source proof consumes, [Stacks, Tag 01Y4] and [Stacks, Tag 01J3] are proved and tagged and
   the function field at the generic point is Mathlib's; the largest genuinely missing piece is
   the *global* bijectivity of [Stacks, Tag 01YB], whose canonical map is already built and
   characterised as `Stacks.AlgebraicGeometry.IdealPowerComparison.canonicalHomsOverOpen` with
   the affine ring-level isomorphism proved as
   `Stacks.AlgebraicGeometry.IdealPowerSections.isIso_canonicalMapToSections`.

## Implementation notes

**`[HasDerivedCategory _]` is a local instance and appears in no statement**, for the reason
recorded in `StacksFrontier/AlgebraicGeometry/SerreAffinenessCriterion/LongExactSequence.lean`:
`Hgroup` mentions no derived category, so the statements are independent of the model, and
`HasDerivedCategory.standard` is deliberately not global upstream.

**Condition (2) is proved by a retraction, not by additivity of a biproduct.** `∏ᶜ` over
`Fin (n+1)` is what 01YM's statement uses; `Pi.lift (fun _ ↦ 𝟙 ℱ)` followed by `Pi.π _ 0` is the
identity by `Pi.lift_comp_π`, so `H¹(ℱ)`'s identity factors through `H¹(∏ᶜ ℱ) = 0`. The generic
lemma `isZero_obj_of_isZero_obj_of_retraction` is stated with every typeclass argument a
variable: instantiating it is then a unification, and instance search is never asked to cross
the `AlgebraicGeometry.Scheme.Modules`/`SheafOfModules` spelling. Stating the split equation
with `by simp` instead fails, with the error reporting an application type mismatch between
`TopCat.Sheaf RingCat ↑X.toPresheafedSpace` and `Sheaf (Opens.grothendieckTopology ↥X) RingCat` —
the same family as the `def`-versus-`abbrev` issue for `AlgebraicGeometry.Scheme.Modules`.

**`Mono I.arrow` has to be supplied by hand.** For `I : Subobject (SheafOfModules.unit _)`,
`CategoryTheory.Subobject.arrow_mono` is an instance in the `SheafOfModules` category and is not
found at the `X.Modules` spelling that [Stacks, Tag 01Y1] is stated over; the application is
therefore written with `@` and the instance passed explicitly.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YL](https://stacks.math.columbia.edu/tag/01YL)
* [Stacks Project, Tag 01YM](https://stacks.math.columbia.edu/tag/01YM)
* [Stacks Project, Tag 01YO](https://stacks.math.columbia.edu/tag/01YO)
* [Stacks Project, Tag 01YQ](https://stacks.math.columbia.edu/tag/01YQ)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Tag01YQDevissage

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules
attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u})

/-- Generic: a functor preserving zero morphisms carries a retract of a zero object to a zero
object.  Stated with every typeclass argument a variable, so that instantiating it is a
unification and never asks instance search to cross a spelling. -/
theorem isZero_obj_of_isZero_obj_of_retraction {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (G : C ⥤ D) [G.PreservesZeroMorphisms] {A B : C}
    (ι : A ⟶ B) (π : B ⟶ A) (hsplit : ι ≫ π = 𝟙 A) (hB : IsZero (G.obj B)) :
    IsZero (G.obj A) := by
  refine (IsZero.iff_id_eq_zero _).2 ?_
  calc 𝟙 (G.obj A) = G.map (ι ≫ π) := by rw [hsplit, G.map_id]
    _ = G.map ι ≫ G.map π := G.map_comp _ _
    _ = 0 ≫ G.map π := by rw [hB.eq_of_tgt (G.map ι) 0]
    _ = 0 := zero_comp

/-- `Hⁿ(U, -)` preserves zero morphisms: it is the degree-`n` part of the right derived
δ-functor of `Γ(U, -)`, and every part of a δ-functor is additive. -/
instance preservesZeroMorphisms_hfunctor (U : X.Opens) (n : ℕ) :
    (Hfunctor X.ringCatSheaf U n).PreservesZeroMorphisms :=
  have : (Hfunctor X.ringCatSheaf U n).Additive :=
    CategoryTheory.DeltaFunctor.additive
      (Stacks.SerreAffinenessCriterion.cohomologyDeltaFunctor X U) n
  Functor.preservesZeroMorphisms_of_additive _

/-- `Hⁿ(X, -)` of a zero object vanishes. -/
theorem isZero_hgroup_terminal (n : ℕ) :
    IsZero (Hgroup X.ringCatSheaf ⊤ n (⊤_ X.Modules)) :=
  Functor.map_isZero _ CoherentDevissage.isZero_terminal

/-- `Hⁿ(X, -)` descends from a nonempty finite product. -/
theorem isZero_hgroup_of_isZero_hgroup_pi (n : ℕ) (F : X.Modules) (k : ℕ)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ n (∏ᶜ fun _ : Fin (k + 1) => F))) :
    IsZero (Hgroup X.ringCatSheaf ⊤ n F) :=
  isZero_obj_of_isZero_obj_of_retraction (Hfunctor X.ringCatSheaf ⊤ n)
    (Pi.lift (fun _ : Fin (k + 1) => 𝟙 F)) (Pi.π (fun _ : Fin (k + 1) => F) 0)
    (Pi.lift_comp_π (fun _ : Fin (k + 1) => 𝟙 F) 0) h

/-- Higher cohomology of a direct image from an affine scheme along an affine morphism vanishes. -/
theorem isZero_hgroup_pushforward_of_isAffine {Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    [IsAffine Y] (F : Y.Modules) [F.IsQuasicoherent] (p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p ((Scheme.Modules.pushforward f).obj F)) :=
  IsZero.of_iso (Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine Y F p hp)
    (Stacks.AffineCohomologyPushforward.cohomologyPushforwardIsoApp f p F).symm

/-! ### The dévissage applied to `H¹` -/

/-- **`H¹(X, ℱ) = 0` for every coherent `ℱ`, from the dévissage and clause (3) alone.**
Conditions (1) and (2) of [Stacks, Tag 01YM] are discharged here: (1) is the long exact
cohomology sequence and (2) is additivity of `H¹`. -/
theorem forall_isZero_hgroup_one_of_hgeneric [IsNoetherian X]
    (h01YE : Tag01YEStalkBridge.HasGenericStalkIdealCoproductSub X)
    (h01YL : Tag01YMHigherRank.HasIrreducibleHigherRankCriterion X)
    (hgeneric : ∀ (I : X.IdealSheafData) [IsIntegral I.subscheme],
      ∃ G : X.Modules, G.IsCoherent ∧
        (∀ x : X, x ∈ I.support ↔ Nontrivial (G.presheaf.stalk x)) ∧
        Tag01YEStalkBridge.IsMaximalIdealAnnihilated G
          (I.subschemeι (genericPoint I.subscheme)) ∧
        (∀ J : X.IdealSheafData,
          I.subschemeι (genericPoint I.subscheme) ∉ J.support →
          ∃ G' : G.Submodule,
            G'.toSheafOfModules.IsCoherent ∧
            (∀ (U : X.affineOpens) (s : Γ(G'.toSheafOfModules, U.1)),
              (Scheme.Modules.Hom.app G'.ι U.1 s : Γ(G, U.1)) ∈
                J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1))) ∧
            Function.Surjective
              (((TopCat.Presheaf.stalkFunctor Ab
                (I.subschemeι (genericPoint I.subscheme))).map
                  (Scheme.Modules.Hom.mapPresheaf G'.ι)).hom) ∧
            IsZero (Hgroup X.ringCatSheaf ⊤ 1 G'.toSheafOfModules))) :
    ∀ F : X.Modules, F.IsCoherent → IsZero (Hgroup X.ringCatSheaf ⊤ 1 F) :=
  Tag01YMHigherRank.property_higher_rank_of_criteria X h01YE h01YL
    (fun F ↦ IsZero (Hgroup X.ringCatSheaf ⊤ 1 F))
    (isZero_hgroup_terminal X 1)
    (fun _ hS _ _ _ h₁ h₃ ↦
      Stacks.SerreAffinenessCriterion.isZero_hgroup_of_shortExact X ⊤ hS 1 h₁ h₃)
    (fun F _ hF ↦ hF.elim fun k hk ↦ isZero_hgroup_of_isZero_hgroup_pi X 1 F k hk)
    hgeneric

/-- **`H¹` vanishes on every quasi-coherent subobject of `𝒪_X`.** On a Noetherian scheme such a
subobject is coherent by [Stacks, Tag 01Y1], so the dévissage applies to it. -/
theorem isZero_hgroup_one_subobject_unit [IsNoetherian X]
    (h : ∀ F : X.Modules, F.IsCoherent → IsZero (Hgroup X.ringCatSheaf ⊤ 1 F))
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf))
    (hI : (Subobject.underlying.obj I).IsQuasicoherent) :
    IsZero (Hgroup X.ringCatSheaf ⊤ 1 (Subobject.underlying.obj I)) :=
  h _ (@CoherentSubquotients.isCoherent_of_mono X _
    (SheafOfModules.unit X.ringCatSheaf) (Subobject.underlying.obj I) _ hI I.arrow
    (Subobject.arrow_mono I))

/-- **[Stacks, Tag 01YQ] with the dévissage layers as named hypotheses.** A Noetherian scheme
receiving a finite surjective morphism from an affine scheme is affine, given
[Stacks, Tag 01YE], [Stacks, Tag 01YL], and clause (3) of [Stacks, Tag 01YM] for `H¹`.

Everything else in the source's proof of 01YQ is discharged: Serre's criterion
[Stacks, Tag 01XF] is proved, the dévissage reduction [Stacks, Tag 01YM] is proved on its two
named hypotheses, and clauses (1) and (2) are proved above. -/
theorem isAffine_of_isFinite_surjective_of_hgeneric {Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [Surjective f] [IsAffine Y] [IsNoetherian X]
    (h01YE : Tag01YEStalkBridge.HasGenericStalkIdealCoproductSub X)
    (h01YL : Tag01YMHigherRank.HasIrreducibleHigherRankCriterion X)
    (hgeneric : ∀ (I : X.IdealSheafData) [IsIntegral I.subscheme],
      ∃ G : X.Modules, G.IsCoherent ∧
        (∀ x : X, x ∈ I.support ↔ Nontrivial (G.presheaf.stalk x)) ∧
        Tag01YEStalkBridge.IsMaximalIdealAnnihilated G
          (I.subschemeι (genericPoint I.subscheme)) ∧
        (∀ J : X.IdealSheafData,
          I.subschemeι (genericPoint I.subscheme) ∉ J.support →
          ∃ G' : G.Submodule,
            G'.toSheafOfModules.IsCoherent ∧
            (∀ (U : X.affineOpens) (s : Γ(G'.toSheafOfModules, U.1)),
              (Scheme.Modules.Hom.app G'.ι U.1 s : Γ(G, U.1)) ∈
                J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1))) ∧
            Function.Surjective
              (((TopCat.Presheaf.stalkFunctor Ab
                (I.subschemeι (genericPoint I.subscheme))).map
                  (Scheme.Modules.Hom.mapPresheaf G'.ι)).hom) ∧
            IsZero (Hgroup X.ringCatSheaf ⊤ 1 G'.toSheafOfModules))) :
    IsAffine X :=
  Stacks.SerreCriterionH1.isAffine_of_forall_isZero_hgroup_one_ideal X
    (isZero_hgroup_one_subobject_unit X
      (forall_isZero_hgroup_one_of_hgeneric X h01YE h01YL hgeneric))

end Stacks.AlgebraicGeometry.Tag01YQDevissage

end
