module

public import StacksFrontier.CategoryTheory.Sites.CoequalizerOfEpi
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.AsEqualizer
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.EqualizerOverAnAtlas
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The coequalizer hypothesis of Stacks 0792, and the lemma instantiated

`Stacks.Sites.GlobalSectionsAsEqualizer.globalSectionsForkIsLimit` is Stacks 0792: for a pair
`a, b : V ⟶ U` in a site `(C, J)` whose sheafified representables present the final sheaf as a
coequalizer `h_V^# ⇉ h_U^# ⟶ *`, the global sections of any sheaf of sets are the equalizer of
`a^*, b^* : F(U) ⇉ F(V)`. That lemma takes the coequalizer as a hypothesis and nothing in this
library produced one, so it had never been applied.

This file produces it from two conditions one checks on the site itself:

* `J.CoversTop (fun _ : Unit => U)` — the one-element family `U` covers the final object;
* `CategoryTheory.Presheaf.FactorsPairs a b` — every pair of morphisms `Z ⇉ U` is `h ≫ a`,
  `h ≫ b` for a single `h : Z ⟶ V`.

The first says the augmentation `h_U ⟶ *` of presheaves is locally surjective: a section of the
final presheaf over `X` lifts along `h_U` over exactly those `Z ⟶ X` whose source admits a
morphism to `U`, so the image sieve *is* `Sieve.ofObjects (fun _ : Unit => U) X`. The second says
the morphism `h_V ⟶ h_U ×_* h_U` determined by `a` and `b` is surjective already before
sheafification, its image sieve being the whole sieve. So
`CategoryTheory.Sheaf.isColimitCoforkOfLocallySurjective` applies, and its cofork is the one
Stacks 0792 wants once the two legs are rewritten through `Limits.pullback.lift_fst` and
`Limits.pullback.lift_snd`.

## Main definitions

* `Stacks.Sites.GlobalSectionsAsEqualizer.yonedaAugmentation` and
  `Stacks.Sites.GlobalSectionsAsEqualizer.yonedaPairToPullback`: the two presheaf morphisms the
  coequalizer presentation is read off.
* `Stacks.Sites.GlobalSectionsAsEqualizer.isColimitCoforkShYonedaTerminal`: **the coequalizer
  hypothesis of Stacks 0792**, from the two conditions above.
* `Stacks.Sites.GlobalSectionsAsEqualizer.globalSectionsForkIsLimitOfCoversTop`: **Stacks 0792
  instantiated** — the global sections of a sheaf of sets are the equalizer of `a^*` and `b^*`,
  with no hypothesis left that is not a condition on the site.

## Main results

* `Stacks.Sites.GlobalSectionsAsEqualizer.isLocallySurjective_yonedaAugmentation`: the
  augmentation of a representable to the final presheaf is locally surjective exactly when the
  one-element family of its representing object covers the final object.
* `Stacks.Sites.GlobalSectionsAsEqualizer.isLocallySurjective_yonedaPairToPullback`: the
  factorization property of the pair makes `h_V ⟶ h_U ×_* h_U` surjective on sections.

## References

* [Stacks Project, Tag 0792](https://stacks.math.columbia.edu/tag/0792)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Sites.GlobalSectionsAsEqualizer

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-! ### Transport of a coequalizer along the two parallel morphisms -/

/-- A cofork which is a colimit stays one when the two parallel morphisms it coequalizes are
rewritten along equalities. The cofork's own morphism and vertex are untouched, so this is only
the substitution; it is stated because the type of `CategoryTheory.Limits.Cofork.ofπ` mentions
the parallel pair and the two presentations of the pair at hand — one through the chosen
pullback, one through `CategoryTheory.yoneda` — agree only propositionally. -/
def isColimitCoforkOfEq {D : Type*} [Category D] {X Y Z : D} {f g f' g' : X ⟶ Y}
    (hf : f = f') (hg : g = g') (π : Y ⟶ Z) {h : f ≫ π = g ≫ π} {h' : f' ≫ π = g' ≫ π}
    (hc : IsColimit (Cofork.ofπ π h)) :
    IsColimit (Cofork.ofπ π h') := by
  subst hf
  subst hg
  exact hc

/-! ### The two locally surjective presheaf morphisms -/

/-- The final presheaf of sets on `C`, in the concrete form of the presheaf constant at a
singleton; that this is the final object is `CategoryTheory.Presheaf.isTerminalConstPUnit`, the
identification Stacks 06UN makes. -/
@[ega "0 8.1.10"]
abbrev constPUnitPresheaf : Cᵒᵖ ⥤ Type u := (Functor.const Cᵒᵖ).obj PUnit.{u + 1}

/-- The presheaf constant at a singleton is the final presheaf; this is
`CategoryTheory.Presheaf.isTerminalConstPUnit`, named here at the universe of the site so that
the fibre product `h_U ×_* h_U` below can be formed. -/
def isTerminal_constPUnitPresheaf : IsTerminal (constPUnitPresheaf (C := C)) :=
  CategoryTheory.Presheaf.isTerminalConstPUnit

/-- The augmentation `h_U ⟶ *` of a representable presheaf to the final presheaf. -/
def yonedaAugmentation (U : C) : yoneda.obj U ⟶ constPUnitPresheaf (C := C) :=
  isTerminal_constPUnitPresheaf.from _

/-- The morphism `h_V ⟶ h_U ×_* h_U` determined by a pair `a, b : V ⟶ U`. -/
noncomputable def yonedaPairToPullback {V U : C} (a b : V ⟶ U) :
    yoneda.obj V ⟶ pullback (yonedaAugmentation U) (yonedaAugmentation U) :=
  pullback.lift (yoneda.map a) (yoneda.map b) (isTerminal_constPUnitPresheaf.hom_ext _ _)

/-- The first projection of `yonedaPairToPullback a b` is `yoneda.map a`. -/
@[simp] theorem yonedaPairToPullback_fst {V U : C} (a b : V ⟶ U) :
    yonedaPairToPullback a b ≫ pullback.fst (yonedaAugmentation U) (yonedaAugmentation U) =
      yoneda.map a :=
  pullback.lift_fst _ _ _

/-- The second projection of `yonedaPairToPullback a b` is `yoneda.map b`. -/
@[simp] theorem yonedaPairToPullback_snd {V U : C} (a b : V ⟶ U) :
    yonedaPairToPullback a b ≫ pullback.snd (yonedaAugmentation U) (yonedaAugmentation U) =
      yoneda.map b :=
  pullback.lift_snd _ _ _

/-- A morphism of representables is `CategoryTheory.yoneda` of the morphism of `C` it comes
from. -/
theorem yoneda_map_yonedaEquiv {W U : C} (α : yoneda.obj W ⟶ yoneda.obj U) :
    yoneda.map (yonedaEquiv α) = α :=
  yonedaEquiv.injective (yonedaEquiv_yoneda_map _)

/-- **The augmentation of a representable to the final presheaf is locally surjective when the
one-element family of its representing object covers the final object.**

The final presheaf has one section over every object, so the image sieve of a section of it
over `X` consists of exactly those `Z ⟶ X` whose source admits *some* morphism to `U` — which
is the sieve `CategoryTheory.Sieve.ofObjects` of the one-element family `U`. -/
theorem isLocallySurjective_yonedaAugmentation {U : C}
    (hU : J.CoversTop (fun _ : Unit => U)) :
    Presheaf.IsLocallySurjective J (yonedaAugmentation U) := by
  refine ⟨fun {X} s => J.superset_covering ?_ (hU X)⟩
  rintro Z i ⟨_, ⟨t⟩⟩
  exact ⟨t, rfl⟩

/-- **The factorization property of a pair makes `h_V ⟶ h_U ×_* h_U` surjective on sections.**

A section of `h_U ×_* h_U` over `W` is a morphism `h_W ⟶ h_U ×_* h_U`, i.e. by Yoneda a pair of
morphisms `W ⇉ U`; the factorization property produces an `h : W ⟶ V` carrying `a, b` to that
pair, and the two legs of a fibre product are jointly monic, so `h` is a preimage. -/
theorem surjective_app_yonedaPairToPullback {V U : C} {a b : V ⟶ U}
    (hrel : CategoryTheory.Presheaf.FactorsPairs a b) (W : C) :
    Function.Surjective ((yonedaPairToPullback a b).app (op W)) := by
  intro y
  obtain ⟨h, hfa, hfb⟩ := hrel W
    (yonedaEquiv (yonedaEquiv.symm y ≫ pullback.fst (yonedaAugmentation U)
      (yonedaAugmentation U)))
    (yonedaEquiv (yonedaEquiv.symm y ≫ pullback.snd (yonedaAugmentation U)
      (yonedaAugmentation U)))
  refine ⟨h, ?_⟩
  have key : yoneda.map h ≫ yonedaPairToPullback a b = yonedaEquiv.symm y := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, yonedaPairToPullback_fst, ← Functor.map_comp, hfa,
        yoneda_map_yonedaEquiv]
    · rw [Category.assoc, yonedaPairToPullback_snd, ← Functor.map_comp, hfb,
        yoneda_map_yonedaEquiv]
  calc (yonedaPairToPullback a b).app (op W) h
      = yonedaEquiv (yoneda.map h ≫ yonedaPairToPullback a b) := by
        rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    _ = yonedaEquiv (yonedaEquiv.symm y) := by rw [key]
    _ = y := Equiv.apply_symm_apply _ _

/-- **The morphism `h_V ⟶ h_U ×_* h_U` of a pair with the factorization property is locally
surjective**, its image sieve being the whole sieve by
`Stacks.Sites.GlobalSectionsAsEqualizer.surjective_app_yonedaPairToPullback`. -/
theorem isLocallySurjective_yonedaPairToPullback {V U : C} {a b : V ⟶ U}
    (hrel : CategoryTheory.Presheaf.FactorsPairs a b) :
    Presheaf.IsLocallySurjective J (yonedaPairToPullback a b) := by
  refine ⟨fun {X} s => J.superset_covering ?_ (J.top_mem X)⟩
  intro W i _
  exact surjective_app_yonedaPairToPullback hrel W _

/-! ### The coequalizer hypothesis, and Stacks 0792 instantiated -/

/-- **The coequalizer hypothesis of Stacks 0792.** If the one-element family `U` covers the
final object of the site and every pair of morphisms into `U` factors through the pair
`a, b : V ⟶ U`, then the final sheaf is the coequalizer of `h_V^# ⇉ h_U^#`.

This is `CategoryTheory.Sheaf.isColimitCoforkOfLocallySurjective` at the augmentation
`h_U ⟶ *` and the morphism `h_V ⟶ h_U ×_* h_U` determined by `a` and `b`, both of which are
locally surjective by the two hypotheses. -/
noncomputable def isColimitCoforkShYonedaTerminal {V U : C} (a b : V ⟶ U)
    (hU : J.CoversTop (fun _ : Unit => U))
    (hrel : CategoryTheory.Presheaf.FactorsPairs a b) :
    IsColimit (Cofork.ofπ (shYonedaTerminal J U) (shYoneda_fork_commutes J a b)) := by
  haveI := isLocallySurjective_yonedaAugmentation J hU
  haveI := isLocallySurjective_yonedaPairToPullback J hrel
  refine isColimitCoforkOfEq
    (congrArg (presheafToSheaf J (Type u)).map (yonedaPairToPullback_fst a b))
    (congrArg (presheafToSheaf J (Type u)).map (yonedaPairToPullback_snd a b)) _
    (Sheaf.isColimitCoforkOfLocallySurjective J (yonedaAugmentation U)
      isTerminal_constPUnitPresheaf (yonedaPairToPullback a b))

/-- **Stacks 0792, instantiated.** Let `(C, J)` be a site, let `U` be an object whose
one-element family covers the final object, and let `a, b : V ⟶ U` be a pair of morphisms
through which every pair of morphisms into `U` factors. Then for every sheaf of sets `F` on `C`
the global sections `Γ(C, F)` are the equalizer of `a^*, b^* : F(U) ⇉ F(V)`.

This is `Stacks.Sites.GlobalSectionsAsEqualizer.globalSectionsForkIsLimit` with its hypothesis
discharged by `Stacks.Sites.GlobalSectionsAsEqualizer.isColimitCoforkShYonedaTerminal`. -/
noncomputable def globalSectionsForkIsLimitOfCoversTop {V U : C} (a b : V ⟶ U)
    (hU : J.CoversTop (fun _ : Unit => U))
    (hrel : CategoryTheory.Presheaf.FactorsPairs a b)
    (F : Sheaf J (Type u)) :
    IsLimit (Fork.ofι (evalAt J F U) (evalAt_eq J a b F)) :=
  globalSectionsForkIsLimit J a b (isColimitCoforkShYonedaTerminal J a b hU hrel) F

end Stacks.Sites.GlobalSectionsAsEqualizer
