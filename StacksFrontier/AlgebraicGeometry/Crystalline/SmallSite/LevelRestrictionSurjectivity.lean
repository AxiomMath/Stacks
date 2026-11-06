module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCosimplicialSystem
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FMapGlobalSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictionCalculus

/-!
# The surjectivity of the level restrictions of [Stacks, Tag 07JN]

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine and `p` nilpotent
on `Γ(X, ⊤)`, and let `F` be a sheaf of `𝒪_{X/S}`-modules on the small crystalline site
`Cris(X/S)` satisfying the two hypotheses of [Stacks, Tag 07JN]:

1. `F` is locally quasi-coherent
   (`Crystalline.GlobalCrystallineSituation.SmallSite.IsLocallyQuasiCoherent`);
2. for every morphism of `Cris(X/S)` whose map on ambient schemes is a closed immersion the
   comparison morphism `c_f : f^* F_{T'} ⟶ F_T` is locally surjective
   (`...SmallSite.CohomologyRestriction.IsSurjectiveComparison`).

The step of the proof of [Stacks, Tag 07JN] carried here is the one
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CompletedPushforwardVanishing.lean` records
as missing: that under those two hypotheses the transition maps of the inverse systems
`e ↦ Γ(T_e, F)` of [Stacks, Tag 07JL] are **surjective**.  Both spellings of those systems are
covered: the level sections `e ↦ Γ((X, T(n)_e, δ(n)), F)` on the global small crystalline site,
whose limits are the terms `M(n)` of the complex of [Stacks, Tag 07JN], and the affine-side
system `Crystalline.finiteLevelSections` of [Stacks, Tag 07JL], read on the little affine
crystalline category through the equivalence
`Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine`.

## How the global surjectivity is used

`...CohomologyRestriction.surjective_sections_fmapModuleRestriction_of_isIso_toX` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FMapGlobalSurjectivity.lean` already proves,
from hypotheses (1) and (2) and nothing else, that `Γ(T', F_{T'}) ⟶ Γ(T, F_T)` is surjective for
a closed immersion between objects of `Cris(X/S)` over the whole of `X` with `T'` affine.  That
statement is about the component over `⊤` of the `f`-map `F_{T'} ⟶ f_* F_T` of sheaves of
`𝒪_{T'}`-modules, that is, about the transition map of `F` along the restriction of `f` over the
whole of `T'`; the transition map of the level system is the transition map of `F` along `f`
itself.  The two differ by the identification of an object with its restriction to the whole of
its ambient scheme, `...SmallSite.CrystallineThickening.isoRestrictOpenTop`, and turning one into
the other is `CohomologyRestriction.surjective_presheaf_map_of_isIso_toX` below.  **No
sections description of `PresheafOfModules.pullback` is used, and none is needed**: everything
here is about images.

## Main results

* `Crystalline.DividedPowerThickening.ringFunctor` — the underlying divided power ring of an
  object of `CRIS(C/A)`, as a functor; what makes an isomorphism of thickenings bijective on
  rings.
* `...SmallSite.isAffine_target_of_isIso_toX` — the ambient scheme of an object of `Cris(X/S)`
  over the whole of an affine `X` is affine.
* `...SmallSite.CohomologyRestriction.surjective_presheaf_map_of_isIso_toX` — **the transition map
  `Γ(T', F) ⟶ Γ(T, F)` of `F` along a closed immersion between objects over the whole of an
  affine `X` is surjective**, under hypotheses (1) and (2).  This is the known global
  surjectivity transported off the restriction to `⊤`.
* `...SmallSite.surjective_abelianSheaf_map_of_isIso_toX` — the same for the underlying abelian
  sheaf of `F` at the coefficient universe `u + 1`, which is the presheaf the level systems are
  formed from.
* `...SmallSite.HasSurjectiveWholeSpaceTransitions` — **the abelian form of hypothesis (2)**: that
  the transition maps of an abelian sheaf on `Cris(X/S)` along closed immersions between objects
  over the whole of `X` are surjective.  This is all that the rest of the proof of
  [Stacks, Tag 07JN] uses of the coefficient sheaf on the surjectivity side.
* `...SmallSite.hasSurjectiveWholeSpaceTransitions_abelianSheaf` — **hypotheses (1) and (2) imply
  that abelian form** for the underlying abelian sheaf.  This is the single declaration through
  which the module structure of the coefficient sheaf enters the surjectivity half of
  [Stacks, Tag 07JN].
* `...SmallSite.surjective_level_restriction_of_isWholeSpaceSystem` — **the level restrictions of
  an arbitrary cosimplicial system of thickenings of the whole space are surjective**, given in
  addition that each level transition is a closed immersion on ambient schemes.  This is
  `...SmallSite.HasSurjectiveLevelRestrictions` of `CompletedPushforwardVanishing.lean` for that
  system, unfolded.
* `...SmallSite.isClosedImmersion_targetHom_inverse_map` — **a morphism of `Cris(X/S)` coming from
  a morphism of the little affine crystalline category that is surjective on rings is a closed
  immersion on ambient schemes.**  This is the scheme-theoretic half that the gap note of
  `SmallSite/FiniteLevelMatch.lean` lists as absent.
* `...SmallSite.surjective_affineSections_level_map` and
  `...SmallSite.surjective_wholeSpaceSystem_level_map` — **the level restrictions of the system
  `(X, T(n)_e, δ(n))` of [Stacks, Tag 07JN] are surjective, from hypotheses (1) and (2) and
  nothing else.**  The second is
  `...SmallSite.HasSurjectiveLevelRestrictions (wholeSpaceSystem S hp) (abelianSheaf F).obj`
  unfolded, and the first is `...SmallSite.HasSurjectiveUniformLevelRestrictions` unfolded; the
  two are definitionally the same condition, which is
  `...SmallSite.hasSurjectiveLevelRestrictions_wholeSpaceSystem` of `FiniteLevelMatch.lean`.
* `...SmallSite.surjective_affineSections_finiteLevelSystem_transition_of_abelian` and
  `...SmallSite.surjective_affineSections_finiteLevelSystem_transition` — **the transition maps of
  `Crystalline.finiteLevelSections` are surjective**, for an arbitrary completed thickening of
  the little affine crystalline category and an arbitrary finite-level system of it, applied to
  the sections of the coefficient sheaf read on that category.  This is the hypothesis `hF` of
  `Crystalline.isZero_firstDerivedLimit_finiteLevelSections` and of
  `Crystalline.isZero_homology_rightDerivedLimit_finiteLevelSections`.  The first is stated for an
  abelian sheaf satisfying `HasSurjectiveWholeSpaceTransitions`, the second for `F` under
  hypotheses (1) and (2), and the second is the first instantiated.

## What is and is not proved

Proved, from hypotheses (1) and (2) of [Stacks, Tag 07JN] and the standing hypotheses of that
proposition's affine situation — `X` and `S` affine and `p` nilpotent on `Γ(X, ⊤)` — and **no
other hypothesis**: the surjectivity of the level transition maps, for the system
`(X, T(n)_e, δ(n))` of the source
(`surjective_wholeSpaceSystem_level_map`, `surjective_affineSections_level_map`) and for an
arbitrary finite-level system of an arbitrary completed thickening on the affine side
(`surjective_affineSections_finiteLevelSystem_transition`).

The one carried hypothesis anywhere below is in
`surjective_level_restriction_of_isWholeSpaceSystem`, which is the statement for an *arbitrary*
cosimplicial system of thickenings of the whole space: there the closed-immersion property of the
level transitions has to be assumed, because it is a property of the system and is false for a
general one.  It is **not** assumed for the source's system: for
`...SmallSite.wholeSpaceSystem` it is *proved*, in `isClosedImmersion_targetHom_inverse_map`
together with the surjectivity of the level drops `D(n)/(p)^{N + e + 1} → D(n)/(p)^{N + e}`
(`Crystalline.surjective_hom_hom_affineLevelSystem_map`), which is why
`surjective_wholeSpaceSystem_level_map` carries no hypothesis beyond (1) and (2).

What is **not** proved here, and what this file does not claim.

* **[Stacks, Tag 07JN] does not follow from this file.**  What follows, through
  `Crystalline.GlobalCrystallineSituation.SmallSite.isZero_firstDerivedLimit_sectionSystem` and
  `...isZero_homology_rightDerivedLimit_sectionSystem` of
  `CompletedPushforwardVanishing.lean`, is the vanishing `R^p lim_e Γ(T_e, F) = 0` for `p ≥ 1`.
  Reading that as `R^p g_*(F|_𝒞) = 0` is the computation half of [Stacks, Tag 07JL], and the
  Leray step that consumes it needs the *derived* half of that tag; see the module documentation
  of `SmallSite/CompletedDirectImageLevels.lean` and `SmallSite/FiniteLevelMatch.lean`.
* **No `@[stacks]` attribute is placed.**  This is a step inside the proof of
  [Stacks, Tag 07JN], not the content of a tag.
* **The module structure of the coefficient sheaf is used exactly once below**, in
  `hasSurjectiveWholeSpaceTransitions_abelianSheaf`, which is
  `surjective_abelianSheaf_map_of_isIso_toX` repackaged.  Everything after it consumes only the
  abelian predicate `HasSurjectiveWholeSpaceTransitions`, so the surjectivity half of
  [Stacks, Tag 07JN] is available for a coefficient sheaf that is not of the form
  `abelianSheaf F`.  This note previously had no such statement, every declaration from
  `surjective_abelianSheaf_map_of_isIso_toX` down being phrased for a sheaf of modules; the
  statements of those declarations are unchanged and each is now the corresponding abelian one
  instantiated.
* This file does not import `CompletedPushforwardVanishing.lean`, so it cannot mention
  `...SmallSite.HasSurjectiveLevelRestrictions` or `Crystalline.finiteLevelSections` by name; the
  statements below are those predicates unfolded, and the unfolding is literal — the predicate is
  `∀ n e, Function.Surjective …` with exactly the map named here, and
  `Crystalline.finiteLevelSections T F` has `F.map (T.transition …)` for its transition maps.  The
  reason is confinement of the import closure, not a difference of content.

## Implementation notes

The ring-level surjectivity of the transitions of a finite-level system is proved inline in
`surjective_affineSections_finiteLevelSystem_transition` from the fields of
`Crystalline.FiniteLevelSystem`, rather than quoted from
`Crystalline.FiniteLevelSystem.surjective_transition_hom` of
`SmallSite/InjectiveLevelAcyclicity.lean`, which proves exactly that statement; that module is
not imported here for the reason in the previous paragraph.

The equivalence `𝒞ᵒᵖ ≌ Cris(Γ(X, ⊤)/Γ(S, ⊤))` enters only through
`CategoryTheory.Equivalence.fun_inv_map`: the image under the equivalence of the transport of an
affine-side morphism is that morphism conjugated by two components of the counit, and an
isomorphism of the little affine crystalline category is bijective on rings, so surjectivity on
rings survives the round trip.  The bridge from a surjective map of rings of global sections to a
closed immersion of ambient schemes is
`AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine`, which applies because an object
of `𝒞` over an affine `X` has affine ambient scheme.

## References

* [Stacks Project, Tag 07JL](https://stacks.math.columbia.edu/tag/07JL)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.DividedPowerThickening

/-- **The underlying divided power ring of an object of `CRIS(C/A)`, as a functor.**  A morphism
of divided power thickenings is a morphism of the ambient divided power rings together with two
compatibilities, and this forgets them; its purpose is that an isomorphism of thickenings is
carried to an isomorphism of divided power rings, hence to a bijection on carriers. -/
def ringFunctor (s : Crystalline.AffineCrystallineSituation.{u, u}) :
    Crystalline.DividedPowerThickening.{u, u, u} s ⥤ DividedPowerRing.{u} where
  obj X := X.ring
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

end Crystalline.DividedPowerThickening

namespace Crystalline

/-- **An isomorphism of the little affine crystalline category is surjective on rings.**  The
underlying divided power ring is a functor, `Crystalline.DividedPowerThickening.ringFunctor`, so
it carries an isomorphism to an isomorphism, and an isomorphism of divided power rings is
bijective on carriers. -/
theorem surjective_hom_hom_of_isIso {s : AffineCrystallineSituation.{u, u}}
    {Z₁ Z₂ : CrystallineThickening.{u, u, u} s} (a : Z₁ ⟶ Z₂) [IsIso a] :
    Function.Surjective (ConcreteCategory.hom a.hom.hom) :=
  have : IsIso a.hom.hom :=
    Functor.map_isIso (DividedPowerThickening.ringFunctor s) a.hom
  (ConcreteCategory.bijective_of_isIso a.hom.hom).2

/-- **A composite of morphisms of the little affine crystalline category that are surjective on
rings is surjective on rings.** -/
theorem surjective_hom_hom_comp {s : AffineCrystallineSituation.{u, u}}
    {Z₁ Z₂ Z₃ : CrystallineThickening.{u, u, u} s} (a : Z₁ ⟶ Z₂) (b : Z₂ ⟶ Z₃)
    (ha : Function.Surjective (ConcreteCategory.hom a.hom.hom))
    (hb : Function.Surjective (ConcreteCategory.hom b.hom.hom)) :
    Function.Surjective (ConcreteCategory.hom (a ≫ b).hom.hom) := by
  intro y
  obtain ⟨z, hz⟩ := hb y
  obtain ⟨x, hx⟩ := ha z
  refine ⟨x, ?_⟩
  calc ConcreteCategory.hom (a ≫ b).hom.hom x
      = ConcreteCategory.hom b.hom.hom (ConcreteCategory.hom a.hom.hom x) := rfl
    _ = y := by rw [hx, hz]

/-- **The level drops of the cosimplicial system of finite levels are surjective on rings**: for
`e ≤ e'` the map `D(n)/(p)^{N + e'} ⟶ D(n)/(p)^{N + e}` of
`Crystalline.affineLevelSystem` is surjective, both sides being quotients of `D(n)`.

This is the ring-theoretic half of the statement that the level transitions of the system
`(X, T(n)_e, δ(n))` of [Stacks, Tag 07JN] are closed immersions of affine schemes; the
scheme-theoretic half is
`Crystalline.GlobalCrystallineSituation.SmallSite.isClosedImmersion_targetHom_inverse_map`. -/
theorem surjective_hom_hom_affineLevelSystem_map {s : AffineCrystallineSituation.{u, u}}
    {ι : Type u} (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g) (n : ℕ)
    {e e' : ℕ} (h : e ≤ e') :
    Function.Surjective (ConcreteCategory.hom
      ((((affineLevelSystem s g hg).obj ⦋n⦌).map
        ((homOfLE h).op : (op e' : ℕᵒᵖ) ⟶ op e)).hom.hom)) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

end Crystalline

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The ambient scheme of an object over the whole of an affine space -/

/-- **The ambient scheme of an object of `Cris(X/S)` over the whole of an affine `X` is affine.**
The structure map `U ⟶ X` being an isomorphism, the thickened scheme `U` is affine, and the
immersion `U ⟶ T` is a thickening, so this is [Stacks, Tag 06AD] through
`Crystalline.SchemeThickening.isAffine_target`. -/
theorem isAffine_target_of_isIso_toX [IsAffine S.X] (A : CrystallineThickening S)
    (hA : IsIso A.obj.toX) : IsAffine A.obj.thickening.target.scheme :=
  have := hA
  have : IsAffine A.obj.thickening.source := IsAffine.of_isIso A.obj.toX
  A.obj.thickening.isAffine_target

namespace CohomologyRestriction

/-! ### The transition map of `F` along a closed immersion inside `𝒞` -/

/-- **The transition map `Γ(T', F) ⟶ Γ(T, F)` of a sheaf of `𝒪_{X/S}`-modules along a closed
immersion between objects of `Cris(X/S)` over the whole of an affine `X` is surjective**, under
hypotheses (1) and (2) of [Stacks, Tag 07JN] and nothing else.

The lemma
`...CohomologyRestriction.surjective_sections_fmapModuleRestriction_of_isIso_toX` gives this for
the transition map along the restriction `f|_⊤` of `f` over the whole of `T'`, which is the
component over `⊤` of the `f`-map `F_{T'} ⟶ f_* F_T`.  The square

`f|_⊤ ≫ (T'|_⊤ ⟶ T') = (T|_{f^{-1}⊤} ⟶ T) ≫ f`

of `...SmallSite.CrystallineThickening.restrictOpenMap_restrictOpenHom` identifies the two up to
the structure morphisms of the two restrictions to the whole ambient scheme, which are
isomorphisms by `...SmallSite.CrystallineThickening.isIso_restrictOpenHom_top`; the argument is
then that a surjection factoring through an injection forces the other factor to be onto. -/
theorem surjective_presheaf_map_of_isIso_toX [IsAffine S.X]
    (F : SheafOfModules.{u} (structureSheaf S)) {A B : CrystallineThickening S} (g : A ⟶ B)
    (hF : IsLocallyQuasiCoherent F) (hM : IsSurjectiveComparison F.val)
    (hg : IsClosedImmersion g.hom.targetHom.hom)
    (hA : IsIso A.obj.toX) (hB : IsIso B.obj.toX) :
    Function.Surjective (ConcreteCategory.hom (F.val.presheaf.map g.op)) := by
  have := isAffine_target_of_isIso_toX B hB
  have : IsIso (A.restrictOpenHom
      (g.hom.targetHom.hom ⁻¹ᵁ (⊤ : B.obj.thickening.target.scheme.Opens))) :=
    CrystallineThickening.isIso_restrictOpenHom_of_eq_top A rfl
  have := CrystallineThickening.isIso_restrictOpenHom_top B
  have h1 : Function.Surjective (ConcreteCategory.hom
      (F.val.presheaf.map (CrystallineThickening.restrictOpenMap g
        (⊤ : B.obj.thickening.target.scheme.Opens)).op)) :=
    surjective_sections_fmapModuleRestriction_of_isIso_toX F g hF hM hg hA hB
  have key : (F.val.presheaf.map
        (B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens)).op) ≫
        (F.val.presheaf.map (CrystallineThickening.restrictOpenMap g
          (⊤ : B.obj.thickening.target.scheme.Opens)).op) =
      (F.val.presheaf.map g.op) ≫ (F.val.presheaf.map
        (A.restrictOpenHom
          (g.hom.targetHom.hom ⁻¹ᵁ (⊤ : B.obj.thickening.target.scheme.Opens))).op) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
      CrystallineThickening.restrictOpenMap_restrictOpenHom g
        (⊤ : B.obj.thickening.target.scheme.Opens)]
  have hu : Function.Surjective (ConcreteCategory.hom (F.val.presheaf.map
      (B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens)).op)) :=
    (ConcreteCategory.bijective_of_isIso _).2
  have ht : Function.Injective (ConcreteCategory.hom (F.val.presheaf.map
      (A.restrictOpenHom
        (g.hom.targetHom.hom ⁻¹ᵁ (⊤ : B.obj.thickening.target.scheme.Opens))).op)) :=
    (ConcreteCategory.bijective_of_isIso _).1
  intro y
  obtain ⟨x, hx⟩ := (h1.comp hu) (ConcreteCategory.hom (F.val.presheaf.map
      (A.restrictOpenHom
        (g.hom.targetHom.hom ⁻¹ᵁ (⊤ : B.obj.thickening.target.scheme.Opens))).op) y)
  refine ⟨x, ht ?_⟩
  rw [← ConcreteCategory.comp_apply, ← key, ConcreteCategory.comp_apply]
  exact hx

end CohomologyRestriction

/-- **The transition map of the underlying abelian sheaf of `F` along a closed immersion between
objects over the whole of an affine `X` is surjective.**  This is
`...CohomologyRestriction.surjective_presheaf_map_of_isIso_toX` read at the coefficient universe
`u + 1` of the cohomology of `Cris(X/S)`, which is the presheaf the level systems of
[Stacks, Tag 07JL] are formed from; universe lifting of abelian groups is surjective on a
surjection because it is applied componentwise. -/
theorem surjective_abelianSheaf_map_of_isIso_toX [IsAffine S.X]
    (F : SheafOfModules.{u} (structureSheaf S)) {A B : CrystallineThickening S} (g : A ⟶ B)
    (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val)
    (hg : IsClosedImmersion g.hom.targetHom.hom)
    (hA : IsIso A.obj.toX) (hB : IsIso B.obj.toX) :
    Function.Surjective (ConcreteCategory.hom ((abelianSheaf F).obj.map g.op)) := by
  intro y
  obtain ⟨x, hx⟩ := CohomologyRestriction.surjective_presheaf_map_of_isIso_toX F g hF hM hg hA hB
    y.down
  exact ⟨ULift.up x, ULift.ext hx⟩

/-- **The abelian form of hypothesis (2) of [Stacks, Tag 07JN]**, for an abelian sheaf `G` on
`Cris(X/S)` at the coefficient universe `u + 1`: the transition map

`Γ((X, T', δ'), G) ⟶ Γ((X, T, δ), G)`

of `G` is surjective along every morphism of `Cris(X/S)` between objects over the whole of `X`
whose map on ambient schemes is a closed immersion.

This is the *conclusion* that the two module hypotheses of [Stacks, Tag 07JN] are used for, and
nothing else about the coefficient sheaf is used by the surjectivity half of that proposition's
proof: `surjective_abelianSheaf_map_of_isIso_toX` derives it for `G = abelianSheaf F` from
hypotheses (1) and (2) on `F` (that derivation is
`hasSurjectiveWholeSpaceTransitions_abelianSheaf`), and everything downstream consumes only this
predicate.  Stating it separately is what makes the chain of [Stacks, Tag 07JN] available for a
coefficient sheaf that is *not* of the form `abelianSheaf F` for a sheaf of modules `F` — for
instance `...SmallSite.tensorDifferentialFormsSheaf`, which is a sheafification and for which the
module-valued hypothesis (1) `...SmallSite.IsLocallyQuasiCoherent` cannot even be written down. -/
def HasSurjectiveWholeSpaceTransitions
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) : Prop :=
  ∀ (A B : CrystallineThickening S) (g : A ⟶ B), IsClosedImmersion g.hom.targetHom.hom →
    IsIso A.obj.toX → IsIso B.obj.toX →
      Function.Surjective (ConcreteCategory.hom (G.obj.map g.op))

/-- **Hypotheses (1) and (2) of [Stacks, Tag 07JN] imply its abelian form
`HasSurjectiveWholeSpaceTransitions` for the underlying abelian sheaf.**  This is
`surjective_abelianSheaf_map_of_isIso_toX` packaged as that predicate, and it is the *only* place
in the proof of [Stacks, Tag 07JN] below the comparison of [Stacks, Tag 07JK] at which the module
structure of the coefficient sheaf is used. -/
theorem hasSurjectiveWholeSpaceTransitions_abelianSheaf [IsAffine S.X]
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) :
    HasSurjectiveWholeSpaceTransitions (abelianSheaf F) :=
  fun _ _ g hg hA hB => surjective_abelianSheaf_map_of_isIso_toX F g hF hM hg hA hB

/-- **The level restrictions of a cosimplicial system of thickenings of the whole space are
surjective**, for a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules with surjective closed
immersion comparison maps on an affine `X`, provided each level transition is a closed immersion
on ambient schemes.

This is `...SmallSite.HasSurjectiveLevelRestrictions T (abelianSheaf F).obj` of
`SmallSite/CompletedPushforwardVanishing.lean`, unfolded; that module is not imported here.

The closed-immersion hypothesis `hclosed` is a property of the system `T` and is **assumed** at
this generality, where it is genuinely needed and genuinely can fail; for the system
`(X, T(n)_e, δ(n))` of [Stacks, Tag 07JN] it is proved, which is why
`surjective_wholeSpaceSystem_level_map` carries no such hypothesis. -/
theorem surjective_level_restriction_of_isWholeSpaceSystem [IsAffine S.X]
    (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val)
    (hT : IsWholeSpaceSystem T)
    (hclosed : ∀ n e : ℕ, IsClosedImmersion
      ((T.obj (op ⦋n⦌)).map (homOfLE (Nat.le_succ e))).hom.targetHom.hom)
    (n e : ℕ) :
    Function.Surjective (ConcreteCategory.hom ((abelianSheaf F).obj.map
      ((T.obj (op ⦋n⦌)).map (homOfLE (Nat.le_succ e))).op)) :=
  surjective_abelianSheaf_map_of_isIso_toX F _ hF hM (hclosed n e) (hT n e) (hT n (e + 1))

section Affine

variable [IsAffine S.X] [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp]

/-! ### Closed immersions inside `𝒞` from surjectivity on the affine side -/

omit [WholeSpacePresentation S hp] in
/-- **A morphism of the little affine crystalline category that is surjective on rings is
surjective on the rings of global sections of the ambient schemes of the corresponding objects of
`𝒞`.**

The affine-to-global bridge
`Crystalline.GlobalCrystallineSituation.wholeSiteToAffine` sends a morphism of `𝒞ᵒᵖ` to the map
it induces on global sections of the ambient divided power schemes, and the bridge into the
*little* affine crystalline category is its lift, so the two agree on morphisms.  The image under
the equivalence of the transport of `φ` is `φ` conjugated by two components of the counit
(`CategoryTheory.Equivalence.fun_inv_map`), and an isomorphism of the little affine crystalline
category is bijective on rings (`Crystalline.surjective_hom_hom_of_isIso`). -/
theorem surjective_appTop_targetHom_inverse_map
    {Y₁ Y₂ : _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation S hp)}
    (φ : Y₁ ⟶ Y₂) (hφ : Function.Surjective (ConcreteCategory.hom φ.hom.hom)) :
    Function.Surjective (((wholeι S).map
      ((wholeSiteEquivLittleAffine hp).inverse.map φ).unop).hom.targetHom.hom.appTop) := by
  have h : Function.Surjective (ConcreteCategory.hom
      ((wholeSiteEquivLittleAffine hp).functor.map
        ((wholeSiteEquivLittleAffine hp).inverse.map φ)).hom.hom) := by
    rw [Equivalence.fun_inv_map]
    exact _root_.Crystalline.surjective_hom_hom_comp _ _
      (_root_.Crystalline.surjective_hom_hom_of_isIso _)
      (_root_.Crystalline.surjective_hom_hom_comp _ _ hφ
        (_root_.Crystalline.surjective_hom_hom_of_isIso _))
  exact h

omit [WholeSpacePresentation S hp] in
/-- **A morphism of `Cris(X/S)` transported from a morphism of the little affine crystalline
category that is surjective on rings is a closed immersion on ambient schemes.**

Both objects lie in `𝒞`, so both ambient schemes are affine
(`isAffine_target_of_isIso_toX`), and a morphism of affine schemes which is surjective on global
sections is a closed immersion, `AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine`;
the surjectivity on global sections is `surjective_appTop_targetHom_inverse_map`.

This is the scheme-theoretic half of item 2 of the gap list in the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FiniteLevelMatch.lean`, which records it as
not being in the library. -/
theorem isClosedImmersion_targetHom_inverse_map
    {Y₁ Y₂ : _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation S hp)}
    (φ : Y₁ ⟶ Y₂) (hφ : Function.Surjective (ConcreteCategory.hom φ.hom.hom)) :
    IsClosedImmersion (((wholeι S).map
      ((wholeSiteEquivLittleAffine hp).inverse.map φ).unop).hom.targetHom.hom) :=
  have : IsAffine ((wholeι S).obj
      ((wholeSiteEquivLittleAffine hp).inverse.obj Y₂).unop).obj.thickening.target.scheme :=
    isAffine_target_of_isIso_toX _
      ((wholeSiteEquivLittleAffine hp).inverse.obj Y₂).unop.property
  have : IsAffine ((wholeι S).obj
      ((wholeSiteEquivLittleAffine hp).inverse.obj Y₁).unop).obj.thickening.target.scheme :=
    isAffine_target_of_isIso_toX _
      ((wholeSiteEquivLittleAffine hp).inverse.obj Y₁).unop.property
  IsClosedImmersion.of_surjective_of_isAffine _
    (surjective_appTop_targetHom_inverse_map hp φ hφ)

/-! ### The level restrictions of the system of [Stacks, Tag 07JN] -/

/-- A sheaf with `HasSurjectiveWholeSpaceTransitions` has surjective sections along a morphism of
the little affine crystalline category that is surjective on rings. -/
private theorem surjective_affineSections_map_of_surjective_hom_hom
    {hp : IsNilpotent (S.p : Γ(S.X, ⊤))} (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (hG : HasSurjectiveWholeSpaceTransitions G)
    {Y₁ Y₂ : _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation S hp)}
    (φ : Y₁ ⟶ Y₂) (hφ : Function.Surjective (ConcreteCategory.hom φ.hom.hom)) :
    Function.Surjective (ConcreteCategory.hom ((affineSections S hp G.obj).map φ)) :=
  hG _ _ _ (isClosedImmersion_targetHom_inverse_map hp φ hφ)
    ((wholeSiteEquivLittleAffine hp).inverse.obj Y₂).unop.property
    ((wholeSiteEquivLittleAffine hp).inverse.obj Y₁).unop.property

/-- **The level restrictions of the system `(X, T(n)_e, δ(n))` of [Stacks, Tag 07JN] are
surjective, read on the little affine crystalline category.**  For every `n` and every `e` the
restriction map of the sections of `F` along the level drop
`D(n)/(p)^{N + e + 1} ⟶ D(n)/(p)^{N + e}` is surjective.

The hypotheses are exactly hypotheses (1) and (2) of [Stacks, Tag 07JN] together with the
standing hypotheses of its affine situation; nothing stands in for a missing result.  The level
drop is surjective on rings (`Crystalline.surjective_hom_hom_affineLevelSystem_map`), hence a
closed immersion on ambient schemes after transport (`isClosedImmersion_targetHom_inverse_map`),
and the objects of the system lie in `𝒞`, so
`surjective_abelianSheaf_map_of_isIso_toX` applies.

This is `...SmallSite.HasSurjectiveUniformLevelRestrictions S hp (abelianSheaf F).obj` of
`SmallSite/FiniteLevelMatch.lean`, unfolded. -/
theorem surjective_affineSections_level_map
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) (n e : ℕ) :
    Function.Surjective (ConcreteCategory.hom
      ((affineSections S hp (abelianSheaf F).obj).map
        (((_root_.Crystalline.affineLevelSystem (affineSituation S hp)
              (wholeSpacePresentation S hp)
              (wholeSpacePresentation_surjective S hp)).obj ⦋n⦌).map
          ((homOfLE (Nat.le_succ e)).op : (op (e + 1) : ℕᵒᵖ) ⟶ op e)))) :=
  surjective_affineSections_map_of_surjective_hom_hom _
    (hasSurjectiveWholeSpaceTransitions_abelianSheaf F hF hM) _
    (_root_.Crystalline.surjective_hom_hom_affineLevelSystem_map _ _ n (Nat.le_succ e))

/-- **The level restrictions of the system `(X, T(n)_e, δ(n))` of [Stacks, Tag 07JN] are
surjective**, in the global spelling: the restriction map

`Γ((X, T(n)_{e + 1}, δ(n)), F) ⟶ Γ((X, T(n)_e, δ(n)), F)`

is surjective for every `n` and every `e`, under hypotheses (1) and (2) of that proposition and
nothing else.

This is `...SmallSite.HasSurjectiveLevelRestrictions (wholeSpaceSystem S hp) (abelianSheaf F).obj`
of `SmallSite/CompletedPushforwardVanishing.lean`, unfolded, and so it is exactly what
`...SmallSite.isZero_firstDerivedLimit_sectionSystem` and
`...SmallSite.isZero_homology_rightDerivedLimit_sectionSystem` consume.  It is the same statement
as `surjective_affineSections_level_map`, definitionally — the system `(X, T(n)_e, δ(n))` is by
construction `Crystalline.affineLevelSystem` carried across the affine-to-global equivalence,
which is what `...SmallSite.hasSurjectiveLevelRestrictions_wholeSpaceSystem` records. -/
theorem surjective_wholeSpaceSystem_level_map
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) (n e : ℕ) :
    Function.Surjective (ConcreteCategory.hom ((abelianSheaf F).obj.map
      (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).map (homOfLE (Nat.le_succ e))).op)) :=
  surjective_affineSections_level_map hp F hF hM n e

omit [WholeSpacePresentation S hp] in
/-- **The transition maps of the inverse system `e ↦ Γ(T_e, G)` of [Stacks, Tag 07JL] are
surjective**, for an arbitrary completed thickening of the little affine crystalline category, an
arbitrary finite-level system of it, and an arbitrary abelian sheaf `G` on `Cris(X/S)` satisfying
the abelian form `HasSurjectiveWholeSpaceTransitions` of hypothesis (2) of [Stacks, Tag 07JN].

This is the hypothesis `hF` of `Crystalline.isZero_firstDerivedLimit_finiteLevelSections` and of
`Crystalline.isZero_homology_rightDerivedLimit_finiteLevelSections` of
`SmallSite/CompletedPushforwardVanishing.lean`, for the coefficient functor
`affineSections S hp G.obj`: the transition maps of `Crystalline.finiteLevelSections T G` are the
maps `G.map (T.transition …)` named here.

The levels of a finite-level system are quotients of the completed thickening and the transitions
are compatible with those quotient maps, so each transition is surjective on rings; that is the
same argument as `Crystalline.FiniteLevelSystem.surjective_transition_hom`, run inline because
the module carrying it is not imported here.  Those level drops are therefore closed immersions
on ambient schemes after transport (`isClosedImmersion_targetHom_inverse_map`) and the objects of
the system lie in `𝒞`, so the hypothesis applies to them; no property of the coefficient sheaf
beyond the hypothesis is used.  The module-valued statement is
`surjective_affineSections_finiteLevelSystem_transition` below. -/
theorem surjective_affineSections_finiteLevelSystem_transition_of_abelian
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (hG : HasSurjectiveWholeSpaceTransitions G)
    {X : _root_.Crystalline.CompletedCrystallineThickening.{u, u, u} (affineSituation S hp)}
    (T : _root_.Crystalline.FiniteLevelSystem X) {e e' : ℕ} (h : e ≤ e') :
    Function.Surjective (ConcreteCategory.hom
      ((affineSections S hp G.obj).map (T.transition h))) := by
  refine surjective_affineSections_map_of_surjective_hom_hom G hG _ fun y => ?_
  obtain ⟨x, hx⟩ := T.projection_surjective e y
  refine ⟨T.projection e' x, ?_⟩
  rw [← hx]
  exact congrArg (fun k => k x) (T.transition_projection h)

omit [WholeSpacePresentation S hp] in
/-- **The transition maps of the inverse system `e ↦ Γ(T_e, F)` of [Stacks, Tag 07JL] are
surjective**, for an arbitrary completed thickening of the little affine crystalline category and
an arbitrary finite-level system of it, applied to the sections of a sheaf of `𝒪_{X/S}`-modules
satisfying hypotheses (1) and (2) of [Stacks, Tag 07JN].

This is the hypothesis `hF` of `Crystalline.isZero_firstDerivedLimit_finiteLevelSections` and of
`Crystalline.isZero_homology_rightDerivedLimit_finiteLevelSections` of
`SmallSite/CompletedPushforwardVanishing.lean`, for the coefficient functor
`affineSections S hp (abelianSheaf F).obj`: the transition maps of
`Crystalline.finiteLevelSections T G` are the maps `G.map (T.transition …)` named here.

This is `surjective_affineSections_finiteLevelSystem_transition_of_abelian` with its abelian
hypothesis discharged by `hasSurjectiveWholeSpaceTransitions_abelianSheaf`; the statement is
unchanged, and the two module hypotheses enter through that one lemma and nowhere else. -/
theorem surjective_affineSections_finiteLevelSystem_transition
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val)
    {X : _root_.Crystalline.CompletedCrystallineThickening.{u, u, u} (affineSituation S hp)}
    (T : _root_.Crystalline.FiniteLevelSystem X) {e e' : ℕ} (h : e ≤ e') :
    Function.Surjective (ConcreteCategory.hom
      ((affineSections S hp (abelianSheaf F).obj).map (T.transition h))) :=
  surjective_affineSections_finiteLevelSystem_transition_of_abelian hp (abelianSheaf F)
    (hasSurjectiveWholeSpaceTransitions_abelianSheaf F hF hM) T h

end Affine

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
