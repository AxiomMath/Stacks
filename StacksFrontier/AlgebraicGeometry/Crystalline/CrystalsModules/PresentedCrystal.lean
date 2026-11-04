module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.ComparisonFunctoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentImpliesLocal
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation

/-!
# A globally presented sheaf of modules on the big crystalline site is a crystal

Let `F` be a sheaf of `𝒪_{X/S}`-modules on the big crystalline site of a global crystalline
situation.  The crystal condition of [Stacks, Tag 07IS] says that for every morphism
`f : (U, T, δ) ⟶ (U', T', δ')` the comparison map `c_f : f^* F_{T'} ⟶ F_T` of *sheaves* of
`𝒪_T`-modules is an isomorphism; that is
`Crystalline.GlobalCrystallineSituation.IsSheafCrystal`, and it is the reading under which
[Stacks, Tag 07IT] is true — the presheaf-level reading is false, see the module documentation of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.SheafCrystal`.

This file proves the computation the source of [Stacks, Tag 07IT] performs for the implication
(1) ⇒ (2)(b):

> assume `F` restricted to `𝒞/(U, T, δ)` has a global presentation
> `⊕_J 𝒪_{X/S} → ⊕_I 𝒪_{X/S} → F → 0`. It is clear that this gives a presentation
> `⊕_J 𝒪_T → ⊕_I 𝒪_T → F_T → 0` ... Moreover, the presentation restricts to `T'` to give a
> similar presentation of `F_{T'}`, whence (b) holds.

namely: **a sheaf of `𝒪_{X/S}`-modules with a global presentation on `CRIS(X/S)` is a crystal in
`𝒪_{X/S}`-modules.**

## Testing the crystal condition without the pullback

The obstacle this file removes is a universe one, and it is removed by changing *how* the crystal
condition is tested, not by moving any universe.

A global presentation in the sense of [Stacks, Tag 03DE] (6),
`SheafOfModules.HasGlobalPresentation`, indexes its coproducts by types in `Type (max u v r m)`,
which on `CRIS(X/S)` is `Type (u + 1)`, and presents the universe lift
`SheafOfModules.uliftForPresentation` of the module: the diagram lives in `SheafOfModules.{u + 1}`.
The crystal condition, on the other hand, lives at module universe `u` and nowhere else, because
`SheafOfModules.pullback` rests on `PresheafOfModules.instIsRightAdjointPushforward`, which comes
from Mathlib's `PresheafOfModules.pullbackObjIsDefined_eq_top`, stated for
`{C D : Type u} [SmallCategory C]` `[SmallCategory D]`, `RingCat.{u}` and `PresheafOfModules.{u}`
with all three universes equal. So the presentation and the comparison map cannot be put in one
category, and the obstruction recorded in the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ModuleUniverseComparison.lean` — that the
crystal condition cannot be *restated* at the raised module universe — stands.

It does not obstruct this implication, because the comparison map need never be raised.  By the
adjunction, `c_f` is an isomorphism exactly when, for every sheaf of `𝒪_T`-modules `Z`,

  `k ↦ (F_{T'} ⟶ f_* F_T) ≫ f_*(k)`,  `k : F_T ⟶ Z`,

is a bijection onto the maps `F_{T'} ⟶ f_* Z`
(`Thickening.isIso_moduleComparisonSheaf_iff_bijective_fmapComp`).
That criterion names only the `f`-map, the restriction `F ↦ F_T` and the pushforward `f_*`, all of
which are computed on sections and so exist at every module universe.  Both sides of it are
statements about the same morphism — nothing is weakened — and the right-hand side transfers
along a universe lift of the module sections, which the pullback does not
(`Crystalline.GlobalCrystallineSituation.Thickening.bijective_fmapCompLift_iff`, by full
faithfulness of the lift).

With the condition in that shape the source's argument runs: composition with the `f`-map is a
natural transformation between two contravariant functors of the module
(`Crystalline.GlobalCrystallineSituation.Thickening.fmapComp_naturality`), both of which take the
presentation to a colimit — restriction to the ambient scheme is a pushforward along a functor
that is continuous *and cocontinuous*, so it preserves colimits by
`Stacks.SheafOfModules.pushforward_preservesColimits` — and it is bijective at `𝒪_{X/S}` itself,
because the comparison map of the structure sheaf is an isomorphism
(`Crystalline.GlobalCrystallineSituation.Thickening.isIso_moduleComparisonSheaf_unit`).

## Main definitions

* `Crystalline.GlobalCrystallineSituation.Thickening.moduleRestrictionSheafFunctor` — the
  restriction `F ↦ F_T` of [Stacks, Tag 07IQ] as a functor, at an arbitrary module universe.
* `Crystalline.GlobalCrystallineSituation.Thickening.moduleFMapSheafOfUniv` and
  `Crystalline.GlobalCrystallineSituation.Thickening.fmapComp` — the `f`-map and composition with
  it, likewise at an arbitrary module universe.

## Main results

* `Stacks.PresentedBijectivity.bijective_of_cofan` and
  `Stacks.PresentedBijectivity.bijective_of_cofork` — **the two abstract steps**: a natural family
  of maps between the hom-sets out of two colimit-preserving functors, bijective at an object, is
  bijective at a coproduct of copies of it and at a coequaliser.
* `Thickening.isIso_moduleComparisonSheaf_iff_bijective_fmapComp`
  — **the crystal condition at a morphism, tested without the pullback.**
* `Crystalline.GlobalCrystallineSituation.Thickening.bijective_fmapCompLift_iff` — that test
  transfers along a universe lift of the module sections.
* `Crystalline.GlobalCrystallineSituation.Thickening.isSheafCrystal_of_hasGlobalPresentation` —
  **a sheaf of `𝒪_{X/S}`-modules with a global presentation on `CRIS(X/S)` is a crystal in
  `𝒪_{X/S}`-modules.**

## What this file proves, and where the tag is delivered

No `@[stacks]` attribute is placed here, because what is proved has a stronger hypothesis than
quasi-coherence: a *global* presentation on all of `CRIS(X/S)`, whereas
`SheafOfModules.IsQuasicoherentOnSite` asks for a presentation on the members of a covering of
each object.  The source's own first move, "since it suffices to prove (a) and (b) Zariski
locally", bridges the two, and it is carried out in two further files.

`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.RestrictOverCrystal` redoes the
computation of this file on a localised site `CRIS(X/S)/B'`, which is the shape in which
quasi-coherence supplies a presentation: it constructs the restriction functor from the opens of
the ambient scheme of an object over `B'` into that localised site, with its continuity and
cocontinuity, and concludes that the comparison map is an isomorphism at every morphism whose
target is `B'`.
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentCrystal` then glues over a
Zariski cover of the ambient scheme of the target, with the cocycle of the `f`-map and the
locality of the crystal condition, and so proves the implication (1) ⇒ (2)(b) itself, as
`Crystalline.GlobalCrystallineSituation.isSheafCrystal_of_isQuasicoherentOnSite`; the small site's
form is
`Crystalline.GlobalCrystallineSituation.SmallSite.isSheafCrystal_of_isQuasicoherentOnSite`.

The other half of that implication, (1) ⇒ (2)(a), carries the attribute at
`Crystalline.GlobalCrystallineSituation.isLocallyQuasiCoherent_of_isQuasicoherentOnSite` for the
big site and at
`Crystalline.GlobalCrystallineSituation.SmallSite.isLocallyQuasiCoherent_of_isQuasicoherentOnSite`
for the small one.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe m u u₁ v₁

namespace Stacks.PresentedBijectivity

variable {𝒜 : Type*} [Category 𝒜] {ℬ₁ : Type*} [Category ℬ₁] {ℬ₂ : Type*} [Category ℬ₂]
  {F₁ : 𝒜 ⥤ ℬ₁} {F₂ : 𝒜 ⥤ ℬ₂} {Z₁ : ℬ₁} {Z₂ : ℬ₂}
  {θ : ∀ N : 𝒜, (F₁.obj N ⟶ Z₁) → (F₂.obj N ⟶ Z₂)}

/-- **A natural family of maps bijective at `U` is bijective at a coproduct of copies of `U`**,
provided both functors carry the cofan to a colimit cofan. -/
theorem bijective_of_cofan
    (hθ : ∀ {M N : 𝒜} (ψ : M ⟶ N) (k : F₁.obj N ⟶ Z₁),
      θ M (F₁.map ψ ≫ k) = F₂.map ψ ≫ θ N k)
    {I : Type*} {U N : 𝒜} (ι : I → (U ⟶ N))
    (h₁ : IsColimit (Cofan.mk (f := fun _ : I ↦ F₁.obj U) (F₁.obj N) fun i ↦ F₁.map (ι i)))
    (h₂ : IsColimit (Cofan.mk (f := fun _ : I ↦ F₂.obj U) (F₂.obj N) fun i ↦ F₂.map (ι i)))
    (hU : Function.Bijective (θ U)) : Function.Bijective (θ N) := by
  refine ⟨fun k k' hkk' ↦ ?_, fun l ↦ ?_⟩
  · refine Cofan.IsColimit.hom_ext h₁ _ _ fun i ↦ hU.1 ?_
    simp only [Limits.cofan_mk_inj]
    rw [hθ (ι i) k, hθ (ι i) k', hkk']
  · choose k hk using fun i ↦ hU.2 (F₂.map (ι i) ≫ l)
    refine ⟨Cofan.IsColimit.desc h₁ k, Cofan.IsColimit.hom_ext h₂ _ _ fun i ↦ ?_⟩
    have hfac : F₁.map (ι i) ≫ Cofan.IsColimit.desc h₁ k = k i := Cofan.IsColimit.fac h₁ k i
    simp only [Limits.cofan_mk_inj]
    rw [← hθ (ι i), hfac, hk i]

/-- **A natural family of maps bijective at `P` and injective at `Q` is bijective at a coequaliser
of a pair `Q ⟶ P`**, provided both functors carry the cofork to a colimit cofork. -/
theorem bijective_of_cofork
    (hθ : ∀ {M N : 𝒜} (ψ : M ⟶ N) (k : F₁.obj N ⟶ Z₁),
      θ M (F₁.map ψ ≫ k) = F₂.map ψ ≫ θ N k)
    {Q P N : 𝒜} {a₁ a₂ : Q ⟶ P} {b : P ⟶ N} {w₁ : F₁.map a₁ ≫ F₁.map b = F₁.map a₂ ≫ F₁.map b}
    {w₂ : F₂.map a₁ ≫ F₂.map b = F₂.map a₂ ≫ F₂.map b}
    (h₁ : IsColimit (Cofork.ofπ (F₁.map b) w₁))
    (h₂ : IsColimit (Cofork.ofπ (F₂.map b) w₂))
    (hP : Function.Bijective (θ P)) (hQ : Function.Injective (θ Q)) :
    Function.Bijective (θ N) := by
  have he₁ : Epi (F₁.map b) := by simpa using Cofork.IsColimit.epi h₁
  have he₂ : Epi (F₂.map b) := by simpa using Cofork.IsColimit.epi h₂
  refine ⟨fun k k' hkk' ↦ ?_, fun l ↦ ?_⟩
  · refine (cancel_epi (F₁.map b)).1 (hP.1 ?_)
    rw [hθ b k, hθ b k', hkk']
  · obtain ⟨k₀, hk₀⟩ := hP.2 (F₂.map b ≫ l)
    have hw : F₁.map a₁ ≫ k₀ = F₁.map a₂ ≫ k₀ := by
      refine hQ ?_
      rw [hθ a₁ k₀, hθ a₂ k₀, hk₀, ← Category.assoc, ← Category.assoc, w₂]
    refine ⟨Cofork.IsColimit.desc h₁ k₀ hw, (cancel_epi (F₂.map b)).1 ?_⟩
    rw [← hθ b]
    have hfac : F₁.map b ≫ Cofork.IsColimit.desc h₁ k₀ hw = k₀ := by
      simpa using Cofork.IsColimit.π_desc' h₁ k₀ hw
    rw [hfac, hk₀]

end Stacks.PresentedBijectivity

namespace Crystalline.GlobalCrystallineSituation.Thickening

variable {S : GlobalCrystallineSituation.{u}} {A B : Thickening S}

/-- The comparison of structure sheaves for the restriction to the ambient scheme of an object is
the identity: the restriction of `𝒪_{X/S}` to the opens of the ambient scheme *is* its restriction
along the restriction functor. -/
noncomputable def restrictOpenStructureHom (A : Thickening S) :
    A.ringRestrictionSheaf ⟶
      (A.restrictOpenFunctor.sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥A.thickening.target.scheme) (topology S)).obj
          (crystallineStructureSheaf S) :=
  𝟙 _

/-- **The restriction `F ↦ F_T` of [Stacks, Tag 07IQ] as a functor, at an arbitrary module
universe.**  It is the pushforward of sheaves of modules along the restriction functor of the
object; at the module universe `u` it is
`Crystalline.GlobalCrystallineSituation.Thickening.moduleRestrictionSheaf`, by
`Crystalline.GlobalCrystallineSituation.Thickening.moduleRestrictionSheafFunctor_obj`. -/
noncomputable def moduleRestrictionSheafFunctor (A : Thickening S) :
    SheafOfModules.{m} (crystallineStructureSheaf S) ⥤
      SheafOfModules.{m} A.ringRestrictionSheaf :=
  SheafOfModules.pushforward.{m} (restrictOpenStructureHom A)

/-- At the module universe `u`, the restriction functor sends a sheaf of `𝒪_{X/S}`-modules `M` to
`moduleRestrictionSheaf M A`. -/
@[simp]
theorem moduleRestrictionSheafFunctor_obj
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (A : Thickening S) :
    (moduleRestrictionSheafFunctor.{u} A).obj M = moduleRestrictionSheaf M A := rfl

/-- **Restriction to the ambient scheme preserves colimits of size `u + 1`**, the size in which a
global presentation on the big crystalline site is indexed.  The restriction functor is continuous
and cocontinuous, so this is
`Stacks.SheafOfModules.pushforward_preservesColimits`; the four sheafification hypotheses are
discharged here, inside a statement mentioning only the module universe `u + 1`. -/
theorem preservesColimitsOfSize_moduleRestrictionSheafFunctor (A : Thickening S) :
    PreservesColimitsOfSize.{u + 1, u + 1}
      (show SheafOfModules.{u + 1} (crystallineStructureSheaf S) ⥤
          SheafOfModules.{u + 1} A.ringRestrictionSheaf from
        moduleRestrictionSheafFunctor.{u + 1} A) := by
  have _ : HasSheafify (topology S) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _
  have _ : (topology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _
  have _ : HasSheafify (Opens.grothendieckTopology ↥A.thickening.target.scheme)
      AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u} _
  have _ : GrothendieckTopology.WEqualsLocallyBijective
      (Opens.grothendieckTopology ↥A.thickening.target.scheme) AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u, u} _
  exact Stacks.SheafOfModules.pushforward_preservesColimits.{u, u, u + 1, u + 1, u, u}
    A.restrictOpenFunctor (restrictOpenStructureHom A)

/-- **The `f`-map of [Stacks, Tag 07IQ] at an arbitrary module universe.** -/
noncomputable def moduleFMapSheafOfUniv
    (M : SheafOfModules.{m} (crystallineStructureSheaf S)) (g : A ⟶ B) :
    (moduleRestrictionSheafFunctor.{m} B).obj M ⟶
      (SheafOfModules.pushforward.{m} (ringRestrictionSheafFMap g)).obj
        ((moduleRestrictionSheafFunctor.{m} A).obj M) :=
  ⟨PresheafOfModules.pushforwardOfNatTrans (restrictOpenFunctorMap g) (crisRing S) M.val⟩

/-- At the module universe `u`, `moduleFMapSheafOfUniv` is the `f`-map `moduleFMapSheaf`. -/
theorem moduleFMapSheafOfUniv_eq (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    (g : A ⟶ B) : moduleFMapSheafOfUniv.{u} M g = moduleFMapSheaf M g := rfl

/-- **Composition with the `f`-map**, the transpose of postcomposition with the comparison map of
sheaves of modules.  It is defined at an arbitrary module universe, and it mentions no pullback. -/
noncomputable def fmapComp (M : SheafOfModules.{m} (crystallineStructureSheaf S)) (g : A ⟶ B)
    (Z : SheafOfModules.{m} A.ringRestrictionSheaf) :
    ((moduleRestrictionSheafFunctor.{m} A).obj M ⟶ Z) →
      ((moduleRestrictionSheafFunctor.{m} B).obj M ⟶
        (SheafOfModules.pushforward.{m} (ringRestrictionSheafFMap g)).obj Z) :=
  fun k ↦ moduleFMapSheafOfUniv M g ≫
    (SheafOfModules.pushforward.{m} (ringRestrictionSheafFMap g)).map k

/-- **Composition with the `f`-map is natural in the module**, contravariantly: this is
`Crystalline.GlobalCrystallineSituation.Thickening.moduleFMapSheaf_naturality` at an arbitrary
module universe. -/
theorem fmapComp_naturality {M N : SheafOfModules.{m} (crystallineStructureSheaf S)}
    (ψ : M ⟶ N) (g : A ⟶ B) (Z : SheafOfModules.{m} A.ringRestrictionSheaf)
    (k : (moduleRestrictionSheafFunctor.{m} A).obj N ⟶ Z) :
    fmapComp M g Z ((moduleRestrictionSheafFunctor.{m} A).map ψ ≫ k) =
      (moduleRestrictionSheafFunctor.{m} B).map ψ ≫ fmapComp N g Z k := by
  have h : (moduleRestrictionSheafFunctor.{m} B).map ψ ≫ moduleFMapSheafOfUniv N g =
      moduleFMapSheafOfUniv M g ≫
        (SheafOfModules.pushforward.{m} (ringRestrictionSheafFMap g)).map
          ((moduleRestrictionSheafFunctor.{m} A).map ψ) := by
    apply SheafOfModules.Hom.ext
    ext W x
    exact (PresheafOfModules.naturality_apply ψ.val (restrictOpenMap g W.unop).op x).symm
  simp only [fmapComp, Functor.map_comp]
  rw [← Category.assoc, ← h, Category.assoc]

/-- The transposition identity: composing with the `f`-map is the transpose of composing with the
comparison map of sheaves of modules. -/
theorem homEquiv_moduleComparisonSheaf_comp
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (g : A ⟶ B)
    (Z : SheafOfModules.{u} A.ringRestrictionSheaf) (k : moduleRestrictionSheaf M A ⟶ Z) :
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (ringRestrictionSheafFMap g)).homEquiv
        (moduleRestrictionSheaf M B) Z (moduleComparisonSheaf M g ≫ k) =
      fmapComp.{u} M g Z k := by
  rw [Adjunction.homEquiv_naturality_right, moduleComparisonSheaf, Equiv.apply_symm_apply]
  rfl

/-- **The crystal condition at a morphism, tested without the pullback.**  The comparison map
`c_f : f^* F_{T'} ⟶ F_T` of sheaves of `𝒪_T`-modules is an isomorphism exactly when, for every
sheaf of `𝒪_T`-modules `Z`, composing the `f`-map `F_{T'} ⟶ f_* F_T` with the pushforward of a
map `F_T ⟶ Z` is a bijection onto the maps `F_{T'} ⟶ f_* Z`.

Both sides of the equivalence are statements about the *same* morphism; what the right-hand side
buys is that it names no pullback functor, so it transfers along a universe lift of the module
sections, which the pullback does not. -/
theorem isIso_moduleComparisonSheaf_iff_bijective_fmapComp
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (g : A ⟶ B) :
    IsIso (moduleComparisonSheaf M g) ↔
      ∀ Z : SheafOfModules.{u} A.ringRestrictionSheaf,
        Function.Bijective (fmapComp.{u} M g Z) := by
  rw [isIso_iff_coyoneda_map_bijective]
  refine forall_congr' fun Z ↦ ?_
  have hE := Equiv.bijective ((SheafOfModules.pullbackPushforwardAdjunction.{u}
    (ringRestrictionSheafFMap g)).homEquiv (moduleRestrictionSheaf M B) Z)
  have hfun : (fun k : moduleRestrictionSheaf M A ⟶ Z ↦
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (ringRestrictionSheafFMap g)).homEquiv (moduleRestrictionSheaf M B) Z
            (moduleComparisonSheaf M g ≫ k)) = fmapComp.{u} M g Z :=
    funext fun k ↦ homEquiv_moduleComparisonSheaf_comp M g Z k
  rw [← hfun]
  exact (hE.of_comp_iff' _).symm

/-- A universe lift of the module sections is bijective on morphisms: the lift is full and
faithful. -/
theorem bijective_uliftForPresentationMap {C₁ : Type u₁} [Category.{v₁} C₁]
    {J : GrothendieckTopology C₁} {R : Sheaf J RingCat.{u}} (X Y : SheafOfModules.{u} R) :
    Function.Bijective fun k : X ⟶ Y ↦
      SheafOfModules.uliftForPresentationMap.{u₁, v₁, u, u, u + 1} k :=
  ⟨fun _ _ h ↦ SheafOfModules.uliftForPresentationMap_injective h,
    fun v ↦ ⟨SheafOfModules.uliftForPresentationMapDown v,
      SheafOfModules.uliftForPresentationMap_down v⟩⟩

/-- **Composition with the `f`-map at the raised module universe, read on the universe lifts of
the modules at the module universe `u`.**  This is
`Crystalline.GlobalCrystallineSituation.Thickening.fmapComp` at the module universe `u + 1`
applied to the lift of `N`; the point of naming it is that its source and target are written with
the lift *outside*, so that it composes with
`SheafOfModules.uliftForPresentationMap` without the elaborator having to reconcile the two
spellings each time.  The restriction to the ambient scheme and the pushforward along the map of
ambient schemes are computed on sections, so the two spellings agree. -/
noncomputable def fmapCompLift (N : SheafOfModules.{u} (crystallineStructureSheaf S))
    (g : A ⟶ B) (Z : SheafOfModules.{u} A.ringRestrictionSheaf) :
    (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
          ((moduleRestrictionSheafFunctor.{u} A).obj N) ⟶
        SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z) →
      (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
          ((moduleRestrictionSheafFunctor.{u} B).obj N) ⟶
        SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
          ((SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap g)).obj Z)) :=
  fmapComp.{u + 1} (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} N) g
    (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)

/-- **Composition with the `f`-map commutes with a universe lift of the module sections.**  The
restriction to the ambient scheme, the pushforward along the map of ambient schemes and the
`f`-map are all computed on sections, so lifting the sections of the module and of the target
commutes with all three; on sections both sides send a section to the lift of its image. -/
theorem fmapCompLift_uliftForPresentationMap
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (g : A ⟶ B)
    (Z : SheafOfModules.{u} A.ringRestrictionSheaf)
    (k : (moduleRestrictionSheafFunctor.{u} A).obj N ⟶ Z) :
    fmapCompLift N g Z (SheafOfModules.uliftForPresentationMap.{u, u, u, u, u + 1} k) =
      SheafOfModules.uliftForPresentationMap.{u, u, u, u, u + 1} (fmapComp.{u} N g Z k) := by
  apply SheafOfModules.Hom.ext
  ext W x
  rfl

/-- **Composition with the `f`-map is bijective exactly when its universe lift is.** -/
theorem bijective_fmapCompLift_iff (N : SheafOfModules.{u} (crystallineStructureSheaf S))
    (g : A ⟶ B) (Z : SheafOfModules.{u} A.ringRestrictionSheaf) :
    Function.Bijective (fmapCompLift N g Z) ↔ Function.Bijective (fmapComp.{u} N g Z) := by
  have h₁ := bijective_uliftForPresentationMap.{u, u, u}
    ((moduleRestrictionSheafFunctor.{u} A).obj N) Z
  have h₂ := bijective_uliftForPresentationMap.{u, u, u}
    ((moduleRestrictionSheafFunctor.{u} B).obj N)
    ((SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap g)).obj Z)
  have hsq : (fmapCompLift N g Z) ∘
        (fun k : (moduleRestrictionSheafFunctor.{u} A).obj N ⟶ Z ↦
          SheafOfModules.uliftForPresentationMap.{u, u, u, u, u + 1} k) =
      (fun k ↦ SheafOfModules.uliftForPresentationMap.{u, u, u, u, u + 1} k) ∘
        (fmapComp.{u} N g Z) :=
    funext fun k ↦ fmapCompLift_uliftForPresentationMap N g Z k
  constructor
  · intro h
    refine (h₂.of_comp_iff' _).1 ?_
    rw [← hsq]
    exact h.comp h₁
  · intro h
    refine (Function.Bijective.of_comp_iff _ h₁).1 ?_
    rw [hsq]
    exact h₂.comp h

/-- **Composition with the `f`-map is bijective at the structure sheaf**, at the raised module
universe: the comparison map of `𝒪_{X/S}` is an isomorphism, by
`Crystalline.GlobalCrystallineSituation.Thickening.isIso_moduleComparisonSheaf_unit`. -/
theorem bijective_fmapCompLift_unit (g : A ⟶ B)
    (Z : SheafOfModules.{u} A.ringRestrictionSheaf) :
    Function.Bijective
      (fmapCompLift (SheafOfModules.unit (crystallineStructureSheaf S)) g Z) :=
  (bijective_fmapCompLift_iff _ g Z).2
    ((isIso_moduleComparisonSheaf_iff_bijective_fmapComp _ g).1
      (isIso_moduleComparisonSheaf_unit g) Z)

/-- Composition with the `f`-map at the raised universe, in its own spelling and in the spelling
`Crystalline.GlobalCrystallineSituation.Thickening.fmapCompLift` gives it, are the same map. -/
theorem bijective_fmapComp_uliftForPresentation_iff
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (g : A ⟶ B)
    (Z : SheafOfModules.{u} A.ringRestrictionSheaf) :
    Function.Bijective (fmapComp.{u + 1}
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} N) g
        (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)) ↔
      Function.Bijective (fmapCompLift N g Z) :=
  Iff.rfl

/-- **A globally presented sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)` has bijective `f`-map
composition.**

This is the computation the source of [Stacks, Tag 07IT] performs for the implication
(1) ⇒ (2)(b): a presentation `⊕_J 𝒪_{X/S} → ⊕_I 𝒪_{X/S} → F → 0` "gives a presentation" of `F_T`
and "restricts to `T'` to give a similar presentation of `F_{T'}`", whence `c_f` is an
isomorphism.  Restriction to the ambient scheme preserves the coproducts and the cokernel, being
a pushforward along a continuous *and cocontinuous* functor, and composition with the `f`-map is
bijective at `𝒪_{X/S}`; the two abstract steps are
`Stacks.PresentedBijectivity.bijective_of_cofan` and
`Stacks.PresentedBijectivity.bijective_of_cofork`. -/
theorem bijective_fmapCompLift_of_hasGlobalPresentation
    (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    (hM : M.HasGlobalPresentation) (g : A ⟶ B)
    (Z : SheafOfModules.{u} A.ringRestrictionSheaf) :
    Function.Bijective (fmapCompLift M g Z) := by
  have hA := preservesColimitsOfSize_moduleRestrictionSheafFunctor.{u} A
  have hB := preservesColimitsOfSize_moduleRestrictionSheafFunctor.{u} B
  have hshrink : ∀ C : Thickening S, PreservesColimitsOfSize.{0, 0}
      (show SheafOfModules.{u + 1} (crystallineStructureSheaf S) ⥤
        SheafOfModules.{u + 1} C.ringRestrictionSheaf from
          moduleRestrictionSheafFunctor.{u + 1} C) := fun C ↦
    have := preservesColimitsOfSize_moduleRestrictionSheafFunctor.{u} C
    preservesColimitsOfSize_shrink _
  refine (bijective_fmapComp_uliftForPresentation_iff M g Z).1 ?_
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hcoker⟩⟩ := hM
  have hθ : ∀ {M' N' : SheafOfModules.{u + 1} (crystallineStructureSheaf S)} (ψ : M' ⟶ N')
      (k : (moduleRestrictionSheafFunctor.{u + 1} A).obj N' ⟶
        SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z),
      fmapComp.{u + 1} M' g (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)
          ((moduleRestrictionSheafFunctor.{u + 1} A).map ψ ≫ k) =
        (moduleRestrictionSheafFunctor.{u + 1} B).map ψ ≫
          fmapComp.{u + 1} N' g (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z) k :=
    fun ψ k ↦ fmapComp_naturality ψ g _ k
  have hunit : Function.Bijective (fmapComp.{u + 1}
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
        (SheafOfModules.unit (crystallineStructureSheaf S))) g
      (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)) :=
    (bijective_fmapComp_uliftForPresentation_iff _ g Z).2 (bijective_fmapCompLift_unit g Z)
  have hcofan : ∀ {I : Type (u + 1)} {U N : SheafOfModules.{u + 1} (crystallineStructureSheaf S)}
      (ι : I → (U ⟶ N)), IsColimit (Cofan.mk (f := fun _ : I ↦ U) N ι) →
      Function.Bijective (fmapComp.{u + 1} U g
        (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)) →
      Function.Bijective (fmapComp.{u + 1} N g
        (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)) :=
    fun ι h ↦ Stacks.PresentedBijectivity.bijective_of_cofan hθ ι
      ((Cofan.isColimitMapCoconeEquiv (moduleRestrictionSheafFunctor.{u + 1} A) _
        (Cofan.mk _ ι)) (isColimitOfPreserves _ h))
      ((Cofan.isColimitMapCoconeEquiv (moduleRestrictionSheafFunctor.{u + 1} B) _
        (Cofan.mk _ ι)) (isColimitOfPreserves _ h))
  have hQbij := hcofan κ hQ hunit
  have hab' : a ≫ b = 0 ≫ b := by rw [hab, zero_comp]
  exact Stacks.PresentedBijectivity.bijective_of_cofork hθ
    (isColimitMapCoconeCoforkEquiv (moduleRestrictionSheafFunctor.{u + 1} A) hab'
      (isColimitOfPreserves _ hcoker))
    (isColimitMapCoconeCoforkEquiv (moduleRestrictionSheafFunctor.{u + 1} B) hab'
      (isColimitOfPreserves _ hcoker)) (hcofan ι hP hunit) hQbij.1

/-- **Stacks Project, Tag 07IT, the implication (1) ⇒ (2)(b) for a globally presented module:** a
sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)` with a global presentation is a crystal in
`𝒪_{X/S}`-modules.  The crystal condition is tested through
`isIso_moduleComparisonSheaf_iff_bijective_fmapComp`, which names no pullback and therefore
survives the universe lift of the module sections at which a global presentation on a crystalline
site lives. -/
theorem isSheafCrystal_of_hasGlobalPresentation
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (hM : M.HasGlobalPresentation) :
    IsSheafCrystal M := fun _ _ g ↦
  (isIso_moduleComparisonSheaf_iff_bijective_fmapComp M g).2 fun Z ↦
    (bijective_fmapCompLift_iff M g Z).1
      (bijective_fmapCompLift_of_hasGlobalPresentation M hM g Z)

end Crystalline.GlobalCrystallineSituation.Thickening

end
