module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalCocycle
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiGluing

/-!
# Locality of the canonical base change relation, and glueing a morphism of pullbacks

Let `q : W ⟶ Z` and `g : Z ⟶ X` be morphisms of schemes with `q ≫ g = pi`.  The relation
`Stacks.AlgebraicGeometry.ModuleLimits.IsCanonicalBaseChange` — the conclusion of
[Stacks Project, Tag 01ZR] (2) — asserts an equality of morphisms of sheaves of modules on `W`,
so it is local on `W`; and the morphism it asserts the base change of can itself be assembled
from local data on `Z`.  This file supplies both halves, which is what a local-to-global argument
for Tag 01ZR (2) consumes.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.canUnconj`: the inverse of
  `Stacks.AlgebraicGeometry.ModuleLimits.canConj` — a morphism of pullbacks along the composite
  read, through the canonical identification, as a morphism of iterated pullbacks.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.canConj_canConj'` and `...canConj_canConj`: reading a
  morphism through the canonical identifications of a chain `L ⟶ W ⟶ Z ⟶ X` is associative.
  This is the cocycle `Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp_canHom` read on
  morphisms, and it is the only coherence a local-to-global argument needs.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isCanonicalBaseChange_of_stage_factor`: pushing
  the stage and factoring the morphism the modules are pulled back along, in one step.
* `Stacks.AlgebraicGeometry.ModuleLimits.isCanonicalBaseChange_restrict` and
  `...isCanonicalBaseChange_of_forall_cover`: the canonical base change relation restricts to an
  open subscheme of `W`, and holds as soon as it holds over every member of an open covering
  of `W`.
* `Stacks.AlgebraicGeometry.ModuleLimits.existsUnique_pullback_map_eq_of_cover` and
  `...existsUnique_pullback_map_eq_of_opens_cover`: **the glueing.**  A family of morphisms of
  the pullbacks along a family of open immersions covering a scheme, agreeing over the opens
  lying in two members, is the family of pullbacks of a unique morphism on the base.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isCanonicalBaseChange_of_opens_cover`: **the
  glueing, for the canonical base change relation.**  Local pieces of a morphism of pullbacks
  along `g : Z ⟶ X`, given over the members of an open covering of `Z` and agreeing over the
  opens lying in two members, come from a morphism of the pullbacks along `g`.
* `Stacks.AlgebraicGeometry.ModuleLimits.locApp_canConj`: the map on sections carried by a
  morphism of pullbacks along an open immersion does not change under pulling back.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctor_map_eq_iff`: a morphism of the
  restrictions to an open subscheme is the restriction of a morphism on the base exactly when a
  square of maps on sections commutes, the comparison being the unit of
  `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`.

## Implementation notes

The glueing is `Stacks.Descent.existsUnique_hom_of_locally` — the Zariski glueing of a morphism
of sheaves of modules already in the library — fed with
`Stacks.Descent.locApp`, the map on sections over an open contained in the range of an open
immersion carried by a morphism of pullbacks along it.  Phrasing the local data as morphisms of
*pullbacks* rather than as morphisms of `AlgebraicGeometry.Scheme.Modules.restrictFunctor`s is
what keeps the whole argument inside the `canConj` calculus of
`StacksFrontier/AlgebraicGeometry/ModuleLimits/CanonicalCocycle.lean`: no comparison between the
pullback along an open immersion and the restriction functor is ever needed, and in particular
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, which is built from
`CategoryTheory.Adjunction.leftAdjointUniq` and has no formula on sections, appears only inside
`Stacks.Descent.isIso_unitApp`, where the library has already dealt with it.

Every equation between composites of morphisms of schemes is carried as an explicit hypothesis,
as in `CanonicalCocycle.lean`: the statements below are applied to composites presented under
several different names, and a hypothesis is the only way to keep the conclusion's `canConj` at
the name the caller has chosen.

## References

* [Stacks Project, Tag 00AK](https://stacks.math.columbia.edu/tag/00AK)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Scheme.Modules

/-! ### The canonical identification along a composite, and the inverse of `canConj` -/

section Can

variable {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X)

/-- For the composite itself the canonical identification is `pullbackComp`. -/
theorem canIso_rfl (F : X.Modules) :
    canIso q g (q ≫ g) rfl F = (Scheme.Modules.pullbackComp q g).app F :=
  Iso.ext ((canIso_hom q g (q ≫ g) rfl F).trans (canHom_rfl q g F))

variable (pi : W ⟶ X) (hpi : q ≫ g = pi)

/-- **The inverse of `Stacks.AlgebraicGeometry.ModuleLimits.canConj`**: a morphism of the
pullbacks along the composite `pi`, read through the canonical identification attached to
`q ≫ g = pi` as a morphism of the iterated pullbacks. -/
noncomputable def canUnconj {F G : X.Modules}
    (ψ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G) :
    (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F) ⟶
      (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj G) :=
  canHom q g pi hpi F ≫ ψ ≫ (canIso q g pi hpi G).inv

/-- `canUnconj` is a right inverse of `canConj`. -/
@[simp]
theorem canConj_canUnconj {F G : X.Modules}
    (ψ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G) :
    canConj q g pi hpi (canUnconj q g pi hpi ψ) = ψ := by
  simp [canConj, canUnconj, ← canIso_hom]

/-- `canUnconj` is a left inverse of `canConj`. -/
@[simp]
theorem canUnconj_canConj {F G : X.Modules}
    (χ : (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj F) ⟶
      (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj G)) :
    canUnconj q g pi hpi (canConj q g pi hpi χ) = χ := by
  simp [canConj, canUnconj, ← canIso_hom]

/-- Reading a morphism of iterated pullbacks through the canonical identification is injective. -/
theorem canConj_injective {F G : X.Modules} :
    Function.Injective (canConj q g pi hpi (F := F) (G := G)) := fun χ₁ χ₂ h => by
  rw [← canUnconj_canConj q g pi hpi χ₁, h, canUnconj_canConj]

/-- Two morphisms of pullbacks along the composite that are both the canonical base change of the
same morphism at the stage are equal. -/
theorem eq_of_isCanonicalBaseChange {F G : X.Modules}
    {χ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G}
    {φ₁ φ₂ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G}
    (h₁ : IsCanonicalBaseChange q g pi hpi χ φ₁)
    (h₂ : IsCanonicalBaseChange q g pi hpi χ φ₂) : φ₁ = φ₂ :=
  (cancel_epi (canHom q g pi hpi F)).mp (h₁.symm.trans h₂)

end Can

/-! ### The two ways of reading a morphism through a chain of canonical identifications -/

/-- **Reading a morphism through the canonical identifications of a chain is associative.**  For
`L ⟶ W ⟶ Z ⟶ X` the two ways of turning a morphism of the triply iterated pullbacks into a
morphism of the pullbacks along the total composite agree.  This is the cocycle
`Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp_canHom` read on morphisms. -/
theorem canConj_canConj' {L W Z X : Scheme.{u}} (p : L ⟶ W) (t : W ⟶ Z) (s : Z ⟶ X)
    (pw : L ⟶ Z) (h1 : p ≫ t = pw) (ts : W ⟶ X) (h3 : t ≫ s = ts)
    (pz : L ⟶ X) (h2 : pw ≫ s = pz) (h4 : p ≫ ts = pz) {F G : X.Modules}
    (χ : (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback s).obj F) ⟶
      (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback s).obj G)) :
    canConj p ts pz h4 ((Scheme.Modules.pullback p).map (canConj t s ts h3 χ))
      = canConj pw s pz h2 (canConj p t pw h1 ((Scheme.Modules.pullback p).map χ)) := by
  have hinv : ∀ K : X.Modules,
      (canIso p ts pz h4 K).inv ≫
          (Scheme.Modules.pullback p).map (canIso t s ts h3 K).inv
        = (canIso pw s pz h2 K).inv ≫
          (canIso p t pw h1 ((Scheme.Modules.pullback s).obj K)).inv := by
    intro K
    have hiso : (Scheme.Modules.pullback p).mapIso (canIso t s ts h3 K) ≪≫ canIso p ts pz h4 K
        = canIso p t pw h1 ((Scheme.Modules.pullback s).obj K) ≪≫ canIso pw s pz h2 K := by
      refine Iso.ext ?_
      simp only [Iso.trans_hom, Functor.mapIso_hom, canIso_hom]
      exact (canHom_comp_canHom p t s pw h1 ts h3 pz h2 h4 K).symm
    simpa only [Iso.trans_inv, Functor.mapIso_inv] using congrArg Iso.inv hiso
  simp only [canConj, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (hinv F), canHom_comp_canHom p t s pw h1 ts h3 pz h2 h4 G]

/-- **Reading a morphism from the base through the canonical identifications of a chain.**  For
`L ⟶ W ⟶ Z ⟶ X` and a morphism of the pullbacks along `s`, restricting to `W` and then to `L`
agrees with restricting to `L` in one step. -/
theorem canConj_canConj {L W Z X : Scheme.{u}} (p : L ⟶ W) (t : W ⟶ Z) (s : Z ⟶ X)
    (pw : L ⟶ Z) (h1 : p ≫ t = pw) (ts : W ⟶ X) (h3 : t ≫ s = ts)
    (pz : L ⟶ X) (h2 : pw ≫ s = pz) (h4 : p ≫ ts = pz) {F G : X.Modules}
    (χ : (Scheme.Modules.pullback s).obj F ⟶ (Scheme.Modules.pullback s).obj G) :
    canConj p ts pz h4
          ((Scheme.Modules.pullback p).map (canConj t s ts h3
            ((Scheme.Modules.pullback t).map χ)))
      = canConj pw s pz h2 ((Scheme.Modules.pullback pw).map χ) :=
  (isCanonicalBaseChange_iff p ts pz h4 _ _).mp
    ((isCanonicalBaseChange_stage_iff p t s pw h1 ts h3 pz h2 h4 χ _).mpr
      ((isCanonicalBaseChange_iff pw s pz h2 χ _).mpr rfl))

/-- **Pushing the stage and factoring the morphism in one step.**  Let
`L ⟶ M ⟶ N ⟶ Y ⟶ X` be a chain with every composite supplied as a hypothesis.  A morphism of
the pullbacks along `N ⟶ Y` of the pullbacks to `Y` of two modules on `X`, whose canonical base
change along `L ⟶ N` is the morphism attached to `ψ` by the canonical identification, gives a
morphism of the pullbacks along `M ⟶ X` whose canonical base change along `L ⟶ M` is `ψ`.

This is `Stacks.AlgebraicGeometry.ModuleLimits.isCanonicalBaseChange_stage_iff` followed by
`Stacks.AlgebraicGeometry.ModuleLimits.isCanonicalBaseChange_factor_iff`; it is stated as one
lemma because the two are always applied together, and in the only shape in which they are. -/
theorem exists_isCanonicalBaseChange_of_stage_factor {L M N Y X : Scheme.{u}} (p : L ⟶ M)
    (t : M ⟶ N) (s : N ⟶ Y) (g₂ : Y ⟶ X) (pw : L ⟶ N) (h1 : p ≫ t = pw) (ts : M ⟶ Y)
    (h3 : t ≫ s = ts) (pz : L ⟶ Y) (h2 : pw ≫ s = pz) (h4 : p ≫ ts = pz) (tsX : M ⟶ X)
    (hg : ts ≫ g₂ = tsX) (pzX : L ⟶ X) (hpi : pz ≫ g₂ = pzX) (hq : p ≫ tsX = pzX)
    {F G : X.Modules}
    (χ : (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback g₂).obj F) ⟶
      (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback g₂).obj G))
    (ψ : (Scheme.Modules.pullback pzX).obj F ⟶ (Scheme.Modules.pullback pzX).obj G)
    (h : IsCanonicalBaseChange pw s pz h2 χ (canUnconj pz g₂ pzX hpi ψ)) :
    ∃ X' : (Scheme.Modules.pullback tsX).obj F ⟶ (Scheme.Modules.pullback tsX).obj G,
      IsCanonicalBaseChange p tsX pzX hq X' ψ := by
  have hstage := (isCanonicalBaseChange_stage_iff p t s pw h1 ts h3 pz h2 h4 χ _).mpr h
  have hfactor := (isCanonicalBaseChange_factor_iff p ts g₂ tsX hg pz h4 pzX hpi hq
    (F := F) (G := G) (canConj t s ts h3 ((Scheme.Modules.pullback t).map χ))
    (canUnconj pz g₂ pzX hpi ψ)).mpr hstage
  rw [canConj_canUnconj] at hfactor
  exact ⟨_, hfactor⟩

/-! ### Pushing the relation to a later stage of a diagram -/

/-- **The canonical base change relation is inherited by a later stage.**  If `χ`, a morphism of
the pullbacks along `E.map w` to a stage `k₁`, has `ϕ` as its canonical base change to the vertex
of a cone, then its pullback to a stage `k₂` over `k₁`, read through the canonical
identification, has `ϕ` as its canonical base change as well.

This is `Stacks.AlgebraicGeometry.ModuleLimits.isCanonicalBaseChange_stage_iff` with the
factorisation of the transition morphism supplied by functoriality. -/
theorem isCanonicalBaseChange_push_stage {J : Type*} [Category J] {E : J ⥤ Scheme.{u}}
    (cn : Cone E) {k₂ k₁ o : J} (v : k₂ ⟶ k₁) (w : k₁ ⟶ o) (w' : k₂ ⟶ o) (hw : v ≫ w = w')
    {A B : (E.obj o).Modules}
    {χ : (Scheme.Modules.pullback (E.map w)).obj A ⟶ (Scheme.Modules.pullback (E.map w)).obj B}
    {ϕ : (Scheme.Modules.pullback (cn.π.app o)).obj A ⟶
      (Scheme.Modules.pullback (cn.π.app o)).obj B}
    (h : IsCanonicalBaseChange (cn.π.app k₁) (E.map w) (cn.π.app o) (cn.w w) χ ϕ) :
    IsCanonicalBaseChange (cn.π.app k₂) (E.map w') (cn.π.app o) (cn.w w')
      (canConj (E.map v) (E.map w) (E.map w') (by rw [← E.map_comp, hw])
        ((Scheme.Modules.pullback (E.map v)).map χ)) ϕ :=
  (isCanonicalBaseChange_stage_iff (cn.π.app k₂) (E.map v) (E.map w) (cn.π.app k₁) (cn.w v)
    (E.map w') (by rw [← E.map_comp, hw]) (cn.π.app o) (cn.w w) (cn.w w') χ ϕ).mpr h

/-! ### Locality of the relation on the stage -/

section Local

variable {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X) (hpi : q ≫ g = pi)
  {ι : Type*} (O : ι → W.Opens)

/-- **The canonical base change relation restricts to an open subscheme of the stage.**  This is
`Stacks.AlgebraicGeometry.ModuleLimits.isCanonicalBaseChange_restrict_iff` in the direction that
is used going down. -/
theorem isCanonicalBaseChange_restrict {W' : Scheme.{u}} (j : W' ⟶ W) (q' : W' ⟶ Z)
    (hq' : j ≫ q = q') (pi' : W' ⟶ X) (hpi' : j ≫ pi = pi') (hq'' : q' ≫ g = pi')
    {F G : X.Modules}
    {χ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G}
    {φ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G}
    (h : IsCanonicalBaseChange q g pi hpi χ φ) :
    IsCanonicalBaseChange q' g pi' hq'' χ
      (canConj j pi pi' hpi' ((Scheme.Modules.pullback j).map φ)) :=
  (isCanonicalBaseChange_restrict_iff j q g pi hpi q' hq' pi' hpi' hq'' χ φ).mp
    (congrArg (Scheme.Modules.pullback j).map h)

/-- **The canonical base change relation is local on the stage.**  If the relation holds over
every member of an open covering of `W`, it holds over `W`.

Equality of morphisms of sheaves of modules is local
(`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover`), and the restriction of the
canonical equation to an open is the canonical equation over that open
(`Stacks.AlgebraicGeometry.ModuleLimits.isCanonicalBaseChange_restrict_iff`). -/
theorem isCanonicalBaseChange_of_forall_cover (hO : ∀ x : W, ∃ a, x ∈ O a)
    (q' : ∀ a, (O a).toScheme ⟶ Z) (hq' : ∀ a, (O a).ι ≫ q = q' a)
    (pi' : ∀ a, (O a).toScheme ⟶ X) (hpi' : ∀ a, (O a).ι ≫ pi = pi' a)
    (hq'' : ∀ a, q' a ≫ g = pi' a) {F G : X.Modules}
    {χ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G}
    {φ : (Scheme.Modules.pullback pi).obj F ⟶ (Scheme.Modules.pullback pi).obj G}
    (h : ∀ a, IsCanonicalBaseChange (q' a) g (pi' a) (hq'' a) χ
      (canConj (O a).ι pi (pi' a) (hpi' a) ((Scheme.Modules.pullback (O a).ι).map φ))) :
    IsCanonicalBaseChange q g pi hpi χ φ := by
  refine hom_ext_of_restrict_cover O hO fun a => ?_
  refine map_eq_of_natIso (Scheme.Modules.restrictFunctorIsoPullback (O a).ι).symm ?_
  exact (isCanonicalBaseChange_restrict_iff (O a).ι q g pi hpi (q' a) (hq' a) (pi' a) (hpi' a)
    (hq'' a) χ φ).mpr (h a)

end Local

/-! ### Glueing a morphism of pullbacks along an open covering -/

section Glue

variable {S : Scheme.{u}} {M N : S.Modules}

/-- `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` of
`AlgebraicGeometry.modulePullbackPseudofunctor`, for a factorisation given by an equation, is
`Stacks.AlgebraicGeometry.ModuleLimits.canConj` of the pullback. -/
theorem pullHom_eq_canConj {T T' : Scheme.{u}} (f : T ⟶ S) (h : T' ⟶ T) (f' : T' ⟶ S)
    (hf' : h ≫ f = f')
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := modulePullbackPseudofunctor)
        (M₁ := M) (M₂ := N) (f₁ := f) (f₂ := f) φ h f' f' hf' hf'
      = canConj h f f' hf' ((Scheme.Modules.pullback h).map φ) := by
  subst hf'
  rw [Stacks.Descent.pullHom_eq, canConj, canIso_rfl, canHom_rfl]
  rfl

/-- **The map on sections carried by a morphism of pullbacks does not change under pulling
back.**  This is `Stacks.Descent.locApp_pullHom` with
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` written as `canConj`. -/
theorem locApp_canConj {T T' : Scheme.{u}} (f : T ⟶ S) [IsOpenImmersion f] (h : T' ⟶ T)
    (f' : T' ⟶ S) [IsOpenImmersion f'] (hf' : h ≫ f = f')
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (V : S.Opens) (hV : V ≤ f'.opensRange) (hVf : V ≤ f.opensRange) :
    Stacks.Descent.locApp f' (canConj h f f' hf' ((Scheme.Modules.pullback h).map φ)) V hV
      = Stacks.Descent.locApp f φ V hVf := by
  rw [← pullHom_eq_canConj, Stacks.Descent.locApp_pullHom f h f' hf' φ V hV hVf]

/-- **A morphism of the restrictions to an open subscheme is the restriction of a morphism on the
base exactly when a square of maps on sections commutes.**  For an open immersion `f : T ⟶ S` and
`φ : M ⟶ N`, the restriction of `φ` along `f` is `ζ` precisely when, for every open `U` of `S`,
the two ways of going from `Γ(M, U)` to `Γ(N, f ''ᵁ (f ⁻¹ᵁ U))` — apply `φ` and restrict, or
restrict and apply `ζ` — agree.

The comparison morphism is the unit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`,
which on sections is a restriction map of the presheaf
(`AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app`); the statement is that unit's
adjunction bijection written out. -/
theorem restrictFunctor_map_eq_iff {T : Scheme.{u}} (f : T ⟶ S) [IsOpenImmersion f]
    (φ : M ⟶ N)
    (ζ : (Scheme.Modules.restrictFunctor f).obj M ⟶ (Scheme.Modules.restrictFunctor f).obj N) :
    (Scheme.Modules.restrictFunctor f).map φ = ζ ↔
      ∀ (U : S.Opens) (m : Γ(M, U)),
        N.presheaf.map (homOfLE (f.image_preimage_le U)).op (φ.app U m)
          = ζ.app (f ⁻¹ᵁ U) (M.presheaf.map (homOfLE (f.image_preimage_le U)).op m) := by
  have hequiv : ∀ (ψ : (Scheme.Modules.restrictFunctor f).obj M ⟶
        (Scheme.Modules.restrictFunctor f).obj N) (U : S.Opens) (m : Γ(M, U)),
      ((Scheme.Modules.restrictAdjunction f).homEquiv M
            ((Scheme.Modules.restrictFunctor f).obj N) ψ).app U m
        = ψ.app (f ⁻¹ᵁ U) (M.presheaf.map (homOfLE (f.image_preimage_le U)).op m) := by
    intro ψ U m
    rw [Adjunction.homEquiv_unit]
    rfl
  have hφ : ∀ (U : S.Opens) (m : Γ(M, U)),
      N.presheaf.map (homOfLE (f.image_preimage_le U)).op (φ.app U m)
        = ((Scheme.Modules.restrictAdjunction f).homEquiv M
            ((Scheme.Modules.restrictFunctor f).obj N)
            ((Scheme.Modules.restrictFunctor f).map φ)).app U m := by
    intro U m
    rw [hequiv, Hom_app_presheaf_map φ (f.image_preimage_le U) m]
    rfl
  refine ⟨fun h U m => by rw [hφ U m, h, hequiv], fun h => ?_⟩
  refine ((Scheme.Modules.restrictAdjunction f).homEquiv M
    ((Scheme.Modules.restrictFunctor f).obj N)).injective ?_
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext m
  rw [← hφ U m, h U m, hequiv]

variable {ι : Type*} {Y : ι → Scheme.{u}}

/-- **Glueing a morphism of pullbacks along an open covering.**  Let `f a : Y a ⟶ S` be a family
of open immersions whose images cover `S` and let `φ a` be a morphism of the pullbacks along
`f a` of two sheaves of modules on `S`.  If any two members carry the same map on sections over
every open of `S` contained in both of their images, then there is a unique morphism `M ⟶ N`
whose pullback along `f a` is `φ a` for every `a`.

This is `Stacks.Descent.existsUnique_hom_of_locally` — the Zariski glueing of a morphism of
sheaves of modules — applied to the family of maps on sections `Stacks.Descent.locApp` attached
to the `φ a`. -/
theorem existsUnique_pullback_map_eq_of_cover (f : ∀ a, Y a ⟶ S) [∀ a, IsOpenImmersion (f a)]
    (hf : ⨆ a, (f a).opensRange = ⊤)
    (φ : ∀ a, (Scheme.Modules.pullback (f a)).obj M ⟶ (Scheme.Modules.pullback (f a)).obj N)
    (hagree : ∀ (a b : ι) (V : S.Opens) (ha : V ≤ (f a).opensRange) (hb : V ≤ (f b).opensRange),
      Stacks.Descent.locApp (f a) (φ a) V ha = Stacks.Descent.locApp (f b) (φ b) V hb) :
    ∃! θ : M ⟶ N, ∀ a, (Scheme.Modules.pullback (f a)).map θ = φ a := by
  obtain ⟨θ, hθ, huniq⟩ := Stacks.Descent.existsUnique_hom_of_locally (M := M) (N := N)
    (U := fun a => (f a).opensRange) hf (fun a V hV => Stacks.Descent.locApp (f a) (φ a) V hV)
    (fun a => Stacks.Descent.locApp_naturality (f a) (φ a))
    (fun a b V ha hb x => ConcreteCategory.congr_hom (hagree a b V ha hb) x)
    (fun a => Stacks.Descent.locApp_smul (f a) (φ a))
  have key : ∀ (ψ : M ⟶ N) (a : ι), (Scheme.Modules.pullback (f a)).map ψ = φ a ↔
      ∀ (V : S.Opens) (hV : V ≤ (f a).opensRange) (x : Γ(M, V)),
        ψ.app V x = Stacks.Descent.locApp (f a) (φ a) V hV x := by
    intro ψ a
    refine ⟨fun hψ V hV x => ?_, fun hψ => ?_⟩
    · refine Stacks.Descent.unitApp_injective (f a) N V hV ?_
      rw [Stacks.Descent.unitApp_locApp, ← hψ, Stacks.Descent.descHom_map]
      rfl
    · refine Stacks.Descent.descHom_injective (f a)
        ((Stacks.Descent.descHom_map (f a) ψ).trans ?_)
      refine Stacks.Descent.hom_ext_of_le_opensRange (f a) fun V hV => ?_
      refine ConcreteCategory.hom_ext _ _ fun x => ?_
      exact (congrArg (Stacks.Descent.unitApp (f a) N V) (hψ V hV x)).trans
        (Stacks.Descent.unitApp_locApp (f a) (φ a) V hV x)
  exact ⟨θ, fun a => (key θ a).mpr (hθ a), fun ψ hψ => huniq ψ fun a => (key ψ a).mp (hψ a)⟩

/-- **Glueing a morphism of restrictions along a covering family of opens.**  This is
`existsUnique_pullback_map_eq_of_cover` for the inclusions of a family of opens covering the
scheme, with the compatibility condition phrased through
`Stacks.AlgebraicGeometry.ModuleLimits.canConj` rather than on sections. -/
theorem existsUnique_pullback_map_eq_of_opens_cover (O : ι → S.Opens) (hO : ⨆ a, O a = ⊤)
    (φ : ∀ a, (Scheme.Modules.pullback (O a).ι).obj M ⟶ (Scheme.Modules.pullback (O a).ι).obj N)
    (hagree : ∀ (a b : ι) (V : S.Opens) (ha : V ≤ O a) (hb : V ≤ O b),
      canConj (S.homOfLE ha) (O a).ι V.ι (S.homOfLE_ι ha)
            ((Scheme.Modules.pullback (S.homOfLE ha)).map (φ a))
        = canConj (S.homOfLE hb) (O b).ι V.ι (S.homOfLE_ι hb)
            ((Scheme.Modules.pullback (S.homOfLE hb)).map (φ b))) :
    ∃! θ : M ⟶ N, ∀ a, (Scheme.Modules.pullback (O a).ι).map θ = φ a := by
  have hrange : ∀ a : ι, ((O a).ι).opensRange = O a := fun a => Scheme.Opens.opensRange_ι _
  refine existsUnique_pullback_map_eq_of_cover (fun a => (O a).ι) (by simpa only [hrange] using hO)
    φ fun a b V ha hb => ?_
  have ha' : V ≤ O a := by rwa [hrange] at ha
  have hb' : V ≤ O b := by rwa [hrange] at hb
  have hVV : V ≤ V.ι.opensRange := by rw [Scheme.Opens.opensRange_ι]
  rw [← locApp_canConj (O a).ι (S.homOfLE ha') V.ι (S.homOfLE_ι ha') (φ a) V hVV ha,
    ← locApp_canConj (O b).ι (S.homOfLE hb') V.ι (S.homOfLE_ι hb') (φ b) V hVV hb,
    hagree a b V ha' hb']

end Glue

/-! ### Glueing the canonical base change relation -/

/-- **Glueing the canonical base change relation along an open covering of the stage.**  Let
`g : Z ⟶ X` be a morphism of schemes, let `O` be a family of opens covering `Z` and let
`ts a : O a ⟶ X` factor the composite `(O a).ι ≫ g`.  Given, over each member, a morphism `Y a`
of the pullbacks along `ts a` of two sheaves of modules on `X`, and given that any two members
restrict to the same morphism over every open contained in both, there is a morphism of the
pullbacks along `g` whose canonical base change to `O a` is `Y a` for every `a`.

The data `Y a` is the local form of the morphism being descended: `Y a` is a morphism of modules
on the open `O a` of `Z` pulled back from `X`, and the conclusion says that the glued morphism
restricts to it. -/
theorem exists_isCanonicalBaseChange_of_opens_cover {Z X : Scheme.{u}} (g : Z ⟶ X)
    {F G : X.Modules} {ι : Type*} (O : ι → Z.Opens) (hO : ⨆ a, O a = ⊤)
    (ts : ∀ a, (O a).toScheme ⟶ X) (hts : ∀ a, (O a).ι ≫ g = ts a)
    (Y : ∀ a, (Scheme.Modules.pullback (ts a)).obj F ⟶ (Scheme.Modules.pullback (ts a)).obj G)
    (hagree : ∀ (a b : ι) (V : Z.Opens) (ha : V ≤ O a) (hb : V ≤ O b),
      canConj (Z.homOfLE ha) (ts a) (V.ι ≫ g)
            (by rw [← hts a, ← Category.assoc, Z.homOfLE_ι])
            ((Scheme.Modules.pullback (Z.homOfLE ha)).map (Y a))
        = canConj (Z.homOfLE hb) (ts b) (V.ι ≫ g)
            (by rw [← hts b, ← Category.assoc, Z.homOfLE_ι])
            ((Scheme.Modules.pullback (Z.homOfLE hb)).map (Y b))) :
    ∃ θ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G,
      ∀ a, IsCanonicalBaseChange (O a).ι g (ts a) (hts a) θ (Y a) := by
  have hagree' : ∀ (a b : ι) (V : Z.Opens) (ha : V ≤ O a) (hb : V ≤ O b),
      canConj (Z.homOfLE ha) (O a).ι V.ι (Z.homOfLE_ι ha)
            ((Scheme.Modules.pullback (Z.homOfLE ha)).map
              (canUnconj (O a).ι g (ts a) (hts a) (Y a)))
        = canConj (Z.homOfLE hb) (O b).ι V.ι (Z.homOfLE_ι hb)
            ((Scheme.Modules.pullback (Z.homOfLE hb)).map
              (canUnconj (O b).ι g (ts b) (hts b) (Y b))) := by
    intro a b V ha hb
    refine canConj_injective V.ι g (V.ι ≫ g) rfl ?_
    rw [← canConj_canConj' (Z.homOfLE ha) (O a).ι g V.ι (Z.homOfLE_ι ha) (ts a) (hts a)
        (V.ι ≫ g) rfl (by rw [← hts a, ← Category.assoc, Z.homOfLE_ι]),
      ← canConj_canConj' (Z.homOfLE hb) (O b).ι g V.ι (Z.homOfLE_ι hb) (ts b) (hts b)
        (V.ι ≫ g) rfl (by rw [← hts b, ← Category.assoc, Z.homOfLE_ι]),
      canConj_canUnconj, canConj_canUnconj]
    exact hagree a b V ha hb
  obtain ⟨θ, hθ, -⟩ := existsUnique_pullback_map_eq_of_opens_cover O hO
    (fun a => canUnconj (O a).ι g (ts a) (hts a) (Y a)) hagree'
  refine ⟨θ, fun a => ?_⟩
  refine (isCanonicalBaseChange_iff (O a).ι g (ts a) (hts a) θ (Y a)).mpr ?_
  rw [hθ a, canConj_canUnconj]

end Stacks.AlgebraicGeometry.ModuleLimits

end
