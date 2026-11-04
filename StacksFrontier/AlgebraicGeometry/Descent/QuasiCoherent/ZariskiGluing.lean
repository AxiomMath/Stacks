module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Zariski
public import StacksFrontier.Topology.Sheaves.Glueing.MapGluing

/-!
# Gluing morphisms of sheaves of modules along a Zariski covering family

This file supplies the *gluing of morphisms* half of Sheaves, Section 00AK for sheaves of modules
over the structure sheaf of a scheme, which is what Stacks 023E appeals to and which the library
had only for sheaves of sets (`TopCat.Sheaf.existsUnique_hom_of_localHom`, Stacks 04TN), for
sheaves of modules over a *fixed* ring (Stacks 00AM, in
`StacksFrontier/Topology/Sheaves/Glueing/AlgebraicStructure.lean`, whose module file says explicitly
that the `𝒪`-module case "is a genuinely different development") and for presheaves of modules on
a ringed site with restriction taken as the slice-site pushforward
(Stacks 03EM).

## Main definitions

* `Stacks.Descent.descHom`: the adjunct `M ⟶ f_* f^* N` of a morphism `f^* M ⟶ f^* N` of pullbacks.
* `Stacks.Descent.unitApp`: the unit of
  `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` on sections over an open of the
  base.
* `Stacks.Descent.locApp`: the morphism on sections over an open `V` of the base contained in the
  range of an open immersion `g`, carried by a morphism `g^* M ⟶ g^* N` of pullbacks.

## Main results

* `Stacks.Descent.isIso_unitApp`: for an open immersion `g` and an open `V` of the base contained
  in the range of `g`, the unit is an isomorphism on sections over `V`.
* `Stacks.Descent.descHom_pullHom`: the adjunct of
  `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` is the adjunct composed with a
  comparison morphism that does not depend on the morphism being pulled back.  This is the one
  non-formal compatibility the whole file rests on, and it is a mate computation: the comparison
  isomorphism `AlgebraicGeometry.Scheme.Modules.pullbackComp` conjugates to
  `AlgebraicGeometry.Scheme.Modules.pushforwardComp`, by Mathlib's
  `AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`.
* `Stacks.Descent.locApp_pullHom`: consequently the local morphism on sections carried by a
  pullback of `φ` along a further morphism agrees with the one carried by `φ`.
* `Stacks.Descent.locApp_descentDataHom_eq`: the local morphisms carried by the components of a
  morphism of canonical descent data for a family of open immersions agree over every open
  contained in two of the ranges.  This is the compatibility hypothesis of the gluing.
* `Stacks.Descent.existsUnique_hom_of_locally`: **the gluing itself.**  A family of maps on
  sections over the opens of a covering, compatible with restriction, `𝒪_S`-linear and independent
  of the member of the covering, comes from a unique morphism of sheaves of modules.
* `Stacks.Descent.full_toDescentData`: consequently, for a family of open immersions whose images
  cover the target, `CategoryTheory.Pseudofunctor.toDescentData` of
  `AlgebraicGeometry.modulePullbackPseudofunctor` is **full**.
* `Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_zariski`, tagged
  `@[stacks 023E "zariski_full_faithfulness"]`: with the faithfulness already in
  `StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/Zariski.lean`, this is the full
  faithfulness half of Stacks 023E.
* `Stacks.Descent.isPrestack_modulePullbackPseudofunctor` and
  `Stacks.Descent.isPrestack_qcohPseudofunctor`: sheaves of modules, and quasi-coherent modules,
  form a **prestack** for the Zariski topology.  These are the first instances of
  `CategoryTheory.Pseudofunctor.IsPrestack` in the library; the second discharges the standing
  hypothesis of
  `Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_openCover_of_isPrestack`, and of
  `Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_of_isPrestack_of_sieve_mem` at
  the Zariski topology.

## What Stacks 023E still needs

The effectivity half is `Stacks.Descent.isEffective_zariski` with
`@[stacks 023E "zariski_effectivity"]` in
`Descent/QuasiCoherent/ZariskiEssSurj.lean`, so 023E is complete for the Zariski topology.
What this file does not prove is the **effectivity** half.  That is
`(AlgebraicGeometry.modulePullbackPseudofunctor.toDescentData f).EssSurj` — the gluing of the
sheaves of modules themselves, as opposed to the morphisms between them — after which
`Stacks.Descent.isEffective_of_essSurj_zariski` gives the effectivity half outright, with no
quasi-coherence side condition.  Nothing in this file proves it, and the tag placed below carries
the `"zariski_full_faithfulness"` clause comment for that reason.

Stacks 023T is a statement about the **fpqc** topology and does *not* follow from this file: the
reductions `Stacks.Descent.isEffective_of_isStack_of_sieve_mem` and
`Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_of_isPrestack_of_sieve_mem` need
`Stacks.Descent.qcohPseudofunctor.IsStack AlgebraicGeometry.Scheme.fpqcTopology`, and the Zariski
topology is strictly coarser than the fpqc one.

## Implementation notes

Everything is phrased so that the opens appearing in a composite are *syntactically* the same.
Writing the unit on sections with codomain `Γ((pullback g).obj M, g ⁻¹ᵁ V)` makes a composite with
a comparison morphism at `h ⁻¹ᵁ (g ⁻¹ᵁ V)` versus `(h ≫ g) ⁻¹ᵁ V` fail to rewrite — the two are
definitionally equal but `rw [Category.assoc]` works at `implicit` transparency and reports that
the target is not type-correct.  Writing it with codomain
`Γ((pullback g ⋙ pushforward g).obj M, V)` removes the problem at the source: every arrow in every
composite below is `Scheme.Modules.Hom.app _ V` for one and the same `V`, and all the
category-theoretic work happens one level up, between morphisms of
`AlgebraicGeometry.Scheme.Modules`.

For the same reason `Stacks.Descent.exists_descHomComparison` returns the comparison morphism as an
*existential* rather than as a definition: its two properties are all that is used, and keeping it
opaque avoids unfolding `AlgebraicGeometry.Scheme.Modules.pullbackComp` (which is built from
`CategoryTheory.Adjunction.leftAdjointUniq`) inside later goals.

## References

* [Stacks Project, Tag 00AK](https://stacks.math.columbia.edu/tag/00AK)
* [Stacks Project, Tag 023D](https://stacks.math.columbia.edu/tag/023D)
* [Stacks Project, Tag 023E](https://stacks.math.columbia.edu/tag/023E)
* [Stacks Project, Tag 04TN](https://stacks.math.columbia.edu/tag/04TN)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory Opposite TopologicalSpace

universe v u

namespace Stacks.Descent

open Scheme.Modules Pseudofunctor.LocallyDiscreteOpToCat

variable {S X X' : Scheme.{u}}

/-! ### The adjunct of a morphism of pullbacks -/

/-- The adjunct `M ⟶ g_* g^* N` of a morphism `g^* M ⟶ g^* N` between pullbacks. -/
def descHom (g : X ⟶ S) {M N : S.Modules}
    (φ : (pullback g).obj M ⟶ (pullback g).obj N) :
    M ⟶ (pullback g ⋙ pushforward g).obj N :=
  (pullbackPushforwardAdjunction g).unit.app M ≫ (pushforward g).map φ

/-- The adjunct of the identity of `g^* M` is the unit of the pullback-pushforward adjunction
at `M`. -/
@[simp]
theorem descHom_id (g : X ⟶ S) (M : S.Modules) :
    descHom g (𝟙 ((pullback g).obj M)) = (pullbackPushforwardAdjunction g).unit.app M := by
  simp [descHom]

/-- `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` for
`AlgebraicGeometry.modulePullbackPseudofunctor`, written out. -/
theorem pullHom_eq (g : X ⟶ S) (h : X' ⟶ X) {M N : S.Modules}
    (φ : (pullback g).obj M ⟶ (pullback g).obj N) :
    pullHom (F := modulePullbackPseudofunctor) (M₁ := M) (M₂ := N) (f₁ := g) (f₂ := g)
        φ h (h ≫ g) (h ≫ g) rfl rfl =
      (pullbackComp h g).inv.app M ≫ (pullback h).map φ ≫ (pullbackComp h g).hom.app N :=
  rfl

/-- The identity morphism of a pullback pulls back to the identity. -/
theorem pullHom_id_eq (g : X ⟶ S) (h : X' ⟶ X) (N : S.Modules) :
    pullHom (F := modulePullbackPseudofunctor) (M₁ := N) (M₂ := N) (f₁ := g) (f₂ := g)
        (𝟙 ((pullback g).obj N)) h (h ≫ g) (h ≫ g) rfl rfl = 𝟙 _ := by
  show (pullbackComp h g).inv.app N ≫ (pullback h).map (𝟙 _) ≫
    (pullbackComp h g).hom.app N = 𝟙 _
  simp

/-- The comparison morphism `g_* g^* N ⟶ (hg)_* (hg)^* N`. -/
def compHom (g : X ⟶ S) (h : X' ⟶ X) (N : S.Modules) :
    (pullback g ⋙ pushforward g).obj N ⟶ (pullback (h ≫ g) ⋙ pushforward (h ≫ g)).obj N :=
  (pushforward g).map ((pullbackPushforwardAdjunction h).unit.app ((pullback g).obj N)) ≫
    (pushforwardComp h g).hom.app ((pullback g ⋙ pullback h).obj N) ≫
      (pushforward (h ≫ g)).map ((pullbackComp h g).hom.app N)

/-- **The adjunct of a pulled-back morphism.**  Pulling a morphism of pullbacks back along a
further morphism composes its adjunct with a comparison morphism independent of it.

This is the mate computation that the whole file rests on: `pullbackComp` conjugates to
`pushforwardComp` under the pullback-pushforward adjunctions, which is Mathlib's
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`. -/
theorem descHom_pullHom (g : X ⟶ S) (h : X' ⟶ X) {M N : S.Modules}
    (φ : (pullback g).obj M ⟶ (pullback g).obj N) :
    descHom (h ≫ g) (pullHom (F := modulePullbackPseudofunctor) (M₁ := M) (M₂ := N)
        (f₁ := g) (f₂ := g) φ h (h ≫ g) (h ≫ g) rfl rfl) =
      descHom g φ ≫ compHom g h N := by
  have key := unit_conjugateEquiv (CategoryTheory.Adjunction.comp
      (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction h))
      (pullbackPushforwardAdjunction (h ≫ g)) (pullbackComp h g).inv M
  rw [conjugateEquiv_pullbackComp_inv, CategoryTheory.Adjunction.comp_unit_app] at key
  have hnat := (pushforwardComp h g).hom.naturality ((pullback h).map φ)
  have hun := (pullbackPushforwardAdjunction h).unit.naturality φ
  simp only [descHom, compHom, pullHom_eq, Functor.map_comp, Category.assoc, ← reassoc_of% key]
  simp only [Functor.comp_map] at hnat
  rw [← reassoc_of% hnat, ← Functor.map_comp_assoc]
  simp only [Functor.comp_map, Functor.id_map] at hun
  rw [← hun]
  simp only [Functor.map_comp, Category.assoc]
  rfl

/-- **The comparison morphism of `Stacks.Descent.descHom_pullHom`, for a factorisation given by an
equation.**  The two properties recorded here are everything that is used downstream, so the
comparison itself is kept opaque; see the implementation notes. -/
theorem exists_descHomComparison (g : X ⟶ S) (h : X' ⟶ X) (g' : X' ⟶ S) (hg' : h ≫ g = g')
    (N : S.Modules) :
    ∃ c : (pullback g ⋙ pushforward g).obj N ⟶ (pullback g' ⋙ pushforward g').obj N,
      (∀ {M : S.Modules} (φ : (pullback g).obj M ⟶ (pullback g).obj N),
          descHom g' (pullHom (F := modulePullbackPseudofunctor) (M₁ := M) (M₂ := N)
            (f₁ := g) (f₂ := g) φ h g' g' hg' hg') = descHom g φ ≫ c) ∧
        (pullbackPushforwardAdjunction g').unit.app N =
          (pullbackPushforwardAdjunction g).unit.app N ≫ c := by
  subst hg'
  refine ⟨compHom g h N, fun φ ↦ descHom_pullHom g h φ, ?_⟩
  refine (descHom_id (h ≫ g) N).symm.trans
    (Eq.trans ?_ (descHom_pullHom g h (𝟙 ((pullback g).obj N))))
  exact (congrArg (descHom (h ≫ g)) (pullHom_id_eq g h N)).symm

/-! ### The unit on sections -/

/-- The unit of the pullback-pushforward adjunction, on sections over an open of the base. -/
def unitApp (g : X ⟶ S) (M : S.Modules) (V : S.Opens) :
    Γ(M, V) ⟶ Γ((pullback g ⋙ pushforward g).obj M, V) :=
  ((pullbackPushforwardAdjunction g).unit.app M).app V

/-- The restriction map of a presheaf along a morphism between equal opens is invertible. -/
private theorem isIso_presheaf_map_of_eq {C : Type*} [Category C] {Z : TopCat}
    (F : (Opens Z)ᵒᵖ ⥤ C) {U V : Opens Z} (f : U ⟶ V) (e : U = V) : IsIso (F.map f.op) := by
  subst e
  rw [Subsingleton.elim f (𝟙 _), op_id, F.map_id]
  infer_instance

/-- **The unit is invertible on sections over an open contained in the range.**  For an open
immersion `g` and an open `V` of the base with `V ≤ g.opensRange`, the unit
`Γ(M, V) ⟶ Γ(g^* M, g ⁻¹ᵁ V)` is an isomorphism: it factors through the unit of
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction`, which is the restriction map of `M` along
`g ''ᵁ (g ⁻¹ᵁ V) = g.opensRange ⊓ V = V`. -/
theorem isIso_unitApp (g : X ⟶ S) [IsOpenImmersion g] (M : S.Modules) (V : S.Opens)
    (hV : V ≤ g.opensRange) : IsIso (unitApp g M V) := by
  have hV' : g ''ᵁ (g ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hV]
  have h₁ : IsIso (((restrictAdjunction g).unit.app M).app V) := by
    rw [restrictAdjunction_unit_app_app]
    exact isIso_presheaf_map_of_eq _ _ hV'
  have h₂ : unitApp g M V = ((restrictAdjunction g).unit.app M).app V ≫
      ((pushforward g).map ((restrictFunctorIsoPullback g).hom.app M)).app V :=
    (congrArg (fun ψ ↦ Scheme.Modules.Hom.app ψ V)
      (Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction g)
        (pullbackPushforwardAdjunction g) M)).symm
  rw [h₂]
  infer_instance

/-! ### The local morphism on sections -/

/-- **The morphism on sections carried by a morphism of pullbacks.**  For an open immersion
`g : X ⟶ S`, a morphism `φ : g^* M ⟶ g^* N` and an open `V` of `S` contained in the range of `g`,
this is the induced morphism `Γ(M, V) ⟶ Γ(N, V)`, obtained from the adjunct of `φ` by inverting
the unit at `N`. -/
def locApp (g : X ⟶ S) [IsOpenImmersion g] {M N : S.Modules}
    (φ : (pullback g).obj M ⟶ (pullback g).obj N) (V : S.Opens) (hV : V ≤ g.opensRange) :
    Γ(M, V) ⟶ Γ(N, V) :=
  (descHom g φ).app V ≫
    @CategoryTheory.inv _ _ _ _ (unitApp g N V) (isIso_unitApp g N V hV)

/-- The morphism on sections carried by `φ`, followed by the unit at `N`, is the adjunct of `φ` on
sections over `V`. -/
@[reassoc]
theorem locApp_comp_unitApp (g : X ⟶ S) [IsOpenImmersion g] {M N : S.Modules}
    (φ : (pullback g).obj M ⟶ (pullback g).obj N) (V : S.Opens) (hV : V ≤ g.opensRange) :
    locApp g φ V hV ≫ unitApp g N V = (descHom g φ).app V := by
  rw [locApp, Category.assoc,
    @IsIso.inv_hom_id _ _ _ _ _ (isIso_unitApp g N V hV), Category.comp_id]

/-- **The local morphism on sections does not change under pulling back.**  If `h ≫ g = g'` and
`V ≤ g'.opensRange`, the morphism on sections over `V` carried by `pullHom φ h g' g'` is the one
carried by `φ`. -/
theorem locApp_pullHom (g : X ⟶ S) [IsOpenImmersion g] (h : X' ⟶ X) (g' : X' ⟶ S)
    [IsOpenImmersion g'] (hg' : h ≫ g = g') {M N : S.Modules}
    (φ : (pullback g).obj M ⟶ (pullback g).obj N) (V : S.Opens) (hV : V ≤ g'.opensRange)
    (hVg : V ≤ g.opensRange) :
    locApp g' (pullHom (F := modulePullbackPseudofunctor) (M₁ := M) (M₂ := N)
        (f₁ := g) (f₂ := g) φ h g' g' hg' hg') V hV = locApp g φ V hVg := by
  obtain ⟨c, hc₁, hc₂⟩ := exists_descHomComparison g h g' hg' N
  have := isIso_unitApp g' N V hV
  have hu : unitApp g' N V = unitApp g N V ≫ c.app V :=
    congrArg (fun ψ ↦ Scheme.Modules.Hom.app ψ V) hc₂
  rw [← cancel_mono (unitApp g' N V)]
  refine (locApp_comp_unitApp g' _ V hV).trans
    ((congrArg (·.app V) (hc₁ φ)).trans ?_)
  rw [hu, locApp_comp_unitApp_assoc g φ V hVg]
  rfl

/-- `Stacks.Descent.descHom` is the adjunction bijection. -/
theorem descHom_eq_homEquiv (g : X ⟶ S) {M N : S.Modules}
    (φ : (pullback g).obj M ⟶ (pullback g).obj N) :
    descHom g φ = (pullbackPushforwardAdjunction g).homEquiv M ((pullback g).obj N) φ := by
  rw [Adjunction.homEquiv_unit, descHom]

/-- `Stacks.Descent.descHom` is injective. -/
theorem descHom_injective (g : X ⟶ S) {M N : S.Modules} :
    Function.Injective (descHom g (M := M) (N := N)) := fun _ _ h ↦
  ((pullbackPushforwardAdjunction g).homEquiv M ((pullback g).obj N)).injective
    (by rwa [← descHom_eq_homEquiv, ← descHom_eq_homEquiv])

/-- The adjunct of the pullback of a morphism on the base. -/
theorem descHom_map (g : X ⟶ S) {M N : S.Modules} (θ : M ⟶ N) :
    descHom g ((pullback g).map θ) = θ ≫ (pullbackPushforwardAdjunction g).unit.app N :=
  ((pullbackPushforwardAdjunction g).unit.naturality θ).symm

/-- **A morphism into a pushforward along an open immersion is determined over the range.**
Two morphisms `M ⟶ g_* K` agreeing on sections over every open contained in `g.opensRange` are
equal: the restriction `Γ(g_* K, V) ⟶ Γ(g_* K, V ⊓ g.opensRange)` is the identity, because the two
opens have the same preimage under `g`. -/
theorem hom_ext_of_le_opensRange (g : X ⟶ S) [IsOpenImmersion g] {M : S.Modules} {K : X.Modules}
    {a b : M ⟶ (pushforward g).obj K}
    (h : ∀ V : S.Opens, V ≤ g.opensRange → a.app V = b.app V) : a = b := by
  refine Scheme.Modules.hom_ext _ _ fun V ↦ ?_
  have hiso : IsIso (((pushforward g).obj K).presheaf.map
      (homOfLE (inf_le_left : V ⊓ g.opensRange ≤ V)).op) :=
    isIso_presheaf_map_of_eq K.presheaf ((Opens.map g.base).map _)
      (Opens.ext (by simp [Set.preimage_inter, Scheme.Hom.opensRange]))
  rw [← cancel_mono (((pushforward g).obj K).presheaf.map
    (homOfLE (inf_le_left : V ⊓ g.opensRange ≤ V)).op)]
  refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
  simp only [ConcreteCategory.comp_apply]
  rw [presheaf_map_app_apply a (homOfLE (inf_le_left : V ⊓ g.opensRange ≤ V)) x,
    presheaf_map_app_apply b (homOfLE (inf_le_left : V ⊓ g.opensRange ≤ V)) x,
    h (V ⊓ g.opensRange) inf_le_right]

/-- `Stacks.Descent.unitApp` is the component over `V` of the unit at `M`. -/
theorem unitApp_def (g : X ⟶ S) (M : S.Modules) (V : S.Opens) :
    unitApp g M V = ((pullbackPushforwardAdjunction g).unit.app M).app V := rfl

/-- For an open immersion `g` and an open `V` contained in its range, the unit on sections over
`V` is injective. -/
theorem unitApp_injective (g : X ⟶ S) [IsOpenImmersion g] (N : S.Modules) (V : S.Opens)
    (hV : V ≤ g.opensRange) : Function.Injective (unitApp g N V) :=
  have := isIso_unitApp g N V hV
  (ConcreteCategory.bijective_of_isIso (unitApp g N V)).1

/-- The unit at `N` sends the image of a section `x` under `Stacks.Descent.locApp` to the image
of `x` under the adjunct of `φ`. -/
theorem unitApp_locApp (g : X ⟶ S) [IsOpenImmersion g] {M N : S.Modules}
    (φ : (pullback g).obj M ⟶ (pullback g).obj N) (V : S.Opens) (hV : V ≤ g.opensRange)
    (x : Γ(M, V)) : unitApp g N V (locApp g φ V hV x) = (descHom g φ).app V x := by
  simpa only [ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom (locApp_comp_unitApp g φ V hV) x

/-- `Stacks.Descent.locApp` is compatible with the restriction maps. -/
theorem locApp_naturality (g : X ⟶ S) [IsOpenImmersion g] {M N : S.Modules}
    (φ : (pullback g).obj M ⟶ (pullback g).obj N) (V W : S.Opens) (hV : V ≤ g.opensRange)
    (hW : W ≤ g.opensRange) (k : W ⟶ V) (x : Γ(M, V)) :
    N.presheaf.map k.op (locApp g φ V hV x) = locApp g φ W hW (M.presheaf.map k.op x) := by
  refine unitApp_injective g N W hW ?_
  rw [unitApp_locApp]
  have h₁ := presheaf_map_app_apply ((pullbackPushforwardAdjunction g).unit.app N) k
    (locApp g φ V hV x)
  simp only [Functor.id_obj] at h₁
  rw [unitApp_def, ← h₁, ← unitApp_def, unitApp_locApp]
  exact presheaf_map_app_apply (descHom g φ) k x

/-- `Stacks.Descent.locApp` is linear over the structure sheaf. -/
theorem locApp_smul (g : X ⟶ S) [IsOpenImmersion g] {M N : S.Modules}
    (φ : (pullback g).obj M ⟶ (pullback g).obj N) (V : S.Opens) (hV : V ≤ g.opensRange)
    (r : Γ(S, V)) (x : Γ(M, V)) :
    locApp g φ V hV (r • x) = r • locApp g φ V hV x := by
  refine unitApp_injective g N V hV ?_
  rw [unitApp_locApp, Scheme.Modules.Hom.app_smul (descHom g φ) r x, unitApp_def,
    Scheme.Modules.Hom.app_smul ((pullbackPushforwardAdjunction g).unit.app N) r
      (locApp g φ V hV x), ← unitApp_def, unitApp_locApp]

/-! ### The compatible family carried by a morphism of canonical descent data -/

section DescentData

variable {I : Type v} {Y : I → Scheme.{u}} {f : ∀ i, Y i ⟶ S} [∀ i, IsOpenImmersion (f i)]

/-- **The local morphisms carried by a morphism of canonical descent data agree on overlaps.**
If `φ` is a morphism between the canonical descent data of `M` and of `N` for a family `f` of open
immersions, then over an open `V` of the base contained in the ranges of `f i` and of `f j` the
morphisms on sections carried by the components `φ.hom i` and `φ.hom j` coincide.

This is the compatibility hypothesis that the gluing of morphisms consumes.  It is the descent
datum's `CategoryTheory.Pseudofunctor.DescentData.Hom.comm` for the open subscheme `V`, read
through `Stacks.Descent.locApp_pullHom`. -/
theorem locApp_descentDataHom_eq {M N : S.Modules}
    (φ : (modulePullbackPseudofunctor.toDescentData f).obj M ⟶
      (modulePullbackPseudofunctor.toDescentData f).obj N)
    (i j : I) (V : S.Opens) (hVi : V ≤ (f i).opensRange) (hVj : V ≤ (f j).opensRange) :
    locApp (f i) (φ.hom i) V hVi = locApp (f j) (φ.hom j) V hVj := by
  have hVV : V ≤ V.ι.opensRange := by rw [Scheme.Opens.opensRange_ι]
  have key : ∀ (k : I) (hk : V ≤ (f k).opensRange), ∃ (hk' : V.toScheme ⟶ Y k)
      (e : hk' ≫ f k = V.ι), locApp V.ι (pullHom (F := modulePullbackPseudofunctor)
        (M₁ := M) (M₂ := N) (f₁ := f k) (f₂ := f k) (φ.hom k) hk' V.ι V.ι e e) V hVV =
          locApp (f k) (φ.hom k) V hk := fun k hk ↦ by
    have hfac := IsOpenImmersion.lift_fac (f k) V.ι fun _ ⟨y, hy⟩ ↦ hy ▸ hk y.2
    exact ⟨_, hfac, locApp_pullHom (f k) _ V.ι hfac (φ.hom k) V hVV hk⟩
  obtain ⟨hi, hfi, ei⟩ := key i hVi
  obtain ⟨hj, hfj, ej⟩ := key j hVj
  have hcompat := ((Pseudofunctor.DescentData.subtypeCompatibleHomEquiv
    modulePullbackPseudofunctor f).symm φ).2 i j (Over.mk V.ι)
      (Over.homMk hi (by simpa using hfi)) (Over.homMk hj (by simpa using hfj))
      (Over.OverMorphism.ext (by simpa using hfi.trans hfj.symm))
  rw [← ei, ← ej]
  exact congrArg (fun ψ ↦ locApp V.ι ψ V hVV) hcompat

end DescentData

/-! ### Gluing a locally given morphism of sheaves of modules -/

section Glue

/-- The sheaf of sets underlying a sheaf of modules on a scheme. -/
def typeSheaf (M : S.Modules) : TopCat.Sheaf (Type u) S.toTopCat :=
  ⟨M.presheaf ⋙ CategoryTheory.forget Ab.{u},
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp _ _).1 M.isSheaf⟩

variable {M N : S.Modules} {I : Type v} {U : I → S.Opens}

/-- **Gluing a morphism of sheaves of modules over the structure sheaf.**  Given an open covering
`⨆ i, U i = ⊤` of a scheme `S` and, for each `i`, a family of maps on sections over the opens
contained in `U i` that is compatible with the restriction maps, `𝒪_S`-linear, and independent of
`i` on the overlaps, there is a unique morphism `M ⟶ N` of sheaves of modules restricting to it.

This is the gluing of morphisms of Sheaves, Section 00AK for sheaves of modules over a structure
sheaf; the underlying map of sheaves of sets is glued by Stacks 04TN
(`TopCat.Sheaf.existsUnique_hom_of_localHom`), and its additivity and linearity follow from the
separation half of the sheaf axiom for `N`. -/
theorem existsUnique_hom_of_locally (hU : ⨆ i, U i = ⊤)
    (β : ∀ (i : I) (V : S.Opens), V ≤ U i → (Γ(M, V) ⟶ Γ(N, V)))
    (hnat : ∀ (i : I) (V W : S.Opens) (hV : V ≤ U i) (hW : W ≤ U i) (k : W ⟶ V) (x : Γ(M, V)),
      N.presheaf.map k.op (β i V hV x) = β i W hW (M.presheaf.map k.op x))
    (hagree : ∀ (i j : I) (V : S.Opens) (hi : V ≤ U i) (hj : V ≤ U j) (x : Γ(M, V)),
      β i V hi x = β j V hj x)
    (hsmul : ∀ (i : I) (V : S.Opens) (hV : V ≤ U i) (r : Γ(S, V)) (x : Γ(M, V)),
      β i V hV (r • x) = r • β i V hV x) :
    ∃! θ : M ⟶ N, ∀ (i : I) (V : S.Opens) (hV : V ≤ U i) (x : Γ(M, V)),
      θ.app V x = β i V hV x := by
  obtain ⟨t, htnat, htloc⟩ : ∃ t : ∀ V : S.Opens, Γ(M, V) → Γ(N, V),
      (∀ (V W : S.Opens) (k : W ⟶ V) (x : Γ(M, V)),
        N.presheaf.map k.op (t V x) = t W (M.presheaf.map k.op x)) ∧
      ∀ (i : I) (V : S.Opens) (hV : V ≤ U i) (x : Γ(M, V)), t V x = β i V hV x := by
    obtain ⟨ψ, hψ, -⟩ := TopCat.Sheaf.existsUnique_hom_of_localHom U hU (typeSheaf M)
      (typeSheaf N)
      (fun i ↦ { app := fun V hV ↦ β i V hV
                 naturality := fun V W hV hW k x ↦ hnat i V W hV hW k x })
      (fun i j V hi hj ↦ funext fun x ↦ hagree i j V hi hj x)
    exact ⟨fun V x ↦ ψ.1.app (op V) x,
      fun V W k x ↦ (NatTrans.naturality_apply ψ.1 k.op x).symm,
      fun i V hV x ↦ congrFun (hψ i V hV) x⟩
  -- an arbitrary open is covered by its traces on the `U i`
  have hcov : ∀ V : S.Opens, V ≤ ⨆ i, V ⊓ U i := fun V ↦ by
    simp only [← inf_iSup_eq, hU, inf_top_eq, le_refl]
  have hsep : ∀ (V : S.Opens) (a b : Γ(N, V)),
      (∀ i, N.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op a =
        N.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op b) → a = b :=
    fun V a b h ↦ TopCat.Sheaf.eq_of_locally_eq'
      (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab.{u} S) (fun i ↦ V ⊓ U i) V
      (fun i ↦ homOfLE inf_le_left) (hcov V) _ _ h
  have hres : ∀ (V : S.Opens) (i : I) (x : Γ(M, V)),
      N.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op (t V x) =
        β i (V ⊓ U i) inf_le_right
          (M.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op x) :=
    fun V i x ↦ (htnat V (V ⊓ U i) (homOfLE inf_le_left) x).trans
      (htloc i (V ⊓ U i) inf_le_right _)
  have hadd : ∀ (V : S.Opens) (x y : Γ(M, V)), t V (x + y) = t V x + t V y := fun V x y ↦ by
    refine hsep V _ _ fun i ↦ ?_
    rw [hres V i, map_add, map_add, map_add, hres V i, hres V i]
  have hsm : ∀ (V : S.Opens) (r : Γ(S, V)) (x : Γ(M, V)), t V (r • x) = r • t V x :=
    fun V r x ↦ by
      refine hsep V _ _ fun i ↦ ?_
      rw [hres V i, Scheme.Modules.map_smul, Scheme.Modules.map_smul, hsmul, hres V i]
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ : M ⟶ N, ∀ (V : S.Opens) (x : Γ(M, V)), θ₀.app V x = t V x :=
    ⟨⟨PresheafOfModules.homMk
        { app := fun V ↦ AddCommGrpCat.ofHom (AddMonoidHom.mk' (t V.unop) (hadd V.unop))
          naturality := fun V W k ↦
            ConcreteCategory.hom_ext _ _ fun x ↦ (htnat V.unop W.unop k.unop x).symm }
        fun V r m ↦ hsm V.unop r m⟩, fun _ _ ↦ rfl⟩
  refine ⟨θ₀, fun i V hV x ↦ (hθ₀ V x).trans (htloc i V hV x), ?_⟩
  intro θ hθ
  refine Scheme.Modules.hom_ext _ _ fun V ↦ ?_
  refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
  refine hsep V _ _ fun i ↦ ?_
  rw [presheaf_map_app_apply θ (homOfLE (inf_le_left : V ⊓ U i ≤ V)) x,
    hθ i (V ⊓ U i) inf_le_right,
    presheaf_map_app_apply θ₀ (homOfLE (inf_le_left : V ⊓ U i ≤ V)) x, hθ₀,
    htloc i (V ⊓ U i) inf_le_right]

end Glue

/-! ### Fullness of the descent functor for a Zariski covering family -/

section Full

variable {I : Type v} {Y : I → Scheme.{u}} {f : ∀ i, Y i ⟶ S} [∀ i, IsOpenImmersion (f i)]

/-- **The gluing of morphisms, as fullness of the descent functor.**  For a family of open
immersions whose images cover the target, the functor
`CategoryTheory.Pseudofunctor.toDescentData` of `AlgebraicGeometry.modulePullbackPseudofunctor`
is full: a family of morphisms of pullbacks compatible over all common refinements comes from a
morphism on the base.

This is the gluing half of Sheaves, Section 00AK for sheaves of modules over a structure sheaf,
and together with `Stacks.Descent.faithful_toDescentData_of_iSup_opensRange_eq_top` it is the
full faithfulness that Stacks 023E asserts. -/
theorem full_toDescentData (hf : ⨆ i, (f i).opensRange = ⊤) :
    (modulePullbackPseudofunctor.toDescentData f).Full where
  map_surjective {M N} φ := by
    obtain ⟨θ, hθ, -⟩ := existsUnique_hom_of_locally (M := M) (N := N)
      (U := fun i ↦ (f i).opensRange) hf
      (fun i V hV ↦ locApp (f i) (φ.hom i) V hV)
      (fun i V W hV hW k x ↦ locApp_naturality (f i) (φ.hom i) V W hV hW k x)
      (fun i j V hi hj x ↦
        ConcreteCategory.congr_hom (locApp_descentDataHom_eq φ i j V hi hj) x)
      (fun i V hV r x ↦ locApp_smul (f i) (φ.hom i) V hV r x)
    refine ⟨θ, Pseudofunctor.DescentData.hom_ext fun i ↦ ?_⟩
    have key : (pullback (f i)).map θ = φ.hom i := by
      refine descHom_injective (f i) ((descHom_map (f i) θ).trans ?_)
      refine hom_ext_of_le_opensRange (f i) fun V hV ↦ ?_
      refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
      exact (congrArg (fun y ↦ unitApp (f i) N V y) (hθ i V hV x)).trans
        (unitApp_locApp (f i) (φ.hom i) V hV x)
    exact key

/-- **Full faithfulness of the descent functor for a Zariski covering family.**  Combining
`Stacks.Descent.full_toDescentData` with the faithfulness
`Stacks.Descent.faithful_toDescentData_of_iSup_opensRange_eq_top`. -/
noncomputable def fullyFaithfulToDescentData (hf : ⨆ i, (f i).opensRange = ⊤) :
    (modulePullbackPseudofunctor.toDescentData f).FullyFaithful :=
  haveI := full_toDescentData hf
  haveI := faithful_toDescentData_of_iSup_opensRange_eq_top f hf
  Functor.FullyFaithful.ofFullyFaithful _

/-- **The full faithfulness half of Stacks 023E.**  For a family of open immersions whose images
cover the target, the canonical descent functor of Stacks 023D on quasi-coherent modules is fully
faithful.

This is the full faithfulness clause of Stacks 023E; the effectivity clause is *not* proved
here. -/
@[stacks 023E "zariski_full_faithfulness"]
theorem nonempty_fullyFaithful_canonicalDescentFunctor_zariski
    (hf : ⨆ i, (f i).opensRange = ⊤) :
    Nonempty (canonicalDescentFunctor f).FullyFaithful :=
  nonempty_fullyFaithful_canonicalDescentFunctor_of_fullyFaithful
    (fullyFaithfulToDescentData hf)

/-- **The full faithfulness half of Stacks 023E**, for an open covering of a scheme in the form of
an `AlgebraicGeometry.Scheme.OpenCover`. -/
theorem nonempty_fullyFaithful_canonicalDescentFunctor_openCover (𝒰 : Scheme.OpenCover.{v} S) :
    Nonempty (canonicalDescentFunctor 𝒰.f).FullyFaithful :=
  nonempty_fullyFaithful_canonicalDescentFunctor_zariski 𝒰.iSup_opensRange

end Full

/-! ### The Zariski prestack condition -/

/-- **Sheaves of modules form a prestack for the Zariski topology.**  This is the first instance
of `CategoryTheory.Pseudofunctor.IsPrestack` in the library, and it is exactly the gluing of
morphisms of Sheaves, Section 00AK: by `CategoryTheory.Pseudofunctor.IsPrestack.of_precoverage` it
is enough to check the descent of morphisms for the presieves of the Zariski precoverage, which is
`Stacks.Descent.full_toDescentData` together with the faithfulness in
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/Zariski.lean`. -/
instance isPrestack_modulePullbackPseudofunctor :
    modulePullbackPseudofunctor.{u}.IsPrestack Scheme.zariskiTopology.{u} :=
  Pseudofunctor.IsPrestack.of_precoverage (J := Scheme.zariskiPrecoverage.{u}) fun _ R hR ↦ by
    obtain ⟨_, _, f, rfl⟩ := R.exists_eq_ofArrows
    have : ∀ i, IsOpenImmersion (f i) := isOpenImmersion_of_mem_zariskiPrecoverage hR
    rw [Pseudofunctor.isPrestackFor_ofArrows_iff]
    exact ⟨fullyFaithfulToDescentData (iSup_opensRange_eq_top_of_mem_zariskiPrecoverage hR)⟩

/-- **The quasi-coherent descent functor is fully faithful for a Zariski covering family**, in
the form of `CategoryTheory.Pseudofunctor.toDescentData` for
`Stacks.Descent.qcohPseudofunctor`. -/
theorem nonempty_fullyFaithful_qcohToDescentData {I : Type v} {Y : I → Scheme.{u}}
    {f : ∀ i, Y i ⟶ S} [∀ i, IsOpenImmersion (f i)] (hf : ⨆ i, (f i).opensRange = ⊤) :
    Nonempty (qcohPseudofunctor.toDescentData f).FullyFaithful := by
  refine (Functor.FullyFaithful.nonempty_iff_map_bijective _).2 fun M N ↦ ?_
  have hb := (Functor.FullyFaithful.nonempty_iff_map_bijective (canonicalDescentFunctor f)).1
    (nonempty_fullyFaithful_canonicalDescentFunctor_zariski hf) M N
  have hcomp : ((canonicalDescentFunctor f).map : (M ⟶ N) → _) =
      homForget ∘ ((qcohPseudofunctor.toDescentData f).map : (M ⟶ N) → _) :=
    funext fun φ ↦ canonicalDescentFunctor_map_eq φ
  rw [hcomp] at hb
  exact (Function.Bijective.of_comp_iff' homForget_bijective _).1 hb

/-- **Quasi-coherent modules form a prestack for the Zariski topology.**  This discharges the
standing hypothesis of
`Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_openCover_of_isPrestack` and of
`Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_of_isPrestack_of_sieve_mem` at the
Zariski topology. -/
instance isPrestack_qcohPseudofunctor :
    qcohPseudofunctor.{u}.IsPrestack Scheme.zariskiTopology.{u} :=
  Pseudofunctor.IsPrestack.of_precoverage (J := Scheme.zariskiPrecoverage.{u}) fun _ R hR ↦ by
    obtain ⟨_, _, f, rfl⟩ := R.exists_eq_ofArrows
    have : ∀ i, IsOpenImmersion (f i) := isOpenImmersion_of_mem_zariskiPrecoverage hR
    rw [Pseudofunctor.isPrestackFor_ofArrows_iff]
    exact nonempty_fullyFaithful_qcohToDescentData
      (iSup_opensRange_eq_top_of_mem_zariskiPrecoverage hR)

end Stacks.Descent

end

end
