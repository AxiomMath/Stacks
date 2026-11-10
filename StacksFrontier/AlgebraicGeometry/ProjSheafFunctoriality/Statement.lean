module

public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Exactness
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStructureRestriction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 01M7 in one statement

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring, let `M` be a `ℤ`-graded `S`-module with grading `𝒨`,
and let `M̃` be the sheaf of `𝒪_{Proj(S)}`-modules associated to `M`. Tag 01M7 collects
everything the construction of `M̃` has produced: the sections over a positive-degree standard
open, the restriction maps between two such, the stalks at a homogeneous prime, the canonical
maps out of the degree-zero pieces `S₀` and `M₀`, the naturality of all of these in `M`, and the
exactness of `M ↦ M̃`.

Each of those is proved separately, and the registrations of the tag sit on the separate
statements. This file states them together, so that one declaration says what the tag says.

## Main results

* `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.sections_restriction_stalks_functorial_exact`:
  **the assertions of Tag 01M7 in one statement.**

## Implementation notes

The identifications of the tag are definitions producing isomorphisms, linear equivalences and a
functor rather than propositions, so the conjuncts that assert an identification exists are
`Nonempty` of the identification's type, which is what the source asserts of them; the conjuncts
that compare two maps — the restriction squares, the two formulas for the canonical maps out of
`S₀` and `M₀`, the naturality squares and the functor laws — are the equations themselves.

The two statements about the structure sheaf alone, `Γ(D₊(f), 𝒪) = S₍f₎` and
`𝒪_{Proj(S), x} = S₍𝔭₎`, are `AlgebraicGeometry.Proj.basicOpenIsoAway` and
`AlgebraicGeometry.Proj.stalkIso'` in Mathlib.

The second graded module and the degree-preserving map into it are quantified inside the
functoriality conjunct rather than taken as parameters, so that the whole statement is about the
graded ring and the single graded module `M` that the source's hypotheses give.

The exactness conjunct is stated through the category `GradedModuleCat` of graded modules with
degree-preserving maps, in which a short exact sequence of graded modules is a pair of morphisms
with the usual three conditions; the carrier universe there is the universe of the ring, which is
the universe in which short exactness of the resulting sheaves of modules is available.

## References

* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat DirectSum
open AlgebraicGeometry
open Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjSheafFunctoriality

universe u w t t' t''

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S M : Type u} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

omit [AddCommGroup M] [AddSubgroupClass τ M] in
/-- A degree-zero element of `M` is homogeneous of degree `0 • d`, which is the degree in which
the standard-open fraction with denominator `f ^ 0` has its numerator. -/
theorem mem_zero_nsmul (𝒨 : ℤ → τ) (d : ℕ) (m : 𝒨 0) :
    (m : M) ∈ 𝒨 ((0 : ℕ) • (d : ℤ)) := by
  simpa only [zero_smul] using m.2

/-- **[Stacks, Tag 01M7].** Let `S` be a graded ring, let `M` be a graded `S`-module and let `M̃`
be the sheaf of `𝒪_{Proj(S)}`-modules associated to `M`. Then all of the following hold.

The conjuncts are, in order:

1. For `f` homogeneous of positive degree, `Γ(D₊(f), 𝒪_{Proj(S)})` is `S₍f₎`.
2. For `f` homogeneous of positive degree, `Γ(D₊(f), M̃)` is `M₍f₎` as an `S₍f₎`-module.
3. For `D₊(g) ⊆ D₊(f)` with `f`, `g` homogeneous of positive degree, the restriction map of
  `𝒪_{Proj(S)}` is the map `S₍f₎ → S₍g₎` of Tag 01M4, and the restriction map of `M̃` is the
  map `M₍f₎ → M₍g₎` of Tag 01M4.
4. At a point `x` of `Proj(S)`, with homogeneous prime `𝔭`, the stalk `𝒪_{Proj(S), x}` is `S₍𝔭₎`.
5. At the same point, the stalk `(M̃)_x` is `M₍𝔭₎` as an `S₍𝔭₎`-module.
6. There is a canonical ring map `S₀ → Γ(Proj(S), 𝒪_{Proj(S)})` and a canonical `S₀`-module map
  `M₀ → Γ(Proj(S), M̃)`, each compatible with the description of the sections over a
  positive-degree standard open and with the description of the stalks: the four equations say
  that the restriction of the global section attached to `a`, resp. to `m`, is `a / 1`, resp.
  `m / f ^ 0`, and that its germ at `x` is `a / 1`, resp. `m / 1`.
7. The identifications are functorial in the graded module. The identity map of `M` induces the
  identity morphism of `M̃`; and for every graded `S`-module `N` and degree-preserving
  `φ : M →ₗ[S] N`, with `M̃ ⟶ Ñ` the induced morphism: composition with a degree-preserving map
  out of `N` is respected, and the identifications of (2), (5) and (6) are natural — over a
  positive-degree standard open the induced morphism is the degree-zero part of the localized
  map `M_f → N_f`, on the stalk at `x` it is the localization of `φ` at `𝔭`, and it takes the
  global section attached to `m` to the global section attached to `φ m`.
8. In particular `M ↦ M̃` is an exact functor: a short exact sequence of graded `S`-modules with
  degree-preserving maps goes to a short exact sequence of sheaves of `𝒪_{Proj(S)}`-modules.

Every conjunct is the separate statement that proves it; the separate registrations of the tag
are on those. -/
@[stacks 01M7 "the tag's assertions in one statement: the sections of the structure sheaf and of
the associated sheaf over a positive-degree standard open are the degree-zero localizations
`S₍f₎` and `M₍f₎`, the restriction maps between two standard opens are the canonical maps
`S₍f₎ → S₍g₎` and `M₍f₎ → M₍g₎` of degree-zero localizations, the stalks at a homogeneous prime
are `S₍𝔭₎` and `M₍𝔭₎`, there are canonical maps `S₀ → Γ(Proj S, 𝒪)` and `M₀ → Γ(Proj S, M̃)`
fitting both descriptions, every one of these identifications is natural in the graded module,
and `M ↦ M̃` is an exact functor", ega "II 2.5.5" "special case"]
theorem sections_restriction_stalks_functorial_exact :
    (∀ (f : S) (d : ℕ), f ∈ 𝒮 d → 0 < d →
        Nonempty (CommRingCat.of (HomogeneousLocalization.Away 𝒮 f) ≅
          (AlgebraicGeometry.Proj 𝒮).presheaf.obj (op (Proj.basicOpen 𝒮 f)))) ∧
      (∀ (f : S) (d : ℕ), f ∈ 𝒮 d → 0 < d →
        Nonempty ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj
            (op (ProjectiveSpectrum.basicOpen 𝒮 f)) ≃ₗ[HomogeneousLocalization.Away 𝒮 f]
          GradedModuleDegreeZeroLocalization 𝒮 𝒨 f)) ∧
      (∀ (f g : S) (d e : ℕ) (hf : f ∈ 𝒮 d) (hd : 0 < d) (hg : g ∈ 𝒮 e) (he : 0 < e)
          (hfg : ProjectiveSpectrum.basicOpen 𝒮 g ≤ ProjectiveSpectrum.basicOpen 𝒮 f),
        CommRingCat.ofHom (ProjectiveSpectrum.degreeZeroRingMap 𝒮 f g
              ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg).toRingHom ≫
            (Proj.basicOpenIsoAway 𝒮 g hg he).hom =
          (Proj.basicOpenIsoAway 𝒮 f hf hd).hom ≫
            (AlgebraicGeometry.Proj 𝒮).presheaf.map (homOfLE hfg).op) ∧
      (∀ (f g : S) (hf : ∃ d : ℕ, 0 < d ∧ f ∈ 𝒮 d) (hg : ∃ d : ℕ, 0 < d ∧ g ∈ 𝒮 d)
          (hfg : ProjectiveSpectrum.basicOpen 𝒮 g ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
          (a : GradedModuleDegreeZeroLocalization 𝒮 𝒨 f),
        (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.map (homOfLE hfg).op
            (ProjectiveSpectrum.Proj.degreeZeroToSection 𝒮 𝒨 f a) =
          ProjectiveSpectrum.Proj.degreeZeroToSection 𝒮 𝒨 g
            ((ProjectiveSpectrum.moduleRestrictionMaps 𝒮 𝒨 f g hf hg hfg).degreeZeroMap a)) ∧
      (∀ x : ProjectiveSpectrum.top 𝒮,
        Nonempty ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x ≃+*
          HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)) ∧
      (∀ x : ProjectiveSpectrum.top 𝒮,
        Nonempty
          (letI : Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x)
              (ProjStalkGlobalSections.degreeZeroModuleAt 𝒮 𝒨 x) :=
            Module.compHom _ (Proj.stalkIso' 𝒮 x).toRingHom
          ProjStalkGlobalSections.associatedModuleSheafStalk 𝒮 𝒨 x ≃ₗ[
              (ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x]
            ProjStalkGlobalSections.degreeZeroModuleAt 𝒮 𝒨 x)) ∧
      Nonempty (𝒮 0 →+* (ProjectiveSpectrum.Proj.structureSheaf 𝒮).1.obj (op ⊤)) ∧
      (∀ (f : S) (a : 𝒮 0),
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).1.map (homOfLE le_top).op
            (ProjStalkGlobalSections.degreeZeroRingToGlobalSections 𝒮 a) =
          (ProjectiveSpectrum.Proj.awayToSection 𝒮 f).hom
            (HomogeneousLocalization.fromZeroRingHom 𝒮 (Submonoid.powers f) a)) ∧
      (∀ (x : ProjectiveSpectrum.top 𝒮) (a : 𝒮 0),
        Proj.stalkIso' 𝒮 x ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.germ ⊤ x trivial
            (ProjStalkGlobalSections.degreeZeroRingToGlobalSections 𝒮 a)) =
          HomogeneousLocalization.fromZeroRingHom 𝒮 x.asHomogeneousIdeal.toIdeal.primeCompl a) ∧
      Nonempty
        (letI : Module (𝒮 0)
            ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj (op ⊤)) :=
          Module.compHom _ (ProjStalkGlobalSections.degreeZeroRingToGlobalSections 𝒮)
        𝒨 0 →ₗ[𝒮 0] (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj (op ⊤)) ∧
      (∀ (f : S) (d : ℕ) (hf : f ∈ 𝒮 d) (hd : 0 < d) (m : 𝒨 0),
        ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf hd
            ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.map (homOfLE le_top).op
              (ProjStalkGlobalSections.degreeZeroToGlobalSections 𝒮 𝒨 m)) =
          ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 𝒨 hf 0 m.1 (mem_zero_nsmul 𝒨 d m)) ∧
      (∀ (x : ProjectiveSpectrum.top 𝒮) (m : 𝒨 0),
        ((ProjStalkGlobalSections.associatedModuleSheafStalkEquiv 𝒮 𝒨 x
              (ProjStalkGlobalSections.associatedModuleSheafGerm 𝒮 𝒨 x ⊤ trivial
                (ProjStalkGlobalSections.degreeZeroToGlobalSections 𝒮 𝒨 m)) :
            ProjStalkGlobalSections.degreeZeroModuleAt 𝒮 𝒨 x) :
              ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x) =
          LocalizedModule.mk m.1 (1 : x.asHomogeneousIdeal.toIdeal.primeCompl)) ∧
      (associatedModuleSheafMap 𝒮 𝒨 𝒨 (LinearMap.id : M →ₗ[S] M) (fun _ _ hm => hm) = 𝟙 _) ∧
      (∀ (N : Type u) [AddCommGroup N] [Module S N] {υ : Type t'} [SetLike υ N]
          [AddSubgroupClass υ N] (𝒩 : ℤ → υ) [Decomposition 𝒩] [SetLike.GradedSMul 𝒮 𝒩]
          (φ : M →ₗ[S] N) (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i),
        (∀ (P : Type u) [AddCommGroup P] [Module S P] {ρ : Type t''} [SetLike ρ P]
              [AddSubgroupClass ρ P] (𝒬 : ℤ → ρ) [Decomposition 𝒬] [SetLike.GradedSMul 𝒮 𝒬]
              (ψ : N →ₗ[S] P) (hψ : ∀ i (n : N), n ∈ 𝒩 i → ψ n ∈ 𝒬 i),
            associatedModuleSheafMap 𝒮 𝒨 𝒬 (ψ.comp φ) (fun i m hm => hψ i (φ m) (hφ i m hm)) =
              associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ ≫ associatedModuleSheafMap 𝒮 𝒩 𝒬 ψ hψ) ∧
          (∀ (f : S) (d : ℕ) (hf : f ∈ 𝒮 d) (hd : 0 < d)
              (s : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj
                (op (ProjectiveSpectrum.basicOpen 𝒮 f))),
            ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒩 hf hd
                  ((associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ).val.app _ s) :
                GradedModuleDegreeZeroLocalization 𝒮 𝒩 f) :
                  LocalizedModule.Away (R := S) f N) =
              LocalizedModule.map (Submonoid.powers f) φ
                (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf hd s :
                  GradedModuleDegreeZeroLocalization 𝒮 𝒨 f)) ∧
          (∀ (x : ProjectiveSpectrum.top 𝒮)
              (s : ProjStalkGlobalSections.associatedModuleSheafStalk 𝒮 𝒨 x),
            ((ProjStalkGlobalSections.associatedModuleSheafStalkEquiv 𝒮 𝒩 x
                  (colim.map (Functor.whiskerLeft (OpenNhds.inclusion x).op
                    ((PresheafOfModules.toPresheaf _).map
                      (associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ).val)) s) :
                ProjStalkGlobalSections.degreeZeroModuleAt 𝒮 𝒩 x) :
                  ProjectiveSpectrum.Proj.ModuleFiber (M := N) 𝒮 x) =
              LocalizedModule.map x.asHomogeneousIdeal.toIdeal.primeCompl φ
                (ProjStalkGlobalSections.associatedModuleSheafStalkEquiv 𝒮 𝒨 x s :
                  ProjStalkGlobalSections.degreeZeroModuleAt 𝒮 𝒨 x)) ∧
          (∀ m : 𝒨 0,
            (associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ).val.app (op ⊤)
                (ProjStalkGlobalSections.degreeZeroToGlobalSections 𝒮 𝒨 m) =
              ProjStalkGlobalSections.degreeZeroToGlobalSections 𝒮 𝒩
                ⟨φ m.1, hφ 0 m.1 m.2⟩)) ∧
      (∀ {X Y Z : GradedModuleCat.{u, u, w} 𝒮} (α : X ⟶ Y) (β : Y ⟶ Z),
        Function.Injective α.toLinearMap → Function.Surjective β.toLinearMap →
        ∀ hexact : Function.Exact α.toLinearMap β.toLinearMap,
          (ShortComplex.mk ((associatedModuleSheafFunctor 𝒮).map α)
            ((associatedModuleSheafFunctor 𝒮).map β)
            (associatedModuleSheafFunctor_map_comp_eq_zero α β
              fun m => (hexact (α.toLinearMap m)).mpr ⟨m, rfl⟩)).ShortExact) := by
  refine ⟨fun f _ hf hd => ⟨Proj.basicOpenIsoAway 𝒮 f hf hd⟩,
    fun _ _ hf hd => ⟨ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf hd⟩,
    fun f g d e hf hd hg he hfg =>
      ProjectiveSpectrum.basicOpenIsoAway_restrict 𝒮 f g d e hf hd hg he hfg,
    fun f g hf hg hfg a =>
      ProjectiveSpectrum.Proj.degreeZeroToSection_restriction 𝒮 𝒨 f g hf hg hfg a,
    fun x => ⟨Proj.stalkIso' 𝒮 x⟩,
    fun x => ⟨ProjStalkGlobalSections.associatedModuleSheafStalkLinearEquiv 𝒮 𝒨 x⟩,
    ⟨ProjStalkGlobalSections.degreeZeroRingToGlobalSections 𝒮⟩,
    fun f a => ProjStalkGlobalSections.degreeZeroRingToGlobalSections_basicOpen 𝒮 f a,
    fun x a => ProjStalkGlobalSections.degreeZeroRingToGlobalSections_stalk 𝒮 x a,
    ⟨ProjStalkGlobalSections.degreeZeroToGlobalSections 𝒮 𝒨⟩,
    fun _ _ hf hd m => ProjStalkGlobalSections.degreeZeroToGlobalSections_basicOpen 𝒮 𝒨 hf hd m,
    fun x m => ProjStalkGlobalSections.degreeZeroToGlobalSections_stalk 𝒮 𝒨 x m,
    associatedModuleSheafMap_id 𝒮 𝒨, ?_,
    fun α β hinj hsurj hexact =>
      associatedModuleSheafFunctor_shortExact α β hinj hsurj hexact⟩
  intro N _ _ _ _ _ 𝒩 _ _ φ hφ
  refine ⟨?_, fun _ _ hf hd s => associatedModuleSheafMap_standardOpen 𝒮 𝒨 𝒩 φ hφ hf hd s,
    fun x s => ProjStalkGlobalSections.associatedModuleSheafMap_stalk 𝒮 𝒨 𝒩 φ hφ x s,
    fun m => ProjStalkGlobalSections.degreeZeroToGlobalSections_naturality 𝒮 𝒨 𝒩 φ hφ m⟩
  intro P _ _ _ _ _ 𝒬 _ _ ψ hψ
  exact associatedModuleSheafMap_comp 𝒮 𝒨 𝒩 𝒬 φ hφ ψ hψ

end Stacks.AlgebraicGeometry.ProjSheafFunctoriality

end
