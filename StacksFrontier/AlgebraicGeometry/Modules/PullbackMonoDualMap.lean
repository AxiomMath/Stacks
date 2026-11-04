module

public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit

/-!
# The dual of a surjection of finite locally free modules is universally injective

Let `X` be a scheme and let `q : 𝒜 ⟶ ℰ` be an epimorphism of `𝒪_X`-modules with `𝒜` and `ℰ`
finite locally free.  Then the dual morphism `q^∨ : ℰ^∨ ⟶ 𝒜^∨` stays a monomorphism after an
*arbitrary* base change: for every morphism of schemes `g : W ⟶ X` the pullback `g^*(q^∨)` is a
monomorphism of `𝒪_W`-modules.

The reason is that `q^∨` is split injective at every point, and a split injection survives any
base change.  At `x : X` the stalk map `q_x : 𝒜_x ↠ ℰ_x` is a surjection onto a free module of
finite rank, hence onto a projective module, so it admits a section `σ : ℰ_x →ₗ 𝒜_x` with
`q_x ∘ σ = id`.  Tag 01CP identifies the stalk of a dual with the dual of the stalk and the
stalk of `q^∨` with precomposition by `q_x`, so `σ^∨`, read through that identification, is a
retraction of `(q^∨)_x`.

Base change is then formal.  Monomorphy of a morphism of `𝒪_W`-modules is injectivity of all of
its stalk maps, and Tag 0098 computes the stalk of a pullback at `w : W` as the extension of
scalars `𝒪_{W,w} ⊗_{𝒪_{X,g w}} (-)_{g w}`, *naturally in the module*.  Naturality turns the
stalk of `g^*φ` at `w` into a conjugate, by two isomorphisms, of the image of the stalk of `φ`
at `g w` under extension of scalars; a split monomorphism is carried to a split monomorphism by
any functor, hence to a monomorphism, and conjugating by isomorphisms preserves that.

## Main results

* `Stacks.AlgebraicGeometry.ReflexiveModules.modulesStalkFunctor_map_apply`: the stalk functor
  of Tag 0098 and the `stalkHom` vocabulary induce the same map on stalks.
* `Stacks.AlgebraicGeometry.ReflexiveModules.mono_pullback_map_of_forall_stalk_splitInjective`:
  **a morphism of `𝒪_X`-modules which is split injective on every stalk is universally
  monomorphic** — its pullback along every morphism of schemes `g : W ⟶ X` is a monomorphism.
* `Stacks.AlgebraicGeometry.ReflexiveModules.mono_pullback_map_dualMap_of_epi`: **the dual of an
  epimorphism of finite locally free modules is universally injective.**

## Implementation notes

Three vocabularies for the stalk of a morphism of `𝒪_X`-modules meet here, and the file is
mostly the bookkeeping that joins them.  `AlgebraicGeometry.SheafOfModules.stalkMap`, whose
scalars are the `RingCat`-valued stalk of the sheaf of rings, is the one the stalkwise criterion
for monomorphy is stated with; `Stacks.SheafOfModules.SheafHomStalk.stalkHom` and
`Stacks.ModuleSkyscraper.modulesStalkFunctor` are over the `CommRingCat`-valued stalk, i.e. over
the local ring, which is where extension of scalars and the dual stalk comparison live.  The
first two are identified by `stalkMap_apply_eq_stalkHom` of
`StacksFrontier/AlgebraicGeometry/Modules/DualShortExact.lean`, the last two by
`modulesStalkFunctor_map_apply` below; both identifications are germ chases, both maps sending
the germ of a local section to the germ of its image.

The local ring itself also has two spellings, `Stacks.SheafOfModules.SheafHomStalk.ringStalk
X.sheaf x` and `X.presheaf.stalk x`, which are definitionally equal but not syntactically so,
and the `Module` instance on a stalk is registered only at the second
(`AlgebraicGeometry.Scheme.Modules.moduleStalk`).  The hypothesis of
`mono_pullback_map_of_forall_stalk_splitInjective` is therefore stated at the
`X.presheaf.stalk` spelling, matching `exists_stalkHom_retraction`, the other producer of such
retractions.  The retraction is turned into a morphism of `ModuleCat` by
`ModuleCat.homEquiv.symm` rather than by `ModuleCat.ofHom`: the latter rebuilds its source and
target with `ModuleCat.of`, which runs an instance search for the module structure on the stalk
in the spelling `((SheafOfModules.forget X.ringCatSheaf).obj N).presheaf`, and that search does
not reach `moduleStalk`; with `homEquiv` the two objects come from the expected type and only a
definitional check of the linear map remains.

A type ascription does not help there, and this is worth recording: `(r : T)` for a local
hypothesis `r` elaborates to `r` itself, so the ascription is discarded and the ambient
spelling is the one in the local context.  Where a different spelling really is needed — the
section `σ` of `q_x`, which `Module.projective_lifting_property` produces over
`ringStalk X.sheaf x` while `LinearMap.dualMap` has to be applied to it over
`X.presheaf.stalk x`, on pain of being asked for a `RingHomCompTriple` between two
syntactically distinct identity ring homomorphisms — it is reintroduced by an `obtain` against
an explicitly stated existential.

The hypotheses of finite local freeness are explicit arguments rather than instances, since the
consumer of this file has them as data; they are taken at the tagged class
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` and crossed to
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree` by
`Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree` where the finite-presentation
consequence is needed.  Finite presentation of `𝒜` and of `ℰ` is *not* an extra hypothesis: it
follows from finite local freeness, and it is what Tag 01CP's dual stalk comparison requires.
No Noetherian or quasi-coherence hypothesis is used, and no hypothesis at all is placed on the
base change `g`.

## References

* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.SheafHomStalk
open Stacks.ModuleSkyscraper

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

variable {X W : Scheme.{u}}

/-! ### The stalk functor of Tag 0098 and the `stalkHom` vocabulary -/

/-- The stalk functor on `𝒪_X`-modules used by the pullback stalk formula of Tag 0098 induces
`stalkHom` on a morphism: both send the germ of a local section to the germ of its image.  This
is the companion of `stalkMap_apply_eq_stalkHom`, which performs the same identification for the
stalk map over the `RingCat`-valued stalk of the sheaf of rings. -/
theorem modulesStalkFunctor_map_apply {M N : X.Modules} (φ : M ⟶ N) (x : X)
    (m : modStalk M x) :
    ((modulesStalkFunctor X x).map φ).hom m = stalkHom φ x m := by
  obtain ⟨V, hxV, t, rfl⟩ := exists_germ_eq M m
  rw [stalkHom_germAt φ x V hxV t]
  exact Stacks.Modules.stalkLinearMap_germ (O := X.presheaf) φ.val V hxV t

/-! ### Split injectivity on stalks is universal monomorphy -/

/-- **A morphism of `𝒪_X`-modules which is split injective on every stalk is universally
monomorphic.**  If `φ : M ⟶ N` admits, at every point `x`, a retraction of its stalk map, then
`g^*φ` is a monomorphism for every morphism of schemes `g : W ⟶ X`.

Monomorphy of `g^*φ` is injectivity of its stalk map at every `w : W`; by the naturality in the
module of the pullback stalk formula of Tag 0098, that map is conjugate by two isomorphisms to
the image of the stalk map of `φ` at `g w` under extension of scalars along `𝒪_{X,g w} →
𝒪_{W,w}`.  The retraction makes the latter a split monomorphism, functors preserve split
monomorphisms, and conjugating by isomorphisms preserves monomorphy. -/
theorem mono_pullback_map_of_forall_stalk_splitInjective (g : W ⟶ X)
    {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ r : N.presheaf.stalk x →ₗ[X.presheaf.stalk x] M.presheaf.stalk x,
      ∀ m : modStalk M x, r (stalkHom φ x m) = m) :
    Mono ((Scheme.Modules.pullback g).map φ) := by
  refine (AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap
    (O := structureSheaf W.sheaf) ((Scheme.Modules.pullback g).map φ)).2 fun w a b hab => ?_
  obtain ⟨r, hr⟩ := h (g.base w)
  have hsm : SplitMono ((modulesStalkFunctor X (g.base w)).map φ) :=
    { retraction := ModuleCat.homEquiv.symm r
      id := ModuleCat.hom_ext (LinearMap.ext fun m =>
        (congrArg r (modulesStalkFunctor_map_apply φ (g.base w) m)).trans (hr m)) }
  have : IsSplitMono ((modulesStalkFunctor X (g.base w) ⋙
      ModuleCat.extendScalars (g.stalkMap w).hom).map φ) :=
    IsSplitMono.mk' (hsm.map (ModuleCat.extendScalars (g.stalkMap w).hom))
  have hmono : Mono ((Scheme.Modules.pullback g ⋙ modulesStalkFunctor W w).map φ) := by
    have hfac : (Scheme.Modules.pullback g ⋙ modulesStalkFunctor W w).map φ =
        inv ((pullbackStalkIso g w).hom.app M) ≫
          ((modulesStalkFunctor X (g.base w) ⋙
            ModuleCat.extendScalars (g.stalkMap w).hom).map φ ≫
              (pullbackStalkIso g w).hom.app N) := by
      rw [(pullbackStalkIso g w).hom.naturality φ]
      simp
    rw [hfac]
    infer_instance
  have key (c) : ((Scheme.Modules.pullback g ⋙ modulesStalkFunctor W w).map φ).hom c =
      (AlgebraicGeometry.SheafOfModules.stalkMap (structureSheaf W.sheaf) w
        ((Scheme.Modules.pullback g).map φ)).hom c :=
    (modulesStalkFunctor_map_apply _ w c).trans (stalkMap_apply_eq_stalkHom _ w c).symm
  exact (ModuleCat.mono_iff_injective _).1 hmono ((key a).trans (hab.trans (key b).symm))

/-! ### The dual of a surjection of finite locally free modules -/

/-- **The dual of an epimorphism of finite locally free modules is universally injective.**  For
an epimorphism `q : 𝒜 ⟶ ℰ` of `𝒪_X`-modules with `𝒜` and `ℰ` finite locally free, the dual
morphism `q^∨ : ℰ^∨ ⟶ 𝒜^∨` pulls back to a monomorphism along *every* morphism of schemes
`g : W ⟶ X`.

At a point `x` the stalk map `q_x` is surjective onto `ℰ_x`, which is free of finite rank over
the local ring, hence projective; so `q_x` has a section `σ`.  Under the identification of Tag
01CP of the stalk of a dual with the dual of the stalk, the stalk of `q^∨` is precomposition
with `q_x`, so precomposition with `σ` is a retraction of it; `q^∨` is therefore split injective
at every stalk, and `mono_pullback_map_of_forall_stalk_splitInjective` applies. -/
theorem mono_pullback_map_dualMap_of_epi (g : W ⟶ X) {A E : X.Modules}
    (q : A ⟶ E) (hq : Epi q)
    (hA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) A)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    Mono ((Scheme.Modules.pullback g).map (dualMap q)) := by
  have := hA
  have := hE
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) A :=
    Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree A
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E :=
    Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree E
  have : A.IsFinitePresentation := Stacks.FiniteLocallyFree.isFinitePresentation A
  have : E.IsFinitePresentation := Stacks.FiniteLocallyFree.isFinitePresentation E
  refine mono_pullback_map_of_forall_stalk_splitInjective g (dualMap q) fun x => ?_
  have : Module.Free (ringStalk X.sheaf x) (modStalk E x) :=
    (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree E x).1
  obtain ⟨σ, hσ⟩ : ∃ σ : E.presheaf.stalk x →ₗ[X.presheaf.stalk x] A.presheaf.stalk x,
      ∀ m : modStalk E x, stalkHom q x (σ m) = m := by
    obtain ⟨σ₀, hσ₀⟩ := Module.projective_lifting_property (stalkHom q x) LinearMap.id
      (surjective_stalkHom q hq x)
    exact ⟨σ₀, fun m => LinearMap.congr_fun hσ₀ m⟩
  refine ⟨((dualStalkEquiv E x).symm.toLinearMap).comp
    (σ.dualMap.comp (dualStalkEquiv A x).toLinearMap), fun ψ => ?_⟩
  refine (LinearEquiv.symm_apply_eq _).2 (LinearMap.ext fun m => ?_)
  exact (dualStalkEquiv_stalkHom_dualMap q x ψ (σ m)).trans
    (congrArg (dualStalkEquiv E x ψ) (hσ m))

end Stacks.AlgebraicGeometry.ReflexiveModules

end
