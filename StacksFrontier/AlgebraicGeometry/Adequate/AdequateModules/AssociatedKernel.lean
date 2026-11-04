module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Abelian
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Pullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleOnSite

/-!
# Kernels of maps of associated modules are adequate

Let `S` be a scheme and `𝓖` a quasi-coherent `𝒪_S`-module. The associated `𝒪`-module `𝓖ᵃ` on a
site of schemes over `S` is [Stacks, Tag 03DU]: its sections over a scheme `T` over `S` are the
global sections of the pullback of `𝓖` to `T`. The cokernel of a map `𝓖ᵃ ⟶ 𝓗ᵃ` is again
quasi-coherent, being `(𝓗/𝓖)ᵃ`, but the kernel in general is not. [Stacks, Tag 06VK] says that
it is nevertheless adequate, and that this is a characterisation: an `𝒪`-module on `(Sch/S)_τ`
is adequate exactly when it is, locally on `S`, such a kernel.

This module supplies the associated module on a chosen big site and proves the implications
(2) ⇒ (1), (3) ⇒ (1), (4) ⇒ (1) and (5) ⇒ (1) of that lemma.

## Main definitions

* `Stacks.Adequate.BigSite.associatedModule` is `𝓖ᵃ` on a chosen big site, namely the associated
  module of [Stacks, Tag 03DU] for the site's own category and topology.
* `Stacks.Adequate.AssociatedModuleMap` is a map `𝓖ᵃ ⟶ 𝓗ᵃ` of associated modules of
  quasi-coherent `𝒪_S`-modules, together with the data presenting it as such.
* `Stacks.Adequate.AssociatedKernelPresentation` exhibits a sheaf of modules as the kernel of
  such a map, and `Stacks.Adequate.IsAssociatedKernel` is the existence of such a presentation.
  This is condition (2) of [Stacks, Tag 06VK] for the one-member covering of `S` by itself.
* `Stacks.Adequate.AffineAssociatedSections` is the identification of the affine sections of an
  associated module with a module extension: over an affine `Spec A` of the site over `S` the
  functor `F_{𝓖ᵃ, A}` is `B ↦ B ⊗_A M` for an `A`-module `M`, compatibly with a given map
  `𝓖ᵃ ⟶ 𝓗ᵃ`. It is taken as a hypothesis; see the implementation notes.
* `Stacks.Adequate.IsAdequateOnPullback` and
  `Stacks.Adequate.IsAssociatedKernelOnPullback` read conditions (4) and (3) of
  [Stacks, Tag 06VK] at one member of a covering: the restriction `𝓕|_(Sch/T)_τ` along
  `g : T ⟶ S` is adequate, respectively is such a kernel.

## Main results

* `Stacks.Adequate.affineSectionsFunctor_preservesFiniteLimits` — **affine sections commute with
  finite limits, in particular with kernels, of sheaves of modules on a big site.** The
  affine-section functor is the forgetful functor to presheaves of modules followed by a
  pushforward, and both preserve limits because limits of presheaves of modules are computed
  objectwise and restriction of scalars preserves them.
* `Stacks.Adequate.isAdequate_of_coveringPullback` — the implication (4) ⇒ (1): adequacy
  descends along a `τ`-covering all of whose pullbacks of `𝓕` are adequate. The covering of
  each member by affines composes with the covering of `S`, because
  `Stacks.Adequate.coveringMorphismProperty_comp` makes the composite a covering morphism and
  the affine-section functors along the composite are those of the pullback.

[Stacks, Tag 06VK]'s own implications to adequacy — from a kernel presentation,
`Stacks.Adequate.isAdequate_of_isAssociatedKernel`, and from a covering of such,
`Stacks.Adequate.isAdequate_of_coveringAssociatedKernel` — are stated in
`StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedAffineSections`, together
with the conditions above. They live there rather than here because they are unconditional, and
discharging the identification they used to assume needs the affine base change, which is built
on top of this module; see the implementation notes.

## Implementation notes

The value universe is the universe `u` of the base scheme throughout, because the associated
module of [Stacks, Tag 03DU] has its sections in that universe: they are sections of a module on
a scheme of the site. Adequacy of a module-valued functor is stated with a universe lift, and at
value universe `u` that lift is undone by
`AdequateFunctor.presheafOfModulesUliftIso`.

`Stacks.Adequate.AffineAssociatedSections` is stated here and **proved** downstream, as
`Stacks.Adequate.affineAssociatedSections`. It is the clause of Descent, Proposition 03DX
computing the affine sections of `𝓖ᵃ`: for a morphism `Spec B ⟶ Spec A` of affines over `S` the
sections of `𝓖ᵃ` over `Spec B` are the base change along `A ⟶ B` of its sections over
`Spec A`, which is `Stacks.Sites.affineAssociatedBaseChangeIso`, normalised by
`Stacks.Sites.affineAssociatedBaseChangeIso_hom_one_tmul`; what it asks for is that objectwise
statement assembled into an isomorphism of module-valued functors, together with the module map
underlying a given map of associated modules, which full faithfulness of module extension
supplies.

Because its proof needs the affine base change, which is built on top of this module, it is a
definition here and a theorem one module further on. That is also why the two implications of
[Stacks, Tag 06VK] which consume it are stated there: stating them here would force them to
carry it as a hypothesis, and it is not one. `Stacks.Adequate.IsAssociatedKernelOnPullback`
still carries it as a conjunct, which is harmless — the conjunct is now always satisfiable — and
is left in place so that the condition keeps the shape the source gives it.

The converse implications (1) ⇒ (5) and (1) ⇒ (4), that an adequate module is locally such a
kernel and that its pullbacks are adequate, are not proved here. The second is
[Stacks, Tag 06VJ], `Stacks.Adequate.isAdequate_pullbackSheaf`, under the hypotheses recorded
there. The first is
`Stacks.Adequate.hasAssociatedKernelOnEveryAffine_of_isAdequate` in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AssociatedKernelConverse.lean`, proved
with no hypotheses; it is two modules downstream because it is stated with the packaged
conditions of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/Characterizations.lean`. It does not go
through the quasi-inverse of the equivalence of [Stacks, Tag 06ZJ], of which the library
has only the comparison functor `Stacks.Adequate.adequateComparison`: reconstructing `𝓕` from
`F_{𝓕, A}` in general is what that quasi-inverse would do, while the implication only needs the
case where `F_{𝓕, A}` is a kernel of module extensions, and there
`AlgebraicGeometry.tilde` supplies the quasi-coherent modules. The clause string of
`Stacks.Adequate.isAdequate_of_isAssociatedKernel` still describes the converse as needing that
quasi-inverse.

## References

* [Stacks Project, Tag 06VK](https://stacks.math.columbia.edu/tag/06VK)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06VG](https://stacks.math.columbia.edu/tag/06VG)
* [Stacks Project, Tag 06ZJ](https://stacks.math.columbia.edu/tag/06ZJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-! ### The associated module on a chosen big site -/

/-- **The associated module `𝓖ᵃ` of [Stacks, Tag 03DU] on a chosen big site.** Its sections over
a scheme of the site are the global sections of the pullback of `𝓖` to that scheme. The sheaf
condition for those sections is a parameter, as it is for the general construction. -/
public noncomputable def BigSite.associatedModule (B : BigSite τ S) (G : S.Modules)
    [G.IsQuasicoherent]
    (hG : Presheaf.IsSheaf B.topology (Stacks.Sites.associatedPresheaf S G B.toOver)) :
    SheafOfModules.{u} B.structureSheaf :=
  Stacks.Sites.siteAssociatedModule S G B.toOver B.topology B.isSheaf hG

/-- The sections of `𝓖ᵃ` over a scheme of the site are the global sections of the pullback of
`𝓖` to that scheme. -/
@[simp] public theorem BigSite.associatedModule_presheaf (B : BigSite τ S) (G : S.Modules)
    [G.IsQuasicoherent]
    (hG : Presheaf.IsSheaf B.topology (Stacks.Sites.associatedPresheaf S G B.toOver)) :
    (B.associatedModule G hG).val.presheaf = Stacks.Sites.associatedPresheaf S G B.toOver := rfl

/-! ### Affine sections commute with kernels -/

variable (B : BigSite τ S)

/-- Forgetting the sheaf condition is additive. -/
private instance forget_additive :
    (SheafOfModules.forget B.structureSheaf : SheafOfModules.{u} _ ⥤ _).Additive := ⟨rfl⟩

/-- Forgetting the sheaf condition preserves finite limits, at the value universe `u` this module
works in.

This registers Mathlib's `SheafOfModules.Finite.forgetPreservesFiniteLimits` at the structure
sheaf of a chosen big site. The registration is needed, and is not a duplicate of the general
`Stacks.Adequate.forget_preservesFiniteLimits`: that one is stated at `{max u m}`, and
discharging a `{u}` goal from it would need `max u ?m =?= u`, which Lean's universe unifier does
not invert. Exported, and named apart from the general one, so that the downstream modules of
this chapter share this single registration instead of each declaring its own. -/
public noncomputable instance forget_structureSheaf_preservesFiniteLimits :
    PreservesFiniteLimits
      (SheafOfModules.forget B.structureSheaf : SheafOfModules.{u} _ ⥤ _) :=
  SheafOfModules.Finite.forgetPreservesFiniteLimits B.structureSheaf

variable (A : CommRingCat.{u}) (f : Spec A ⟶ S)

/-- The pushforward computing affine sections is additive. -/
private instance pushforward_additive :
    (PresheafOfModules.pushforward.{u} (affineRingMap B A f)).Additive := ⟨rfl⟩

/-- The affine-section functor is additive. -/
public noncomputable instance affineSectionsFunctor_additive :
    (affineSectionsFunctor.{u, u} B A f).Additive :=
  inferInstanceAs ((SheafOfModules.forget B.structureSheaf ⋙
    PresheafOfModules.pushforward.{u} (affineRingMap B A f)).Additive)

/-- **Affine sections commute with finite limits, in particular with kernels.** The
affine-section functor `𝓕 ↦ F_{𝓕, A}` is the forgetful functor to presheaves of modules followed
by the pushforward along the scalar identification, and both preserve finite limits. -/
public noncomputable instance affineSectionsFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (affineSectionsFunctor.{u, u} B A f) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.forget B.structureSheaf ⋙
    PresheafOfModules.pushforward.{u} (affineRingMap B A f)))

/-! ### Kernel presentations by associated modules -/

/-- A map `𝓖ᵃ ⟶ 𝓗ᵃ` of the associated modules of two quasi-coherent `𝒪_S`-modules on a chosen
big site, with the two modules and their sheaf conditions as part of the data. -/
public structure AssociatedModuleMap (B : BigSite τ S) where
  /-- The quasi-coherent `𝒪_S`-module whose associated module is the source. -/
  source : S.Modules
  /-- The quasi-coherent `𝒪_S`-module whose associated module is the target. -/
  target : S.Modules
  [source_isQuasicoherent : source.IsQuasicoherent]
  [target_isQuasicoherent : target.IsQuasicoherent]
  /-- The sections of the pullbacks of the source form a sheaf on the site. -/
  source_isSheaf :
    Presheaf.IsSheaf B.topology (Stacks.Sites.associatedPresheaf S source B.toOver)
  /-- The sections of the pullbacks of the target form a sheaf on the site. -/
  target_isSheaf :
    Presheaf.IsSheaf B.topology (Stacks.Sites.associatedPresheaf S target B.toOver)
  /-- The map of associated modules. -/
  hom : B.associatedModule source source_isSheaf ⟶ B.associatedModule target target_isSheaf

/-- A presentation of a sheaf of modules on a chosen big site as the kernel of a map
`𝓖ᵃ ⟶ 𝓗ᵃ` of associated modules of quasi-coherent `𝒪_S`-modules. This is the shape of
conditions (2), (3) and (5) of [Stacks, Tag 06VK]. -/
public structure AssociatedKernelPresentation (B : BigSite τ S)
    (F : SheafOfModules.{u} B.structureSheaf) extends AssociatedModuleMap B where
  /-- The sheaf of modules is the kernel of the map of associated modules. -/
  iso : F ≅ kernel toAssociatedModuleMap.hom

/-- A sheaf of modules on a chosen big site is a kernel of associated modules when it admits a
presentation as the kernel of a map `𝓖ᵃ ⟶ 𝓗ᵃ` of associated modules of quasi-coherent
`𝒪_S`-modules. -/
public abbrev IsAssociatedKernel (B : BigSite τ S)
    (F : SheafOfModules.{u} B.structureSheaf) : Prop :=
  Nonempty (AssociatedKernelPresentation B F)

/-- **The affine sections of an associated module are a module extension.** For every affine
scheme `Spec A` of the site over `S` and every map `𝓖ᵃ ⟶ 𝓗ᵃ` of associated modules there are
`A`-modules `M`, `N` and a map `ψ : M ⟶ N` such that the induced map of affine-section functors
is the map `B ↦ B ⊗_A M → B ⊗_A N` of module extensions.

This is the clause of Descent, Proposition 03DX computing the sections of `𝓖ᵃ` over an affine as
a base change, `Stacks.Sites.affineAssociatedBaseChangeIso`, assembled into an isomorphism of
module-valued functors; see the module documentation.

The hypothesis `schemeSizeBelow B.cutoff (Spec A)` corrects the statement. Without it the
quantifier ranges over affine schemes over `S` which need not be objects of the site; at such an
`A` the map `φ.hom`, which is a map of sheaves on the site, has no component over `Spec A`, and
the `A`-module map `ψ` the conclusion asks for does not exist. The only consumer,
`Stacks.Adequate.isAdequate_of_forall_affineSectionFunctor`, supplies that membership.

This narrowing is a strengthening of every result that assumes it, not a weakening of any. The
quantifier appears here in a *hypothesis*: adding `schemeSizeBelow` makes this `Prop` weaker, so
each theorem carrying it as an assumption — the three [Stacks, Tag 06VK] sites below — now demands
strictly less of its caller and concludes the same thing. Nothing downstream proves less. The
previous form was not merely stronger but unsatisfiable in general, which is why it had no proof.
The corrected form is provable, by taking `ψ` to be the component of `φ.hom` over `Spec A`, which
exists precisely because `Spec A` is an object of the site. -/
public abbrev AffineAssociatedSections (B : BigSite τ S) : Prop :=
  ∀ (φ : AssociatedModuleMap B) (A : CommRingCat.{u}) (f : Spec A ⟶ S),
    schemeSizeBelow B.cutoff (Spec A) →
    ∃ (M N : ModuleCat.{u} A) (ψ : M ⟶ N),
      Nonempty (Arrow.mk ((affineSectionsFunctor.{u, u} B A f).map φ.hom) ≅
        Arrow.mk ((AdequateFunctor.moduleExtensionFunctorOn
          (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))).map ψ))

/-! ### Descent of adequacy along a covering -/

/-- Composing two morphisms with the covering morphism property of a topology again has it. -/
public theorem coveringMorphismProperty_comp (σ : CoveringTopology) {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (ha : coveringMorphismProperty σ a)
    (hb : coveringMorphismProperty σ b) :
    coveringMorphismProperty σ (a ≫ b) := by
  cases σ with
  | fppf =>
      exact ⟨MorphismProperty.comp_mem _ _ _ ha.1 hb.1,
        MorphismProperty.comp_mem _ _ _ ha.2 hb.2⟩
  | _ => exact MorphismProperty.comp_mem _ _ _ ha hb

/-- The pullback `g^*𝓕` of `𝓕` along `g : T ⟶ S` is an adequate `𝒪`-module on the big `τ`-site
over `T`. The site over `T` is required to have the cutoff of the site over `S`, so that the
two are slices of one category of schemes, and both it and the sheaf condition for the
restriction are existentially quantified: the source writes `(Sch/T)_τ` for the one site over
`T` cut out by the same cardinal, and `Stacks.Adequate.BigSite` records no comparison between
the topologies over two different bases. -/
public abbrev IsAdequateOnPullback (F : SheafOfModules.{u} B.structureSheaf)
    {T : Scheme.{u}} (g : T ⟶ S) : Prop :=
  ∃ (hT : schemeSizeBelow B.cutoff T)
    (J : GrothendieckTopology (Over (⟨T, hT⟩ : SchemeBelow B.cutoff)))
    (hJ : Presheaf.IsSheaf J (Stacks.Sites.structurePresheaf T
      (Over.post (ObjectProperty.ι (schemeSizeBelow B.cutoff)))))
    (hchosen :
      (τ = .zariski ∧ ∃ Z : BigZariskiSite.{u}, ∃ hTZ : Z.Contains T,
          ∃ _e : Z.schemeCardinal = B.cutoff, HEq J (BigZariskiOver.topology Z T hTZ)) ∨
      (τ = .etale ∧ ∃ E : BigEtaleSite.{u}, ∃ hTE : E.Contains T,
          ∃ _e : E.cutoff = B.cutoff, HEq J (BigEtaleOver.topology E T hTE)) ∨
      (τ = .fppf ∧ ∃ P : BigFppfSite.{u}, ∃ hTP : P.Contains T,
          ∃ _e : P.cutoff = B.cutoff, HEq J (BigFppfOver.topology P T hTP)) ∨
      (τ = .smooth ∧ ∃ M : BigSmoothSite.{u}, ∃ hTM : T.size < M.cutoff,
          ∃ _e : M.cutoff = B.cutoff, HEq J (BigSmoothOver.topology M T hTM)) ∨
      (τ = .syntomic ∧ ∃ Y : BigSyntomicSite.{u}, ∃ hTY : Y.Contains T,
          ∃ _e : Y.cutoff = B.cutoff, HEq J (BigSyntomicOver.topology Y T hTY)))
    (hsh : Presheaf.IsSheaf (B.baseChange hT J hJ hchosen).topology
      (pullbackVal B hT J hJ hchosen g F).presheaf),
    IsAdequate (B.baseChange hT J hJ hchosen) (pullbackSheaf B hT J hJ hchosen g F hsh)

/-- **[Stacks, Tag 06VK], the implication (4) ⇒ (1).** If there is a `τ`-covering
`{gᵢ : Tᵢ → S}` of `S` by schemes of the site such that every pullback `gᵢ^*𝓕` is adequate,
then `𝓕` is adequate.

A `τ`-covering of each `Tᵢ` by affine schemes of the site witnessing adequacy of `gᵢ^*𝓕`
composes with `gᵢ` to a `τ`-covering of `S` by affine schemes of the site, because the covering
morphism property of each topology is stable under composition and the composed family is still
jointly surjective; and the affine-section functors along the composite are those of the
pullback, by `Stacks.Adequate.affineSectionFunctor_pullbackSheaf`. This is the source's "a
composition of `τ`-coverings is a `τ`-covering". -/
public theorem isAdequate_of_coveringPullback (F : SheafOfModules.{u} B.structureSheaf)
    (I : Type (u + 1)) (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ S)
    (hg : ∀ i, coveringMorphismProperty τ (g i))
    (hsurj : (⋃ i, Set.range (g i)) = Set.univ)
    (hadq : ∀ i, IsAdequateOnPullback B F (g i)) :
    IsAdequate B F := by
  classical
  choose hT J hJ hchosen hsh hAd using hadq
  choose K A fj hcov hsurj' hmem using hAd
  refine ⟨(i : I) × K i, fun p => A p.1 p.2, fun p => fj p.1 p.2 ≫ g p.1,
    fun p => coveringMorphismProperty_comp τ _ _ (hcov p.1 p.2) (hg p.1), ?_, ?_⟩
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp (hsurj ▸ Set.mem_univ x)
    obtain ⟨j, z, hz⟩ := Set.mem_iUnion.mp ((hsurj' i) ▸ Set.mem_univ y)
    exact Set.mem_iUnion.mpr ⟨⟨i, j⟩, z, by
      show (g i) ((fj i j) z) = x
      rw [hz, hy]⟩
  · rintro ⟨i, j⟩
    refine ⟨(hmem i j).1, ?_⟩
    have h := (hmem i j).2
    rwa [affineSectionFunctor_pullbackSheaf B (hT i) (J i) (hJ i) (hchosen i) (g i) F
      (hsh i) (A i j) (fj i j)] at h

/-- The restriction of `𝓕` to the big `τ`-site over `T` along `g : T ⟶ S` is the kernel of a map
`𝓖ᵃ ⟶ 𝓗ᵃ` of associated modules of quasi-coherent `𝒪_T`-modules. The site over `T` and the
sheaf condition for the restriction are existentially quantified, as in
`Stacks.Adequate.IsAdequateOnPullback`, and the identification
`Stacks.Adequate.AffineAssociatedSections` for that site is carried along with the
presentation, since it is a statement about the site the presentation lives on. -/
public abbrev IsAssociatedKernelOnPullback (F : SheafOfModules.{u} B.structureSheaf)
    {T : Scheme.{u}} (g : T ⟶ S) : Prop :=
  ∃ (hT : schemeSizeBelow B.cutoff T)
    (J : GrothendieckTopology (Over (⟨T, hT⟩ : SchemeBelow B.cutoff)))
    (hJ : Presheaf.IsSheaf J (Stacks.Sites.structurePresheaf T
      (Over.post (ObjectProperty.ι (schemeSizeBelow B.cutoff)))))
    (hchosen :
      (τ = .zariski ∧ ∃ Z : BigZariskiSite.{u}, ∃ hTZ : Z.Contains T,
          ∃ _e : Z.schemeCardinal = B.cutoff, HEq J (BigZariskiOver.topology Z T hTZ)) ∨
      (τ = .etale ∧ ∃ E : BigEtaleSite.{u}, ∃ hTE : E.Contains T,
          ∃ _e : E.cutoff = B.cutoff, HEq J (BigEtaleOver.topology E T hTE)) ∨
      (τ = .fppf ∧ ∃ P : BigFppfSite.{u}, ∃ hTP : P.Contains T,
          ∃ _e : P.cutoff = B.cutoff, HEq J (BigFppfOver.topology P T hTP)) ∨
      (τ = .smooth ∧ ∃ M : BigSmoothSite.{u}, ∃ hTM : T.size < M.cutoff,
          ∃ _e : M.cutoff = B.cutoff, HEq J (BigSmoothOver.topology M T hTM)) ∨
      (τ = .syntomic ∧ ∃ Y : BigSyntomicSite.{u}, ∃ hTY : Y.Contains T,
          ∃ _e : Y.cutoff = B.cutoff, HEq J (BigSyntomicOver.topology Y T hTY)))
    (hsh : Presheaf.IsSheaf (B.baseChange hT J hJ hchosen).topology
      (pullbackVal B hT J hJ hchosen g F).presheaf),
    AffineAssociatedSections (B.baseChange hT J hJ hchosen) ∧
      IsAssociatedKernel (B.baseChange hT J hJ hchosen)
        (pullbackSheaf B hT J hJ hchosen g F hsh)

end Stacks.Adequate

end
