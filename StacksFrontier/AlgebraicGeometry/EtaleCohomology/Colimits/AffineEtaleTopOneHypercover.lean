module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineLimitEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcqsEtaleCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiSeparated.AffineOneHypercover
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BoundedCovering
public import
  StacksFrontier.CategoryTheory.Sites.InverseSystem.AbelianGlobalSectionsOfColimitOfFiniteSites

/-! # A finite one-hypercover of the terminal sheaf of a small affine etale site

The small affine etale site of a scheme `S` has a terminal object only when `S` is affine, so the
global sections of that site are not the sections over any object of it. What replaces the
terminal object for a quasi-compact quasi-separated `S` is a **finite one-hypercover of the
terminal sheaf** in the sense of
`Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercover`: finitely many objects `W k` which
jointly cover the terminal sheaf, together with, for each pair `(k, l)`, finitely many objects
`P k l m` through which any two morphisms into `W k` and `W l` locally factor. That notion is the
hypothesis of the degree-zero Cech step of Stacks 09YQ,
`Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit`, and this
file supplies its geometric instance.

The data is the affine one-hypercover of opens of
`Stacks.QcqsOneHypercover.exists_finite_affine_oneHypercover_opens`: a finite affine open cover
`U k` of `S` together with finite affine open covers `V k l m` of the intersections `U k ⊓ U l`,
which exist because `S` is quasi-compact and quasi-separated. Each of those opens is an object of
the small affine etale site, an open immersion being etale
(`Stacks.EtaleCohomology.QcqsLimitCohomology.objOfAffineOpen`).

Everything is stated at an arbitrary **small model** `C` of the small affine etale site of `S` —
a small category together with a functor `E : C ⥤ SmallAffineEtale B S hS` which is an
equivalence of categories and an inclusion of a dense subsite. That is forced:
`IsTopOneHypercover` is stated for a `SmallCategory`, and the objects of
`AlgebraicGeometry.SmallAffineEtale B S hS` live one universe above its morphisms. The levels of
the site system of Stacks 0EYL and the universe raise of the site of its limit are exactly such
models, by `Stacks.EtaleCohomology.AffineLimitCohomology.isDenseSubsite_levelFunctor` and by
`CategoryTheory.AsSmall.isDenseSubsite_down`. The raise needs the *down* direction: a model of a
site `A` is a functor into `A`, and for the raise that functor is `AsSmall.down`.

The file then does the same for the **base changes** of those objects along an arbitrary morphism
`g : S' ⟶ S`, which is what makes one chosen hypercover at one level of the system of Stacks 0EYL
a hypercover at every level below it and in the site of the limit — the two hypotheses `hlev` and
`hC` of the degree-zero Cech step. Those base changes are not the objects attached to any opens;
they are pinned only by their fibre-product squares, and `isTopOneHypercover_of_lifts` is the
statement that separates the family of objects from the family of opens it stands over so that
both cases are instances of it.

## Main definitions

* `modelObjOfAffineOpen` — the object of the model attached to an affine open of `S`.
* `modelHomOfLE` — the morphism of the model attached to an inclusion of affine opens.
* `objOfOpenOver` — an affine open of the scheme of an object of the small affine etale site,
  as an object of that site.
* `modelObjOfAffineOpenIso` — the comparison isomorphism of the model at the object attached to an
  affine open, read in schemes, with its codomain ascribed as that open.
* `baseChangeHom`, `baseChangeHomOfRange` — the morphisms into a base change produced by lifting a
  factorisation along the fibre-product square.
* `IsCompatibleLegsOfTypes`, `IsUniversalLegsOfTypes` — a presentation of a sheaf of sets on the
  site of the limit as the colimit of the inverse images of a system of sheaves of sets on the
  levels. The library has `InverseSystemOfFiniteSites.IsColimitPresentation` only for abelian
  sheaves.

## Main results

* `ofObjects_mem_topology_of_mem` — a family of objects of the small affine etale site which
  absorbs every object landing in a corresponding open generates a covering sieve of every object
  landing in the union of those opens. This is where the geometry is: affine opens of the source
  form a basis, and a jointly surjective family is a covering
  (`AlgebraicGeometry.SmallEtale.mem_topology_of_jointlySurjective`, read across the dense subsite
  `AlgebraicGeometry.SmallAffineEtale.inclusion`).
* `isTopOneHypercover_of_lifts` — such a family, over a system of opens covering `S` and its
  pairwise intersections, is a one-hypercover of the terminal sheaf of the model.
* `isTopOneHypercover_modelObjOfAffineOpen` — **an affine one-hypercover of opens of `S` is a
  one-hypercover of the terminal sheaf of any small model of the small affine etale site of `S`.**
* `exists_finite_isTopOneHypercover` — the same with the data existentially quantified and its
  index types in `Type`, which is the shape the degree-zero Cech step consumes, for `S`
  quasi-compact and quasi-separated.
* `isTopOneHypercover_baseChange` — **the base changes along `g : S' ⟶ S` of the objects attached
  to an affine one-hypercover of opens of `S` are a one-hypercover of the terminal sheaf of any
  small model of the small affine etale site of `S'`**, over the preimage opens.
* `exists_finite_isTopOneHypercover_level_transition` — **the hypotheses `hlev` and `hC` of the
  degree-zero Cech step of Stacks 09YQ, discharged at the site system of Stacks 0EYL** for a
  quasi-compact quasi-separated level.
* `globalSections_colimit_of_level` — **Stacks 09YP over the terminal sheaf, in degree zero**, at
  that system: the global sections of `colim_i f_i^{-1}F_i` are the filtered colimit of the global
  sections of the `F_n`, with no hypothesis left about covers.
* `globalSections_colimit_of_level_ab` — **the same for ABELIAN sheaves**, with the global sections
  those of Mathlib's `CategoryTheory.Sheaf.Γ` and the colimit presentation the library's
  `InverseSystemOfFiniteSites.IsColimitPresentation`.
* `rightDerivedZeroIsoGammaLimit`, `rightDerivedZeroIsoGammaLevel` — **the zeroth right derived
  functor of global sections is global sections**, at the site of the limit and at a level:
  `CategoryTheory.Sheaf.Γ` is a right adjoint, hence left exact.
* `rightDerivedZero_globalSections_colimit_of_level_ab` — **Stacks 09YP over the terminal sheaf in
  degree zero at its own vertex** `(CategoryTheory.Sheaf.Γ _ Ab).rightDerived 0`.

## Implementation notes

The two matching conditions of `IsTopOneHypercover.locally_factors` are automatic here and cost
nothing: the structure morphism of the object attached to an affine open is an open immersion,
hence a monomorphism, so an object of the site has **at most one** morphism to it
(`hom_ext_objOfAffineOpen`, `model_hom_ext`). The same holds for a base change of such an object,
a monomorphism staying one under base change (`baseChange_hom_ext`). The content of
`locally_factors` is therefore only that the `V k l m` cover `U k ⊓ U l`, which is
quasi-separatedness of `S`.

No affineness of `S` is used anywhere, and no separatedness: the pairwise intersections of the
`U k` are covered by the second layer rather than being affine, which is exactly what the
one-hypercover shape is for. In the base-change section no affineness of `g`, of `S` or of `S'` is
used either, and the preimage opens `g ⁻¹ᵁ U k` are nowhere claimed to be affine: that they are is
true but not needed, the base changes being objects of an affine etale site by construction.

Two spellings have to be kept apart by hand. The scheme of the object attached to an affine open
`U` is `U` itself, but only definitionally (`toScheme_objOfAffineOpen`), and instance search does
not see `AlgebraicGeometry.IsOpenImmersion U.ι` or `Mono U.ι` through that identification; so the
lift of `objOfAffineOpenHomOfRange` is type-ascribed and the comparison isomorphism is hoisted
into `modelObjOfAffineOpenIso`, whose codomain is ascribed as `U`. Likewise the two halves of a
colimit presentation of sheaves of sets are named (`IsCompatibleLegsOfTypes`,
`IsUniversalLegsOfTypes`) rather than written inline: spelled out, they put the statement of
`globalSections_colimit_of_level` over the elaborator's default heartbeat budget. The abelian
statements are named for the same reason — `IsGlobalSectionsMapAb`,
`IsColimitGlobalSectionsAb`, `IsColimitRightDerivedZeroGlobalSectionsAb` and
`transitionOfGlobalSection` — the heartbeat budget being shared between the statement and the
proof of one declaration.

Additivity of `CategoryTheory.Sheaf.Γ` is needed already in the *statement* of
`rightDerivedZeroIsoGammaLimit`, `CategoryTheory.Functor.rightDerived` asking for it, so it is
pinned as a local instance (`additive_Γ_limitSite_pinned`, `additive_Γ_level_pinned`) rather than
supplied inside the proof; likewise
`Stacks.EtaleCohomology.AffineLimitCohomology.hasSheafify_level` and `hasSheafify_limitSite`,
without which instance search for `HasWeakSheafify` — which `CategoryTheory.Sheaf.Γ` asks for —
runs past its heartbeat budget.

## References

* [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks 09YP](https://stacks.math.columbia.edu/tag/09YP)
* [Stacks 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v u

namespace Stacks.EtaleCohomology.AffineEtaleTopOneHypercover

open AlgebraicGeometry
open Stacks.EtaleCohomology.QcqsLimitCohomology Stacks.EtaleCohomology.AffineLimitCohomology

/-- **A finite affine one-hypercover of opens of a quasi-compact quasi-separated scheme, indexed
in `Type`.** This is `Stacks.QcqsOneHypercover.exists_finite_affine_oneHypercover_opens` with its
two finite index types reindexed along `Finite.exists_equiv_fin`, so that they live in `Type`
rather than in the universe of the scheme: the degree-zero Cech step of Stacks 09YQ,
`Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit`, asks for its
two index types in `Type`. -/
theorem exists_finite_affine_oneHypercover_opens_fin (S : Scheme.{u}) [CompactSpace S]
    [QuasiSeparatedSpace S] :
    ∃ (κ ν : Type) (_ : Finite κ) (_ : Finite ν) (U : κ → S.Opens)
      (V : κ → κ → ν → S.Opens),
      (∀ k, IsAffineOpen (U k)) ∧ (∀ k l m, IsAffineOpen (V k l m)) ∧
        (⨆ k, U k) = ⊤ ∧ (∀ k l m, V k l m ≤ U k ⊓ U l) ∧
          ∀ k l, (⨆ m, V k l m) = U k ⊓ U l := by
  obtain ⟨κ, ν, hκ, hν, U, V, hUaff, hVaff, hUtop, hVle, hVsup⟩ :=
    Stacks.QcqsOneHypercover.exists_finite_affine_oneHypercover_opens S
  obtain ⟨n, ⟨eκ⟩⟩ := Finite.exists_equiv_fin κ
  obtain ⟨n', ⟨eν⟩⟩ := Finite.exists_equiv_fin ν
  refine ⟨Fin n, Fin n', inferInstance, inferInstance,
    fun k => U (eκ.symm k), fun k l m => V (eκ.symm k) (eκ.symm l) (eν.symm m),
    fun k => hUaff _, fun k l m => hVaff _ _ _, ?_, fun k l m => hVle _ _ _, fun k l => ?_⟩
  · rwa [eκ.symm.surjective.iSup_comp U]
  · rw [eν.symm.surjective.iSup_comp (fun m => V (eκ.symm k) (eκ.symm l) m)]
    exact hVsup _ _

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The scheme of an object of the small affine etale site of `S` is contained in the big etale
site `B`. -/
lemma contains_toScheme_obj (Z : AlgebraicGeometry.SmallAffineEtale B S hS) :
    B.Contains ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z) :=
  Z.obj.obj.left.2

/-- A morphism of schemes over `S` between the schemes of two objects is a morphism of the
small affine etale site. -/
def homOfSchemeHom {Z W : AlgebraicGeometry.SmallAffineEtale B S hS}
    (t : (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z ⟶
      (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj W)
    (ht : t ≫ structMap B S hS W = structMap B S hS Z) : Z ⟶ W :=
  ObjectProperty.homMk (ObjectProperty.homMk
    (Over.homMk (B.inclusion.preimage t) (by
      apply B.inclusion.map_injective
      rwa [Functor.map_comp, Functor.map_preimage])))

/-- The morphism of schemes underlying `homOfSchemeHom t ht` is `t`. -/
@[simp] lemma toScheme_map_homOfSchemeHom {Z W : AlgebraicGeometry.SmallAffineEtale B S hS}
    (t : (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z ⟶
      (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj W)
    (ht : t ≫ structMap B S hS W = structMap B S hS Z) :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map (homOfSchemeHom B S hS t ht) = t :=
  B.inclusion.map_preimage t

/-- An affine open of the scheme of an object of the small affine etale site is again an
object. -/
def objOfOpenOver (Z : AlgebraicGeometry.SmallAffineEtale B S hS)
    (A : ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z).Opens)
    (hA : AlgebraicGeometry.IsAffineOpen A) :
    AlgebraicGeometry.SmallAffineEtale B S hS :=
  haveI : IsAffine (A : Scheme.{u}) := hA
  haveI hc : B.Contains (A : Scheme.{u}) :=
    Scheme.size_lt_of_isOpenImmersion A.ι (contains_toScheme_obj B S hS Z)
  ⟨⟨Over.mk (B.inclusion.preimage (X := B.obj (A : Scheme.{u}) hc) (Y := B.obj S hS)
      (A.ι ≫ structMap B S hS Z)), by
      change AlgebraicGeometry.Etale (B.inclusion.map (B.inclusion.preimage _))
      rw [Functor.map_preimage]
      infer_instance⟩, by
    change AlgebraicGeometry.IsAffine (A : Scheme.{u})
    infer_instance⟩

/-- The scheme of `objOfOpenOver Z A hA` is the open subscheme `A`. -/
lemma toScheme_objOfOpenOver (Z : AlgebraicGeometry.SmallAffineEtale B S hS)
    (A : ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z).Opens)
    (hA : AlgebraicGeometry.IsAffineOpen A) :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj (objOfOpenOver B S hS Z A hA) =
      (A : Scheme.{u}) := rfl

/-- The structure morphism of `objOfOpenOver Z A hA` is the open immersion of `A` followed by the
structure morphism of `Z`. -/
lemma structMap_objOfOpenOver (Z : AlgebraicGeometry.SmallAffineEtale B S hS)
    (A : ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z).Opens)
    (hA : AlgebraicGeometry.IsAffineOpen A) :
    structMap B S hS (objOfOpenOver B S hS Z A hA) = A.ι ≫ structMap B S hS Z :=
  B.inclusion.map_preimage _

open Stacks.EtaleCohomology.BaseChangeAlgebraSystem in
attribute [local instance] isDenseSubsite_smallAffineEtaleInclusion

/-- Two morphisms of the small affine etale site into an object with monomorphic structure
morphism agree: both are morphisms over `S`. -/
private theorem hom_ext_of_mono_structMap {X V : AlgebraicGeometry.SmallAffineEtale B S hS}
    [Mono (structMap B S hS X)] (t t' : V ⟶ X) : t = t' :=
  (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map_injective <| (cancel_mono _).mp <|
    (toScheme_map_comp_structMap B S hS t).trans (toScheme_map_comp_structMap B S hS t').symm

/-- An object of the small affine etale site admits at most one morphism to the object attached
to an affine open of `S`: the structure morphism of the latter is an open immersion, hence a
monomorphism, and the functor to schemes is faithful. -/
lemma hom_ext_objOfAffineOpen {V : AlgebraicGeometry.SmallAffineEtale B S hS}
    (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U)
    (t t' : V ⟶ objOfAffineOpen B S hS U hU) : t = t' := by
  have : Mono (structMap B S hS (objOfAffineOpen B S hS U hU)) := by
    rw [structMap_objOfAffineOpen B S hS U hU]
    exact inferInstanceAs (Mono U.ι)
  exact hom_ext_of_mono_structMap B S hS t t'

/-- The scheme of the object attached to an affine open is that open. -/
lemma toScheme_objOfAffineOpen (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj (objOfAffineOpen B S hS U hU) =
      (U : Scheme.{u}) := rfl

/-- **An object whose structure morphism has image inside an affine open `U` of `S` maps to the
object attached to `U`**: lift the structure morphism along the open immersion `U ⟶ S`.

The lift is ascribed the type `... ⟶ (U : Scheme)` rather than left to the expected type
`... ⟶ toScheme.obj (objOfAffineOpen U)`. The two are the same by `toScheme_objOfAffineOpen`, but
only definitionally, and `AlgebraicGeometry.IsOpenImmersion.lift` takes
`AlgebraicGeometry.IsOpenImmersion U.ι` as an instance argument, which instance search does not
find at the second spelling. -/
def objOfAffineOpenHomOfRange (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U)
    (V : AlgebraicGeometry.SmallAffineEtale B S hS)
    (hr : Set.range (structMap B S hS V) ⊆ (U : Set S)) :
    V ⟶ objOfAffineOpen B S hS U hU := by
  have hr' : Set.range (structMap B S hS V) ⊆ Set.range U.ι := by
    rwa [AlgebraicGeometry.Scheme.Opens.range_ι]
  refine homOfSchemeHom B S hS (W := objOfAffineOpen B S hS U hU)
    (AlgebraicGeometry.IsOpenImmersion.lift U.ι (structMap B S hS V) hr' :
      (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj V ⟶ (U : Scheme.{u})) ?_
  rw [structMap_objOfAffineOpen B S hS U hU]
  exact AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hr'

/-- **A family of objects which absorbs every object landing in a corresponding open generates a
covering sieve.** Let `O k` be opens of `S` and let `Zk k` be objects of the small affine etale
site such that every object whose structure morphism has image inside `O k` admits a morphism to
`Zk k`. Then the `Zk k` generate a covering sieve of every object whose structure morphism lands
in the union of the `O k`.

This is where the geometry is: affine opens of the source form a basis, so the object is covered
by affine opens each of which lands in a single `O k`, and a jointly surjective family of etale
objects is a covering
(`AlgebraicGeometry.SmallEtale.mem_topology_of_jointlySurjective`, read across the dense subsite
`AlgebraicGeometry.SmallAffineEtale.inclusion`).

The objects attached to a family of affine opens of `S` are the case `Zk k = objOfAffineOpen (O k)`
whose hypothesis is `objOfAffineOpenHomOfRange`. The *base changes* of such objects along a
morphism `g : S' ⟶ S` are the case the transition hypercovers run on, and there the opens are the
preimages `g ⁻¹ᵁ O k`: that is the point of stating the family and the opens separately, since a
base change is pinned only by a fibre-product square and is not the object attached to any
particular open. -/
theorem ofObjects_mem_topology_of_mem
    {κ : Type*} (O : κ → S.Opens) (Zk : κ → AlgebraicGeometry.SmallAffineEtale B S hS)
    (hlift : ∀ (k : κ) (V : AlgebraicGeometry.SmallAffineEtale B S hS),
      Set.range (structMap B S hS V) ⊆ (O k : Set S) → Nonempty (V ⟶ Zk k))
    (Z : AlgebraicGeometry.SmallAffineEtale B S hS)
    (hZ : ∀ x : (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z,
      ∃ k, (structMap B S hS Z).base x ∈ O k) :
    Sieve.ofObjects Zk Z ∈ AlgebraicGeometry.SmallAffineEtale.topology B S hS Z := by
  classical
  rw [← Functor.IsDenseSubsite.functorPushforward_mem_iff
    (J := AlgebraicGeometry.SmallAffineEtale.topology B S hS)
    (K := AlgebraicGeometry.SmallEtale.topology B S hS)
    (G := AlgebraicGeometry.SmallAffineEtale.inclusion B S hS)]
  refine AlgebraicGeometry.SmallEtale.mem_topology_of_jointlySurjective ?_
  intro x
  obtain ⟨k, hk⟩ := hZ x
  -- an affine open of the scheme of `Z` through `x` inside the preimage of `O k`
  have hbasis := ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z).isBasis_affineOpens
  obtain ⟨A, hA, hxA, hle⟩ :
      ∃ A : ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj Z).Opens,
        AlgebraicGeometry.IsAffineOpen A ∧ x ∈ A ∧ A ≤ (structMap B S hS Z) ⁻¹ᵁ O k := by
    obtain ⟨-, ⟨A, hA, rfl⟩, hxA, hAsub⟩ :=
      hbasis.exists_subset_of_mem_open
        (show x ∈ ((structMap B S hS Z) ⁻¹ᵁ O k : Scheme.Opens _) from hk)
        ((structMap B S hS Z) ⁻¹ᵁ O k).isOpen
    exact ⟨A, hA, hxA, hAsub⟩
  have hrange : Set.range (structMap B S hS (objOfOpenOver B S hS Z A hA)) ⊆ (O k : Set S) := by
    rw [structMap_objOfOpenOver B S hS Z A hA]
    rintro - ⟨a, rfl⟩
    exact hle a.2
  obtain ⟨ιk⟩ := hlift k (objOfOpenOver B S hS Z A hA) hrange
  let ι₀ : objOfOpenOver B S hS Z A hA ⟶ Z :=
    homOfSchemeHom B S hS (Z := objOfOpenOver B S hS Z A hA) (W := Z) A.ι
      (structMap_objOfOpenOver B S hS Z A hA).symm
  have hmap : (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map ι₀ = A.ι :=
    toScheme_map_homOfSchemeHom B S hS _ _
  refine ⟨(AlgebraicGeometry.SmallAffineEtale.inclusion B S hS).obj
      (objOfOpenOver B S hS Z A hA),
    (AlgebraicGeometry.SmallAffineEtale.inclusion B S hS).map ι₀, ?_, ?_⟩
  · exact ⟨objOfOpenOver B S hS Z A hA, ι₀, 𝟙 _, ⟨k, ⟨ιk⟩⟩, (Category.id_comp _).symm⟩
  · refine ⟨⟨x, hxA⟩, ?_⟩
    change ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map ι₀).base ⟨x, hxA⟩ = x
    rw [hmap]
    rfl

/-- The morphism of the small affine etale site attached to an inclusion of affine opens
of `S`. -/
def objOfAffineOpenHomOfLE {U U' : S.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    (hU' : AlgebraicGeometry.IsAffineOpen U') (h : U ≤ U') :
    objOfAffineOpen B S hS U hU ⟶ objOfAffineOpen B S hS U' hU' :=
  homOfSchemeHom B S hS (S.homOfLE h) (by
    rw [structMap_objOfAffineOpen B S hS U hU, structMap_objOfAffineOpen B S hS U' hU']
    exact S.homOfLE_ι h)

section Model

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
  (E : C ⥤ AlgebraicGeometry.SmallAffineEtale B S hS) [E.IsEquivalence]
  [E.IsDenseSubsite J (AlgebraicGeometry.SmallAffineEtale.topology B S hS)]

/-- The object of a small model of the small affine etale site of `S` attached to an affine open
of `S`. -/
def modelObjOfAffineOpen (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) : C :=
  E.asEquivalence.inverse.obj (objOfAffineOpen B S hS U hU)

/-- Any two morphisms of a small model into the object attached to an affine open of `S`
agree. -/
lemma model_hom_ext {V : C} (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U)
    (t t' : V ⟶ modelObjOfAffineOpen B S hS E U hU) : t = t' := by
  apply E.map_injective
  have h : E.map t ≫ E.asEquivalence.counitIso.hom.app (objOfAffineOpen B S hS U hU) =
      E.map t' ≫ E.asEquivalence.counitIso.hom.app (objOfAffineOpen B S hS U hU) :=
    hom_ext_objOfAffineOpen B S hS U hU _ _
  exact (cancel_mono (E.asEquivalence.counitIso.hom.app _)).mp h

/-- The morphism of a small model attached to an inclusion of affine opens of `S`. -/
def modelHomOfLE {U U' : S.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    (hU' : AlgebraicGeometry.IsAffineOpen U') (h : U ≤ U') :
    modelObjOfAffineOpen B S hS E U hU ⟶ modelObjOfAffineOpen B S hS E U' hU' :=
  E.asEquivalence.inverse.map (objOfAffineOpenHomOfLE B S hS hU hU' h)

/-- **A family of objects of a small model which absorbs every object landing in a corresponding
open generates a covering sieve**, the model form of `ofObjects_mem_topology_of_mem`. -/
theorem model_ofObjects_mem
    {κ : Type*} (O : κ → S.Opens) (Wk : κ → C)
    (hlift : ∀ (k : κ) (V : AlgebraicGeometry.SmallAffineEtale B S hS),
      Set.range (structMap B S hS V) ⊆ (O k : Set S) → Nonempty (V ⟶ E.obj (Wk k)))
    (Z : C)
    (hZ : ∀ x : (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj (E.obj Z),
      ∃ k, (structMap B S hS (E.obj Z)).base x ∈ O k) :
    Sieve.ofObjects Wk Z ∈ J Z := by
  rw [← Functor.IsDenseSubsite.functorPushforward_mem_iff
    (J := J) (K := AlgebraicGeometry.SmallAffineEtale.topology B S hS) (G := E)]
  refine GrothendieckTopology.superset_covering _ ?_
    (ofObjects_mem_topology_of_mem B S hS O (fun k => E.obj (Wk k)) hlift (E.obj Z) hZ)
  rintro Y f ⟨k, ⟨h⟩⟩
  refine ⟨E.asEquivalence.inverse.obj Y,
    E.preimage ((E.asEquivalence.counitIso.app Y).hom ≫ f),
    (E.asEquivalence.counitIso.app Y).inv,
    ⟨k, ⟨E.asEquivalence.inverse.map h ≫ E.asEquivalence.unitIso.inv.app (Wk k)⟩⟩, ?_⟩
  rw [Functor.map_preimage]
  exact (Iso.inv_hom_id_assoc _ _).symm

/-- A morphism of a small model into the object attached to an affine open `U` of `S` forces the
structure morphism of its source to land in `U`. -/
lemma model_structMap_mem (Z : C) {U : S.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    (t : Z ⟶ modelObjOfAffineOpen B S hS E U hU)
    (x : (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj (E.obj Z)) :
    (structMap B S hS (E.obj Z)).base x ∈ U := by
  let tk : E.obj Z ⟶ objOfAffineOpen B S hS U hU :=
    E.map t ≫ (E.asEquivalence.counitIso.app (objOfAffineOpen B S hS U hU)).hom
  have h1 := toScheme_map_comp_structMap B S hS tk
  rw [structMap_objOfAffineOpen B S hS U hU] at h1
  have h2 : (structMap B S hS (E.obj Z)).base x ∈ Set.range U.ι := by
    refine ⟨((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map tk).base x, ?_⟩
    rw [← h1]
    rfl
  rwa [AlgebraicGeometry.Scheme.Opens.range_ι] at h2

/-- **The comparison isomorphism of a small model at the object attached to an affine open**,
read in schemes: an isomorphism from the scheme of `modelObjOfAffineOpen U` onto `U`.

Its codomain is ascribed as `U` rather than left as `toScheme.obj (objOfAffineOpen U)`. The two
are the same scheme by `toScheme_objOfAffineOpen`, but only definitionally, and instance search
does not see `AlgebraicGeometry.IsOpenImmersion U.ι` — hence not `Mono U.ι` either — at the
second spelling, which is what the factorisations below are cancelled against. -/
def modelObjOfAffineOpenIso (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj
        (E.obj (modelObjOfAffineOpen B S hS E U hU)) ⟶ (U : Scheme.{u}) :=
  (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map
    (E.asEquivalence.counitIso.hom.app (objOfAffineOpen B S hS U hU))

/-- The morphism `modelObjOfAffineOpenIso U hU` is an isomorphism. -/
lemma isIso_modelObjOfAffineOpenIso (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) :
    IsIso (modelObjOfAffineOpenIso B S hS E U hU) := by
  change IsIso ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map
    (E.asEquivalence.counitIso.hom.app (objOfAffineOpen B S hS U hU)))
  infer_instance

/-- The structure morphism of the object of a small model attached to an affine open `U` is the
open immersion of `U`, composed with the comparison isomorphism of the model. -/
lemma structMap_modelObjOfAffineOpen (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) :
    modelObjOfAffineOpenIso B S hS E U hU ≫ U.ι =
      structMap B S hS (E.obj (modelObjOfAffineOpen B S hS E U hU)) := by
  rw [← structMap_objOfAffineOpen B S hS U hU]
  exact toScheme_map_comp_structMap B S hS
    (E.asEquivalence.counitIso.hom.app (objOfAffineOpen B S hS U hU))

/-- The structure morphism of the object of a small model attached to an affine open `U` has
image inside `U`. -/
lemma range_structMap_modelObjOfAffineOpen (U : S.Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U) :
    Set.range (structMap B S hS (E.obj (modelObjOfAffineOpen B S hS E U hU))) ⊆ (U : Set S) := by
  rw [← structMap_modelObjOfAffineOpen B S hS E U hU,
    ← AlgebraicGeometry.Scheme.Opens.range_ι]
  rintro - ⟨a, rfl⟩
  exact ⟨_, rfl⟩

/-- **The structure morphism of the object of a small model attached to an affine open is a
monomorphism**: it is an open immersion composed with an isomorphism. This is what makes the base
change of such an object along any morphism of schemes absorb at most one morphism from each
object. -/
lemma mono_structMap_modelObjOfAffineOpen (U : S.Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U) :
    Mono (structMap B S hS (E.obj (modelObjOfAffineOpen B S hS E U hU))) := by
  have := isIso_modelObjOfAffineOpenIso B S hS E U hU
  rw [← structMap_modelObjOfAffineOpen B S hS E U hU]
  infer_instance

/-- **A finite system of opens of `S` together with objects of a small model absorbing exactly
the objects landing in them is a one-hypercover of the terminal sheaf.** The objects `Wk k`
stand in for the opens `O k`, which cover `S`, and the objects `Pk k l m` for the opens
`O' k l m`, which cover `O k ⊓ O l`; `hliftW`/`hliftP` say that an object landing in one of the
opens maps to the corresponding member of the family, `hmemW` is the converse for the `Wk`, and
`hextW` says an object maps to `Wk k` in at most one way.

The hypotheses are exactly what the two clauses of
`Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercover` need, and no relation between the
morphisms `p₁`, `p₂` and the opens is asked for: by `hextW` there is nothing to ask, the
morphisms into `Wk k` being unique. This is the statement both
`isTopOneHypercover_modelObjOfAffineOpen` — the family attached to the opens themselves — and
`isTopOneHypercover_baseChange` — the family of base changes of that family along a morphism of
schemes — are read off. -/
theorem isTopOneHypercover_of_lifts
    {κ ν : Type*} (O : κ → S.Opens) (O' : κ → κ → ν → S.Opens)
    (Wk : κ → C) (Pk : κ → κ → ν → C)
    (p₁ : ∀ k l m, Pk k l m ⟶ Wk k) (p₂ : ∀ k l m, Pk k l m ⟶ Wk l)
    (hliftW : ∀ (k : κ) (V : AlgebraicGeometry.SmallAffineEtale B S hS),
      Set.range (structMap B S hS V) ⊆ (O k : Set S) → Nonempty (V ⟶ E.obj (Wk k)))
    (hliftP : ∀ (k l : κ) (m : ν) (V : AlgebraicGeometry.SmallAffineEtale B S hS),
      Set.range (structMap B S hS V) ⊆ (O' k l m : Set S) → Nonempty (V ⟶ E.obj (Pk k l m)))
    (hmemW : ∀ (k : κ) (Z : C), (Z ⟶ Wk k) →
      ∀ x : (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj (E.obj Z),
        (structMap B S hS (E.obj Z)).base x ∈ O k)
    (hextW : ∀ (k : κ) (Z : C) (t t' : Z ⟶ Wk k), t = t')
    (hOtop : (⨆ k, O k) = ⊤) (hOsup : ∀ k l, (⨆ m, O' k l m) = O k ⊓ O l) :
    Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercover J Wk Pk p₁ p₂ where
  coversTop Z := by
    refine model_ofObjects_mem B S hS J E O Wk hliftW Z fun x => ?_
    have hx : (structMap B S hS (E.obj Z)).base x ∈ (⊤ : S.Opens) := trivial
    rw [← hOtop] at hx
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  locally_factors Z k l f g := by
    refine ⟨Sieve.ofObjects (Pk k l) Z, ?_, ?_⟩
    · refine model_ofObjects_mem B S hS J E (O' k l) (Pk k l) (hliftP k l) Z fun x => ?_
      have hx : (structMap B S hS (E.obj Z)).base x ∈ O k ⊓ O l :=
        ⟨hmemW k Z f x, hmemW l Z g x⟩
      rw [← hOsup k l] at hx
      exact TopologicalSpace.Opens.mem_iSup.1 hx
    · rintro V' q ⟨m, ⟨r⟩⟩
      exact ⟨m, r, hextW k V' _ _, hextW l V' _ _⟩

/-- **A finite affine one-hypercover of a scheme is a one-hypercover of the terminal sheaf of
every small model of its small affine etale site.** This is `isTopOneHypercover_of_lifts` at the
family of objects attached to the opens themselves, whose three hypotheses are
`objOfAffineOpenHomOfRange`, `model_structMap_mem` and `model_hom_ext`. -/
theorem isTopOneHypercover_modelObjOfAffineOpen
    {κ ν : Type*} (U : κ → S.Opens) (V : κ → κ → ν → S.Opens)
    (hUaff : ∀ k, AlgebraicGeometry.IsAffineOpen (U k))
    (hVaff : ∀ k l m, AlgebraicGeometry.IsAffineOpen (V k l m))
    (hUtop : (⨆ k, U k) = ⊤) (hVsup : ∀ k l, (⨆ m, V k l m) = U k ⊓ U l)
    (hVle : ∀ k l m, V k l m ≤ U k ⊓ U l) :
    Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercover J
      (fun k => modelObjOfAffineOpen B S hS E (U k) (hUaff k))
      (fun k l m => modelObjOfAffineOpen B S hS E (V k l m) (hVaff k l m))
      (fun k l m =>
        modelHomOfLE B S hS E (hVaff k l m) (hUaff k) ((hVle k l m).trans inf_le_left))
      (fun k l m =>
        modelHomOfLE B S hS E (hVaff k l m) (hUaff l) ((hVle k l m).trans inf_le_right)) :=
  isTopOneHypercover_of_lifts B S hS J E U V _ _ _ _
    (fun k W hr => ⟨objOfAffineOpenHomOfRange B S hS (U k) (hUaff k) W hr ≫
      (E.asEquivalence.counitIso.app (objOfAffineOpen B S hS (U k) (hUaff k))).inv⟩)
    (fun k l m W hr => ⟨objOfAffineOpenHomOfRange B S hS (V k l m) (hVaff k l m) W hr ≫
      (E.asEquivalence.counitIso.app (objOfAffineOpen B S hS (V k l m) (hVaff k l m))).inv⟩)
    (fun k Z t x => model_structMap_mem B S hS E Z (hUaff k) t x)
    (fun k Z => model_hom_ext (V := Z) B S hS E (U k) (hUaff k)) hUtop hVsup

include B hS E in
/-- **Every small model of the small affine etale site of a quasi-compact quasi-separated scheme
carries a finite one-hypercover of its terminal sheaf.** -/
theorem exists_finite_isTopOneHypercover [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (κ ν : Type) (_ : Finite κ) (_ : Finite ν) (W : κ → C) (P : κ → κ → ν → C)
      (p₁ : ∀ k l m, P k l m ⟶ W k) (p₂ : ∀ k l m, P k l m ⟶ W l),
      Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercover J W P p₁ p₂ := by
  obtain ⟨κ, ν, hκ, hν, U, V, hUaff, hVaff, hUtop, hVle, hVsup⟩ :=
    exists_finite_affine_oneHypercover_opens_fin S
  exact ⟨κ, ν, hκ, hν, _, _, _, _,
    isTopOneHypercover_modelObjOfAffineOpen B S hS J E U V hUaff hVaff hUtop hVsup hVle⟩

end Model

/-! ### Base changes of the objects attached to affine opens

The objects of a small model attached to the affine opens of `S` have base changes along any
morphism `g : S' ⟶ S`, in any small model of the small affine etale site of `S'`, and those base
changes are again a one-hypercover of the terminal sheaf — of the model of `S'`, over the
*preimage* opens `g ⁻¹ᵁ U k`.

Nothing here asks the preimage opens to be affine, and nothing asks `g` to be affine. A base
change is not the object attached to any particular open: it is pinned only by its fibre-product
square, and the scheme underlying it is affine for free, being the scheme of an object of an
*affine* etale site. That is exactly why `isTopOneHypercover_of_lifts` keeps the family of objects
and the family of opens apart.
-/

section BaseChange

variable (S' : Scheme.{u}) (hS' : B.Contains S') (g : S' ⟶ S)
  {C₀ : Type w} [SmallCategory C₀]
  (E₀ : C₀ ⥤ AlgebraicGeometry.SmallAffineEtale B S hS) [E₀.IsEquivalence]
  {C : Type w'} [SmallCategory C]
  (E : C ⥤ AlgebraicGeometry.SmallAffineEtale B S' hS') [E.IsEquivalence]
  (T : C₀ ⥤ C)
  (φ : ∀ Y : C₀, (AlgebraicGeometry.SmallAffineEtale.toScheme B S' hS').obj (E.obj (T.obj Y)) ⟶
    (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj (E₀.obj Y))
  (hT : ∀ Y : C₀, IsPullback (φ Y) (structMap B S' hS' (E.obj (T.obj Y)))
    (structMap B S hS (E₀.obj Y)) g)

omit [E₀.IsEquivalence] [E.IsEquivalence] in
include hT in
/-- **The structure morphism of a base change, followed by `g`, factors through the object it is
based from**, read along a morphism into the base change. -/
lemma toScheme_map_comp_fst (Y : C₀) (Z : C) (t : Z ⟶ T.obj Y) :
    ((AlgebraicGeometry.SmallAffineEtale.toScheme B S' hS').map (E.map t) ≫ φ Y) ≫
        structMap B S hS (E₀.obj Y) = structMap B S' hS' (E.obj Z) ≫ g := by
  rw [Category.assoc, (hT Y).w, ← Category.assoc,
    toScheme_map_comp_structMap B S' hS' (E.map t)]

include hT in
/-- **A base change absorbs an object together with a factorisation of its structure morphism.**
Given an object `V` of the small affine etale site of `S'` and a morphism `t` of schemes from `V`
to the object `Y` is based from which commutes with `g`, the lift of `(t, structMap V)` along the
fibre-product square is a morphism `V ⟶ E.obj (T.obj Y)`. -/
def baseChangeHom (Y : C₀) (V : AlgebraicGeometry.SmallAffineEtale B S' hS')
    (t : (AlgebraicGeometry.SmallAffineEtale.toScheme B S' hS').obj V ⟶
      (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj (E₀.obj Y))
    (ht : t ≫ structMap B S hS (E₀.obj Y) = structMap B S' hS' V ≫ g) :
    V ⟶ E.obj (T.obj Y) :=
  homOfSchemeHom B S' hS' ((hT Y).lift t (structMap B S' hS' V) ht)
    ((hT Y).lift_snd t (structMap B S' hS' V) ht)

include hT in
/-- **The base change of the object attached to an affine open `U` of `S` absorbs every object of
the small affine etale site of `S'` whose structure morphism lands in the preimage `g ⁻¹ᵁ U`.**
This is the hypothesis `hliftW` of `isTopOneHypercover_of_lifts` for the family of base
changes. -/
def baseChangeHomOfRange (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U)
    (V : AlgebraicGeometry.SmallAffineEtale B S' hS')
    (hr : Set.range (structMap B S' hS' V) ⊆ ((g ⁻¹ᵁ U : S'.Opens) : Set S')) :
    V ⟶ E.obj (T.obj (modelObjOfAffineOpen B S hS E₀ U hU)) := by
  haveI := isIso_modelObjOfAffineOpenIso B S hS E₀ U hU
  have hr' : Set.range (structMap B S' hS' V ≫ g) ⊆ Set.range U.ι := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    rintro - ⟨x, rfl⟩
    exact hr ⟨x, rfl⟩
  refine baseChangeHom B S hS S' hS' g E₀ E T φ hT (modelObjOfAffineOpen B S hS E₀ U hU) V
    (AlgebraicGeometry.IsOpenImmersion.lift U.ι (structMap B S' hS' V ≫ g) hr' ≫
      inv (modelObjOfAffineOpenIso B S hS E₀ U hU)) ?_
  rw [← structMap_modelObjOfAffineOpen B S hS E₀ U hU, Category.assoc, IsIso.inv_hom_id_assoc]
  exact AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hr'

omit [E.IsEquivalence] in
include hT in
/-- **The structure morphism of an object mapping to the base change of the object attached to an
affine open `U` lands in the preimage `g ⁻¹ᵁ U`**, the converse of `baseChangeHomOfRange`. This is
the hypothesis `hmemW` of `isTopOneHypercover_of_lifts`. -/
lemma baseChange_structMap_mem (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) (Z : C)
    (t : Z ⟶ T.obj (modelObjOfAffineOpen B S hS E₀ U hU))
    (x : (AlgebraicGeometry.SmallAffineEtale.toScheme B S' hS').obj (E.obj Z)) :
    (structMap B S' hS' (E.obj Z)).base x ∈ g ⁻¹ᵁ U := by
  have h := toScheme_map_comp_fst B S hS S' hS' g E₀ E T φ hT
    (modelObjOfAffineOpen B S hS E₀ U hU) Z t
  have hmem : (structMap B S' hS' (E.obj Z) ≫ g).base x ∈ (U : Set S) := by
    rw [← h]
    exact range_structMap_modelObjOfAffineOpen B S hS E₀ U hU ⟨_, rfl⟩
  simpa using hmem

include hT in
/-- **An object of a small model of the small affine etale site of `S'` maps in at most one way to
the base change of the object attached to an affine open of `S`.** The structure morphism of the
latter is a monomorphism (`mono_structMap_modelObjOfAffineOpen`), a monomorphism stays one under
base change, and a morphism of the site is a morphism over `S'`. This is the hypothesis `hextW` of
`isTopOneHypercover_of_lifts`. -/
lemma baseChange_hom_ext (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) (Z : C)
    (t t' : Z ⟶ T.obj (modelObjOfAffineOpen B S hS E₀ U hU)) : t = t' := by
  have := mono_structMap_modelObjOfAffineOpen B S hS E₀ U hU
  have := (hT (modelObjOfAffineOpen B S hS E₀ U hU)).mono_snd_of_mono
  exact E.map_injective (hom_ext_of_mono_structMap B S' hS' (E.map t) (E.map t'))

section Topology

variable (J : GrothendieckTopology C)
  [E.IsDenseSubsite J (AlgebraicGeometry.SmallAffineEtale.topology B S' hS')]

include hT in
/-- **The base changes of the objects attached to a finite affine one-hypercover of `S` are a
one-hypercover of the terminal sheaf of any small model of the small affine etale site of `S'`.**
The opens the family stands over are the preimages `g ⁻¹ᵁ U k` and `g ⁻¹ᵁ V k l m`, which cover
`S'` and the pairwise intersections because the `U k` and the `V k l m` cover `S` and the
intersections there.

No affineness of `g`, of `S` or of `S'` is used, and the preimage opens are not claimed to be
affine; see the section introduction. -/
theorem isTopOneHypercover_baseChange
    {κ ν : Type*} (U : κ → S.Opens) (V : κ → κ → ν → S.Opens)
    (hUaff : ∀ k, AlgebraicGeometry.IsAffineOpen (U k))
    (hVaff : ∀ k l m, AlgebraicGeometry.IsAffineOpen (V k l m))
    (hUtop : (⨆ k, U k) = ⊤) (hVsup : ∀ k l, (⨆ m, V k l m) = U k ⊓ U l)
    (hVle : ∀ k l m, V k l m ≤ U k ⊓ U l) :
    Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercover J
      (fun k => T.obj (modelObjOfAffineOpen B S hS E₀ (U k) (hUaff k)))
      (fun k l m => T.obj (modelObjOfAffineOpen B S hS E₀ (V k l m) (hVaff k l m)))
      (fun k l m => T.map
        (modelHomOfLE B S hS E₀ (hVaff k l m) (hUaff k) ((hVle k l m).trans inf_le_left)))
      (fun k l m => T.map
        (modelHomOfLE B S hS E₀ (hVaff k l m) (hUaff l) ((hVle k l m).trans inf_le_right))) :=
  isTopOneHypercover_of_lifts B S' hS' J E (fun k => g ⁻¹ᵁ U k) (fun k l m => g ⁻¹ᵁ V k l m)
    _ _ _ _
    (fun k W hr => ⟨baseChangeHomOfRange B S hS S' hS' g E₀ E T φ hT (U k) (hUaff k) W hr⟩)
    (fun k l m W hr =>
      ⟨baseChangeHomOfRange B S hS S' hS' g E₀ E T φ hT (V k l m) (hVaff k l m) W hr⟩)
    (fun k Z t x =>
      baseChange_structMap_mem B S hS S' hS' g E₀ E T φ hT (U k) (hUaff k) Z t x)
    (fun k Z t t' => baseChange_hom_ext B S hS S' hS' g E₀ E T φ hT (U k) (hUaff k) Z t t')
    (AlgebraicGeometry.Scheme.Hom.iSup_preimage_eq_top g hUtop)
    (fun k l => by
      rw [← AlgebraicGeometry.Scheme.Hom.preimage_iSup, hVsup k l,
        AlgebraicGeometry.Scheme.Hom.preimage_inf])

end Topology

end BaseChange

/-! ### The levels of the site system of Stacks 0EYL -/

section Level

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Limits.Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt) (hc : Limits.IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-- **A quasi-compact quasi-separated level of the site system of Stacks 0EYL carries a finite
one-hypercover of the terminal sheaf of its site.** The level `i` is a small model of the small
affine etale site of the scheme `X_j` it sits over
(`Stacks.EtaleCohomology.AffineLimitCohomology.isDenseSubsite_levelFunctor`), so
`exists_finite_isTopOneHypercover` applies to it; the hypercover is the affine one-hypercover of
opens of `X_j`.

This is the input the degree-zero Cech step of Stacks 09YQ asks for at a single level, and
nothing more: it does not say that the **transition images** of one chosen hypercover are again
hypercovers at the levels below, nor that its image in the site of the limit is one. Those two
statements — the hypotheses `hlev` and `hC` of that step — are
`exists_finite_isTopOneHypercover_level_transition`. -/
theorem exists_finite_isTopOneHypercover_level (i : (sys D c B hD hX hc).I)
    [CompactSpace (levelScheme D c B hD hX hc i)]
    [QuasiSeparatedSpace (levelScheme D c B hD hX hc i)] :
    ∃ (κ ν : Type) (_ : Finite κ) (_ : Finite ν)
      (W : κ → (sys D c B hD hX hc).C i) (P : κ → κ → ν → (sys D c B hD hX hc).C i)
      (p₁ : ∀ k l m, P k l m ⟶ W k) (p₂ : ∀ k l m, P k l m ⟶ W l),
      Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercover
        ((sys D c B hD hX hc).J i) W P p₁ p₂ :=
  have := isDenseSubsite_levelFunctor D c B hD hX hc i
  exists_finite_isTopOneHypercover B (levelScheme D c B hD hX hc i)
    (hD (levelIndex D c B hD hX hc i)) ((sys D c B hD hX hc).J i)
    (levelAffineEtaleFunctor D c B hD hX hc i)

/-- **A quasi-compact quasi-separated level of the site system of Stacks 0EYL carries a finite
one-hypercover of the terminal sheaf whose transition images at every level below, and whose
image in the site of the limit, are again finite one-hypercovers of the terminal sheaf.**

This is the complete covering input of the degree-zero Cech step of Stacks 09YQ,
`Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit`: the first
clause of the conclusion is that step's hypothesis `hlev`, the second is its hypothesis `hC`, and
the hypercover itself is its data `W₀`, `P₀`, `q₁`, `q₂`. Both clauses are
`isTopOneHypercover_baseChange`, the transition functors and the functors to the site of the
limit being geometric base change by `AffineEtaleSiteColimit.transition_isPullback` and
`AffineEtaleSiteColimit.toLimit_isPullback`.

Only the chosen level is asked to be quasi-compact and quasi-separated. In particular neither the
levels below nor the limit `X` is asked to be affine, quasi-compact, quasi-separated — or
anything else: the base changes of the objects attached to the affine opens of `X_{i₀}` are
objects of the small affine etale sites downstairs by construction, so their schemes are affine
for free and the preimage opens are never asked to be affine. The affineness of the transition
morphisms of `D` enters only through the existence of the site system itself. -/
theorem exists_finite_isTopOneHypercover_level_transition (i₀ : (sys D c B hD hX hc).I)
    [CompactSpace (levelScheme D c B hD hX hc i₀)]
    [QuasiSeparatedSpace (levelScheme D c B hD hX hc i₀)] :
    ∃ (κ ν : Type) (_ : Finite κ) (_ : Finite ν)
      (W : κ → (sys D c B hD hX hc).C i₀) (P : κ → κ → ν → (sys D c B hD hX hc).C i₀)
      (p₁ : ∀ k l m, P k l m ⟶ W k) (p₂ : ∀ k l m, P k l m ⟶ W l),
      (∀ {n : (sys D c B hD hX hc).I} (a : n ⟶ i₀),
          Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercover ((sys D c B hD hX hc).J n)
            (fun k => ((sys D c B hD hX hc).u a).obj (W k))
            (fun k l m => ((sys D c B hD hX hc).u a).obj (P k l m))
            (fun k l m => ((sys D c B hD hX hc).u a).map (p₁ k l m))
            (fun k l m => ((sys D c B hD hX hc).u a).map (p₂ k l m))) ∧
        Stacks.WeakSites.ColimitGlobalSections.IsTopOneHypercover
          (limitSitePrecoverage D c B hX).toGrothendieck
          (fun k => (toLimitSmall D c B hD hX hc i₀).obj (W k))
          (fun k l m => (toLimitSmall D c B hD hX hc i₀).obj (P k l m))
          (fun k l m => (toLimitSmall D c B hD hX hc i₀).map (p₁ k l m))
          (fun k l m => (toLimitSmall D c B hD hX hc i₀).map (p₂ k l m)) := by
  obtain ⟨κ, ν, hκ, hν, U, V, hUaff, hVaff, hUtop, hVle, hVsup⟩ :=
    exists_finite_affine_oneHypercover_opens_fin
      (levelScheme D c B hD hX hc i₀)
  refine ⟨κ, ν, hκ, hν,
    fun k => modelObjOfAffineOpen B (levelScheme D c B hD hX hc i₀)
      (hD (levelIndex D c B hD hX hc i₀)) (levelAffineEtaleFunctor D c B hD hX hc i₀)
      (U k) (hUaff k),
    fun k l m => modelObjOfAffineOpen B (levelScheme D c B hD hX hc i₀)
      (hD (levelIndex D c B hD hX hc i₀)) (levelAffineEtaleFunctor D c B hD hX hc i₀)
      (V k l m) (hVaff k l m),
    fun k l m => modelHomOfLE B (levelScheme D c B hD hX hc i₀)
      (hD (levelIndex D c B hD hX hc i₀)) (levelAffineEtaleFunctor D c B hD hX hc i₀)
      (hVaff k l m) (hUaff k) ((hVle k l m).trans inf_le_left),
    fun k l m => modelHomOfLE B (levelScheme D c B hD hX hc i₀)
      (hD (levelIndex D c B hD hX hc i₀)) (levelAffineEtaleFunctor D c B hD hX hc i₀)
      (hVaff k l m) (hUaff l) ((hVle k l m).trans inf_le_right),
    fun {n} a => ?_, ?_⟩
  · have := isDenseSubsite_levelFunctor D c B hD hX hc n
    exact isTopOneHypercover_baseChange B (levelScheme D c B hD hX hc i₀)
      (hD (levelIndex D c B hD hX hc i₀)) (levelScheme D c B hD hX hc n)
      (hD (levelIndex D c B hD hX hc n))
      (D.map ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map a))
      (levelAffineEtaleFunctor D c B hD hX hc i₀) (levelAffineEtaleFunctor D c B hD hX hc n)
      ((sys D c B hD hX hc).u a)
      (fun Y => ((affineEtaleSiteColimit D c B hD hX hc).transitionFst a).app Y)
      ((affineEtaleSiteColimit D c B hD hX hc).transition_isPullback a)
      ((sys D c B hD hX hc).J n) U V hUaff hVaff hUtop hVsup hVle
  · have := CategoryTheory.Precoverage.isEquivalence_of_surjective_obj
      (AsSmall.down : limitSite D c B hX ⥤ AlgebraicGeometry.SmallAffineEtale B c.pt hX)
      CategoryTheory.AsSmall.surjective_down_obj
    have : (AsSmall.down :
        limitSite D c B hX ⥤ AlgebraicGeometry.SmallAffineEtale B c.pt hX).IsDenseSubsite
        (limitSitePrecoverage D c B hX).toGrothendieck
        (AlgebraicGeometry.SmallAffineEtale.topology B c.pt hX) :=
      CategoryTheory.AsSmall.isDenseSubsite_down
        (AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX)
    exact isTopOneHypercover_baseChange B (levelScheme D c B hD hX hc i₀)
      (hD (levelIndex D c B hD hX hc i₀)) c.pt hX
      (c.π.app (levelIndex D c B hD hX hc i₀))
      (levelAffineEtaleFunctor D c B hD hX hc i₀) AsSmall.down (toLimitSmall D c B hD hX hc i₀)
      (fun Y => ((affineEtaleSiteColimit D c B hD hX hc).toLimitFst i₀).app Y)
      ((affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback i₀)
      (limitSitePrecoverage D c B hX).toGrothendieck U V hUaff hVaff hUtop hVsup hVle

/-! ### Stacks 09YP over the terminal sheaf, in degree zero

The data assembled above is the whole covering input of
`Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit`, and the
object-level colimit statement that step also consumes is a theorem of the library — Stacks 09YN,
in the form
`Stacks.WeakSites.ColimitGlobalSections.objectSections_jointlySurjective_and_separated`. What is
left to assume is the colimit presentation itself (`hψ`, `hι`, `hG`, `hρ`), so the statement below
carries no geometric hypothesis beyond the chosen level being quasi-compact and quasi-separated.

This is Stacks 09YP **over the terminal sheaf** rather than over an object of the colimit site, in
degree zero and for sheaves of sets: the small affine etale site of a non-affine `X` has no
terminal object, so its global sections are not the sections over any object of it, and the
object-level statement does not apply to them. The passage from sheaves of sets to abelian sheaves
and to the right derived functors of `CategoryTheory.Sheaf.Γ` is carried out in the section
*Stacks 09YP over the terminal sheaf, in degree zero, for abelian sheaves* below. The positive
degrees are not here.
-/

section DegreeZero

open Stacks.WeakSites.ColimitGlobalSections

/-- **The legs of a family of sheaves of sets on the levels are compatible with the transitions**,
read on the site of the limit. This is the first half of a presentation of `G` as the colimit
`colim_i f_i^{-1} F_i`. -/
def IsCompatibleLegsOfTypes
    (Fs : ∀ i, Sheaf ((sys D c B hD hX hc).J i) (Type (max u v + 1)))
    (ψ : ∀ {i j : (sys D c B hD hX hc).I} (a : j ⟶ i),
      (Fs i).obj ⟶ ((sys D c B hD hX hc).u a).op ⋙ (Fs j).obj)
    (G : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck (Type (max u v + 1)))
    (ι : ∀ i, (Fs i).obj ⟶ (toLimitSmall D c B hD hX hc i).op ⋙ G.obj) : Prop :=
  ∀ {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) (Y : (sys D c B hD hX hc).C i)
      (x : (Fs i).obj.obj (op Y)),
    (ι i).app (op Y) x =
      G.obj.map (eqToHom (congrArg op
          (Functor.congr_obj (toLimitSmall_transition D c B hD hX hc a) Y)))
        ((ι j).app (op (((sys D c B hD hX hc).u a).obj Y)) ((ψ a).app (op Y) x))

/-- **The universal property of the colimit `colim_i f_i^{-1} F_i` on the site of the limit**, for
a system of sheaves of sets: every family of legs compatible with the transitions factors uniquely
through `ι`. Together with `IsCompatibleLegsOfTypes` this is the set-valued analogue of
`InverseSystemOfFiniteSites.IsColimitPresentation`, which the library has only for systems of
abelian sheaves. -/
def IsUniversalLegsOfTypes
    (Fs : ∀ i, Sheaf ((sys D c B hD hX hc).J i) (Type (max u v + 1)))
    (ψ : ∀ {i j : (sys D c B hD hX hc).I} (a : j ⟶ i),
      (Fs i).obj ⟶ ((sys D c B hD hX hc).u a).op ⋙ (Fs j).obj)
    (G : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck (Type (max u v + 1)))
    (ι : ∀ i, (Fs i).obj ⟶ (toLimitSmall D c B hD hX hc i).op ⋙ G.obj) : Prop :=
  ∀ (H : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck (Type (max u v + 1)))
      (g : ∀ i, (Fs i).obj ⟶ (toLimitSmall D c B hD hX hc i).op ⋙ H.obj),
    (∀ {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) (Y : (sys D c B hD hX hc).C i)
        (x : (Fs i).obj.obj (op Y)),
        (g i).app (op Y) x =
          H.obj.map (eqToHom (congrArg op
              (Functor.congr_obj (toLimitSmall_transition D c B hD hX hc a) Y)))
            ((g j).app (op (((sys D c B hD hX hc).u a).obj Y)) ((ψ a).app (op Y) x))) →
      ∃! h : G ⟶ H, ∀ (i : (sys D c B hD hX hc).I) (Y : (sys D c B hD hX hc).C i)
          (x : (Fs i).obj.obj (op Y)),
        (g i).app (op Y) x =
          h.hom.app (op ((toLimitSmall D c B hD hX hc i).obj Y)) ((ι i).app (op Y) x)

/-- **Stacks 09YP over the terminal sheaf of the site of the limit, in degree zero.** Let `I` be a
directed set, let `(X_i)` be an inverse system of schemes over `Iᵒᵖ` with affine transition
morphisms, let `X = lim_i X_i`, let `F_i` be a system of sheaves of sets on the levels of the site
system of Stacks 0EYL with transition maps `ψ`, and let `G` with legs `ι` present the colimit
`colim_i f_i^{-1} F_i` on the site of the limit. Fix a level `i₀` whose scheme is quasi-compact
and quasi-separated. Then the **global sections** of `G` — the sections over the terminal sheaf of
the site of the limit, which is not the site's terminal object unless `X` is affine — are the
filtered colimit of the global sections of the `F_n` over the arrows `n ⟶ i₀`: the canonical maps
`ρ` are jointly surjective, and two global sections of a level with the same image agree on a
finite one-hypercover of the terminal sheaf after passing to a further level, hence have the same
image there by
`Stacks.WeakSites.ColimitGlobalSections.existsUnique_sections_of_matching`.

No hypothesis of this statement is about covers: the one-hypercover, its transition images and its
image in the site of the limit are supplied by
`exists_finite_isTopOneHypercover_level_transition`, and the object-level colimit statement by
Stacks 09YN. Nothing is assumed of `X` or of the levels other than `i₀` — in particular not that
`X` is affine, which is exactly the case the object-level statement already covers. -/
theorem globalSections_colimit_of_level (i₀ : (sys D c B hD hX hc).I)
    [CompactSpace (levelScheme D c B hD hX hc i₀)]
    [QuasiSeparatedSpace (levelScheme D c B hD hX hc i₀)]
    (Fs : ∀ i, Sheaf ((sys D c B hD hX hc).J i) (Type (max u v + 1)))
    (ψ : ∀ {i j : (sys D c B hD hX hc).I} (a : j ⟶ i),
      (Fs i).obj ⟶ ((sys D c B hD hX hc).u a).op ⋙ (Fs j).obj)
    (G : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck (Type (max u v + 1)))
    (ι : ∀ i, (Fs i).obj ⟶ (toLimitSmall D c B hD hX hc i).op ⋙ G.obj)
    (ρ : ∀ {n : (sys D c B hD hX hc).I} (_ : n ⟶ i₀),
      (Fs n).obj.sections → G.obj.sections)
    (hψ : ∀ {i j k : (sys D c B hD hX hc).I} (a : j ⟶ i) (b : k ⟶ j)
        (Y : (sys D c B hD hX hc).C i) (x : (Fs i).obj.obj (op Y)),
      (ψ (b ≫ a)).app (op Y) x =
        (Fs k).obj.map (eqToHom (congrArg op
            (Functor.congr_obj ((sys D c B hD hX hc).comp b a) Y).symm))
          ((ψ b).app (op (((sys D c B hD hX hc).u a).obj Y)) ((ψ a).app (op Y) x)))
    (hι : IsCompatibleLegsOfTypes D c B hD hX hc Fs ψ G ι)
    (hG : IsUniversalLegsOfTypes D c B hD hX hc Fs ψ G ι)
    (hρ : ∀ {n : (sys D c B hD hX hc).I} (a : n ⟶ i₀) (t : (Fs n).obj.sections)
        (Y : (sys D c B hD hX hc).C n),
      (ρ a t).val (op ((toLimitSmall D c B hD hX hc n).obj Y)) =
        (ι n).app (op Y) (t.val (op Y))) :
    ∃ (κ : Type) (_ : Finite κ) (W₀ : κ → (sys D c B hD hX hc).C i₀),
      (∀ s : G.obj.sections, ∃ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀)
          (t : (Fs n).obj.sections), ρ a t = s) ∧
        ∀ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀) (t t' : (Fs n).obj.sections),
          ρ a t = ρ a t' →
            ∃ (m : (sys D c B hD hX hc).I) (b : m ⟶ n), ∀ k : κ,
              (ψ b).app (op (((sys D c B hD hX hc).u a).obj (W₀ k)))
                  (t.val (op (((sys D c B hD hX hc).u a).obj (W₀ k)))) =
                (ψ b).app (op (((sys D c B hD hX hc).u a).obj (W₀ k)))
                  (t'.val (op (((sys D c B hD hX hc).u a).obj (W₀ k)))) := by
  obtain ⟨κ, ν, hκ, hν, W₀, P₀, q₁, q₂, hlev, hC⟩ :=
    exists_finite_isTopOneHypercover_level_transition D c B hD hX hc i₀
  have := hκ
  have := hν
  obtain ⟨hsurj, hsep⟩ :=
    objectSections_jointlySurjective_and_separated (sys D c B hD hX hc)
      (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
      (toLimitSmall_obj_descends D c B hD hX hc) (toLimitSmall_hom_descends D c B hD hX hc)
      (toLimitSmall_hom_eventually_eq D c B hD hX hc) (limitSitePrecoverage D c B hX)
      (mem_limitSitePrecoverage_iff D c B hD hX hc) Fs ψ hψ G ι hι hG
  exact ⟨κ, hκ, W₀,
    globalSections_colimit_pullback_of_colimit (sys D c B hD hX hc)
      (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc) Fs ψ G ι
      hψ hι hsurj hsep i₀ W₀ P₀ q₁ q₂ hlev hC ρ hρ⟩

end DegreeZero

/-! ### Stacks 09YP over the terminal sheaf, in degree zero, for abelian sheaves

The statement above is about sheaves of **sets**, because the degree-zero Cech step of Stacks 09YQ
is. Stacks 09YP is about abelian sheaves, and the passage to them is
`Stacks.WeakSites.ColimitGlobalSections.abelianGlobalSections_colimit_pullback_of_colimit`: the
colimit presentation it consumes is the library's
`InverseSystemOfFiniteSites.IsColimitPresentation` for a system of abelian sheaves, and the global
sections are Mathlib's `CategoryTheory.Sheaf.Γ`.

That passage is **not** the forgetful image of an abelian colimit presentation, and it does not
need one: the forgetful functor `Sheaf K Ab ⥤ Sheaf K (Type _)` is a right adjoint, so there is no
reason for it to carry `colim f_i^{-1}F_i` to a colimit, and the universal property of
`IsColimitPresentation` is quantified only over abelian sheaves. What the Cech step actually
consumes of the presentation is its *object-level* conclusion, Stacks 09YN — joint surjectivity
and separatedness of the legs over an object of the colimit site — and that is a statement about
elements of the very same sets, available for an abelian system as
`Stacks.WeakSites.ColimitSiteCohomology.abelianSections_jointlySurjective_and_separated`.
Sheafification therefore plays no part.
-/

section DegreeZeroAbelian

open Stacks.WeakSites.ColimitGlobalSections Stacks.WeakSites.ColimitSiteCohomology

/- Sheafification of abelian sheaves on the site of the limit and on the levels: the two
`HasSheafify` facts `Sheaf.Γ` needs, at the spelling these sites have. Both are theorems of
`Stacks.EtaleCohomology.AffineLimitCohomology` rather than instances, and without them instance
search for `HasWeakSheafify` runs past its heartbeat budget on `sheafToPresheaf.IsRightAdjoint`. -/
attribute [local instance] hasSheafify_limitSite hasSheafify_level

variable (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, v, max u v + 1, max u v + 1}
    (sys D c B hD hX hc))

/-- The global sections of the abelian sheaf of the level `n` of the site system of Stacks 0EYL. -/
abbrev levelGlobalSections (n : (sys D c B hD hX hc).I) : Type (max u v + 1) :=
  (Sheaf.Γ ((sys D c B hD hX hc).J n) Ab.{max u v + 1}).obj (F.obj n)

/-- The global sections of an abelian sheaf on the site of the limit. -/
abbrev limitGlobalSections
    (𝒢 : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1}) :
    Type (max u v + 1) :=
  (Sheaf.Γ (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1}).obj 𝒢

/-- **A global section of the level `n`, restricted to an object `Y` of that level and carried
down to the level `m` by the transition of `b : m ⟶ n`.** This is named rather than written
inline: spelled out four times, it puts the statement of `globalSections_colimit_of_level_ab`
over the elaborator's default heartbeat budget. -/
def transitionOfGlobalSection {n m : (sys D c B hD hX hc).I} (b : m ⟶ n)
    (Y : (sys D c B hD hX hc).C n) (t : levelGlobalSections D c B hD hX hc F n) :
    ((F.obj m).obj.obj (op (((sys D c B hD hX hc).u b).obj Y)) : Type (max u v + 1)) :=
  (transition (sys D c B hD hX hc) F b).app (op Y) (Sheaf.ΓRes (F.obj n) (op Y) t)

/-- **`ρ` is the map on global sections induced by the legs `ι`**: the restriction of `ρ a t` to
the image of an object `Y` of the level `n` is the leg at `Y` applied to the restriction of `t`.
This pins `ρ` uniquely, a global section being determined by its restrictions, and is named rather
than written inline for the heartbeat reason recorded in the implementation notes. -/
def IsGlobalSectionsMapAb (i₀ : (sys D c B hD hX hc).I)
    (𝒢 : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1})
    (ι : ∀ j, (F.obj j).obj ⟶ (toLimitSmall D c B hD hX hc j).op ⋙ 𝒢.obj)
    (ρ : ∀ {n : (sys D c B hD hX hc).I} (_ : n ⟶ i₀),
      levelGlobalSections D c B hD hX hc F n → limitGlobalSections D c B hX 𝒢) : Prop :=
  ∀ {n : (sys D c B hD hX hc).I} (a : n ⟶ i₀)
      (t : levelGlobalSections D c B hD hX hc F n) (Y : (sys D c B hD hX hc).C n),
    Sheaf.ΓRes 𝒢 (op ((toLimitSmall D c B hD hX hc n).obj Y)) (ρ a t) =
      (ι n).app (op Y) (Sheaf.ΓRes (F.obj n) (op Y) t)

/-- **The global sections of `𝒢` are the filtered colimit of the global sections of the `F_n` over
the arrows into `i₀`, read off the family `W₀`**: the maps `ρ` are jointly surjective, and two
global sections of a level with the same image under `ρ` have the same image at some further level
on each `W₀ k`. Named rather than written inline for the heartbeat reason recorded in the
implementation notes. -/
def IsColimitGlobalSectionsAb (i₀ : (sys D c B hD hX hc).I)
    (𝒢 : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1})
    {κ : Type} (W₀ : κ → (sys D c B hD hX hc).C i₀)
    (ρ : ∀ {n : (sys D c B hD hX hc).I} (_ : n ⟶ i₀),
      levelGlobalSections D c B hD hX hc F n → limitGlobalSections D c B hX 𝒢) : Prop :=
  (∀ s : limitGlobalSections D c B hX 𝒢,
      ∃ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀)
        (t : levelGlobalSections D c B hD hX hc F n), ρ a t = s) ∧
    ∀ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀)
        (t t' : levelGlobalSections D c B hD hX hc F n),
      ρ a t = ρ a t' →
        ∃ (m : (sys D c B hD hX hc).I) (b : m ⟶ n), ∀ k : κ,
          transitionOfGlobalSection D c B hD hX hc F b
              (((sys D c B hD hX hc).u a).obj (W₀ k)) t =
            transitionOfGlobalSection D c B hD hX hc F b
              (((sys D c B hD hX hc).u a).obj (W₀ k)) t'

/-- **Stacks 09YP over the terminal sheaf of the site of the limit, in degree zero, for ABELIAN
sheaves.** Let `I` be a directed set, let `(X_i)` be an inverse system of schemes over `Iᵒᵖ` with
affine transition morphisms, let `X = lim_i X_i`, let `F` be a system of **abelian** sheaves on the
levels of the site system of Stacks 0EYL, and let `𝒢` with legs `ι` present the colimit
`colim_i f_i^{-1}F_i` on the site of the limit (`IsColimitPresentation`). Fix a level `i₀` whose
scheme is quasi-compact and quasi-separated. Then the **global sections** `Γ(𝒢)` — Mathlib's
`CategoryTheory.Sheaf.Γ`, the sections over the terminal sheaf of the site of the limit, which is
not the site's terminal object unless `X` is affine — are the filtered colimit of the global
sections `Γ(F_n)` over the arrows `n ⟶ i₀`, in the sense of `IsColimitGlobalSectionsAb`: the
canonical maps `ρ` are jointly surjective, and two global sections of a level with the same image
agree on a finite one-hypercover of the terminal sheaf after passing to a further level.

No hypothesis of this statement is about covers: the one-hypercover, its transition images and its
image in the site of the limit are supplied by
`exists_finite_isTopOneHypercover_level_transition`, and the object-level colimit statement by
Stacks 09YN for abelian systems
(`Stacks.WeakSites.ColimitSiteCohomology.abelianSections_jointlySurjective_and_separated`).
Nothing is assumed of `X` or of the levels other than `i₀` — in particular not that `X` is affine,
which is the case the object-level statement
`Stacks.EtaleCohomology.QcqsLimitCohomology.etaleCohomologyColimit_isColimit` already covers. -/
theorem globalSections_colimit_of_level_ab (i₀ : (sys D c B hD hX hc).I)
    [CompactSpace (levelScheme D c B hD hX hc i₀)]
    [QuasiSeparatedSpace (levelScheme D c B hD hX hc i₀)]
    (𝒢 : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1})
    (ι : ∀ j, (F.obj j).obj ⟶ (toLimitSmall D c B hD hX hc j).op ⋙ 𝒢.obj)
    (hcolim : IsColimitPresentation.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) F 𝒢 ι)
    (ρ : ∀ {n : (sys D c B hD hX hc).I} (_ : n ⟶ i₀),
      levelGlobalSections D c B hD hX hc F n → limitGlobalSections D c B hX 𝒢)
    (hρ : IsGlobalSectionsMapAb D c B hD hX hc F i₀ 𝒢 ι ρ) :
    ∃ (κ : Type) (_ : Finite κ) (W₀ : κ → (sys D c B hD hX hc).C i₀),
      IsColimitGlobalSectionsAb D c B hD hX hc F i₀ 𝒢 W₀ ρ := by
  obtain ⟨κ, ν, hκ, hν, W₀, P₀, q₁, q₂, hlev, hC⟩ :=
    exists_finite_isTopOneHypercover_level_transition D c B hD hX hc i₀
  have := hκ
  have := hν
  have h := abelianGlobalSections_colimit_pullback_of_colimit.{v, v, max u v + 1}
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc)
      (toLimitSmall_obj_descends D c B hD hX hc)
      (toLimitSmall_hom_descends D c B hD hX hc)
      (toLimitSmall_hom_eventually_eq D c B hD hX hc)
      (limitSitePrecoverage D c B hX)
      (mem_limitSitePrecoverage_iff D c B hD hX hc) F 𝒢 ι hcolim i₀ W₀ P₀ q₁ q₂ hlev hC ρ hρ
  refine ⟨κ, hκ, W₀, h.1, fun n a t t' htt => ?_⟩
  obtain ⟨m, b, hb⟩ := h.2 n a t t' htt
  exact ⟨m, b, fun k => hb k⟩

/-! ### The vertex in degree zero: the right derived functors of global sections

`CategoryTheory.Sheaf.Γ` is a right adjoint, hence preserves finite limits, so its zeroth right
derived functor is itself (`CategoryTheory.Functor.rightDerivedZeroIsoSelf`). That is what makes
the statement above a statement about the degree-zero vertex
`(CategoryTheory.Sheaf.Γ _ Ab).rightDerived 0` of Stacks 09YP, which is the shape in which the
bridges `Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH` and
`Stacks.Cohomology.GlobalSections.rightDerivedSectionsIsoFunctorH` compare it with the cohomology
of the site.
-/

attribute [local instance] locallySmall_limitSite enoughInjectives_limitSite
  locallySmall_level enoughInjectives_level

/-- Global sections of abelian sheaves on the site of the limit, with coefficients in
`Ab.{max u v + 1}`, are additive. This is `Stacks.Cohomology.GlobalSections.additive_Γ` with its
coefficient universe pinned; it is needed already in the *statement* of
`rightDerivedZeroIsoGammaLimit`, `CategoryTheory.Functor.rightDerived` asking for it. -/
local instance additive_Γ_limitSite_pinned :
    (Sheaf.Γ (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1}).Additive :=
  Stacks.Cohomology.GlobalSections.additive_Γ.{max u v + 1, max u v + 1, max u v + 1} _

/-- Global sections of abelian sheaves on the level `n`, with coefficients in `Ab.{max u v + 1}`,
are additive; the level form of `additive_Γ_limitSite_pinned`. -/
local instance additive_Γ_level_pinned (n : (sys D c B hD hX hc).I) :
    (Sheaf.Γ ((sys D c B hD hX hc).J n) Ab.{max u v + 1}).Additive :=
  Stacks.Cohomology.GlobalSections.additive_Γ.{max u v + 1, max u v + 1, max u v + 1} _

/-- **The zeroth right derived functor of global sections on the site of the limit is global
sections itself.** `CategoryTheory.Sheaf.Γ` is a right adjoint, so it preserves finite limits, and
`CategoryTheory.Functor.rightDerivedZeroIsoSelf` applies; additivity is
`Stacks.Cohomology.GlobalSections.additive_Γ`. -/
def rightDerivedZeroIsoGammaLimit :
    (Sheaf.Γ (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1}).rightDerived 0 ≅
      Sheaf.Γ (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1} :=
  Functor.rightDerivedZeroIsoSelf
    (Sheaf.Γ (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1})

/-- **The zeroth right derived functor of global sections on the level `n` is global sections
itself**, the level form of `rightDerivedZeroIsoGammaLimit`. -/
def rightDerivedZeroIsoGammaLevel (n : (sys D c B hD hX hc).I) :
    (Sheaf.Γ ((sys D c B hD hX hc).J n) Ab.{max u v + 1}).rightDerived 0 ≅
      Sheaf.Γ ((sys D c B hD hX hc).J n) Ab.{max u v + 1} :=
  Functor.rightDerivedZeroIsoSelf
    (Sheaf.Γ ((sys D c B hD hX hc).J n) Ab.{max u v + 1})

/-- The degree-zero right derived global sections of the abelian sheaf of the level `n`. -/
abbrev rightDerivedZeroLevel (n : (sys D c B hD hX hc).I) : Type (max u v + 1) :=
  ((Sheaf.Γ ((sys D c B hD hX hc).J n) Ab.{max u v + 1}).rightDerived 0).obj (F.obj n)

/-- The degree-zero right derived global sections of an abelian sheaf on the site of the limit. -/
abbrev rightDerivedZeroLimit
    (𝒢 : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1}) :
    Type (max u v + 1) :=
  ((Sheaf.Γ (limitSitePrecoverage D c B hX).toGrothendieck
    Ab.{max u v + 1}).rightDerived 0).obj 𝒢

/-- **The degree-zero derived global sections on the site of the limit are the global sections**,
on elements: `rightDerivedZeroIsoGammaLimit` is an isomorphism of abelian groups, hence a
bijection. -/
def rightDerivedZeroEquivGammaLimit
    (𝒢 : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1}) :
    rightDerivedZeroLimit D c B hX 𝒢 ≃ limitGlobalSections D c B hX 𝒢 :=
  Equiv.ofBijective _
    (ConcreteCategory.bijective_of_isIso ((rightDerivedZeroIsoGammaLimit D c B hX).hom.app 𝒢))

/-- **The degree-zero derived global sections on the level `n` are the global sections**, on
elements; the level form of `rightDerivedZeroEquivGammaLimit`. -/
def rightDerivedZeroEquivGammaLevel (n : (sys D c B hD hX hc).I) :
    rightDerivedZeroLevel D c B hD hX hc F n ≃ levelGlobalSections D c B hD hX hc F n :=
  Equiv.ofBijective _
    (ConcreteCategory.bijective_of_isIso
      ((rightDerivedZeroIsoGammaLevel D c B hD hX hc n).hom.app (F.obj n)))

/-- **The degree-zero derived global sections of `𝒢` are the filtered colimit of those of the
`F_n`**: the conclusion of `IsColimitGlobalSectionsAb` read at the vertex
`(CategoryTheory.Sheaf.Γ _ Ab).rightDerived 0`, which is the vertex Stacks 09YP is stated at. The
separatedness clause is still read on sections over the objects `W₀ k` of the one-hypercover,
through `rightDerivedZeroEquivGammaLevel`. -/
def IsColimitRightDerivedZeroGlobalSectionsAb (i₀ : (sys D c B hD hX hc).I)
    (𝒢 : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1})
    {κ : Type} (W₀ : κ → (sys D c B hD hX hc).C i₀)
    (ρ : ∀ {n : (sys D c B hD hX hc).I} (_ : n ⟶ i₀),
      rightDerivedZeroLevel D c B hD hX hc F n → rightDerivedZeroLimit D c B hX 𝒢) : Prop :=
  (∀ s : rightDerivedZeroLimit D c B hX 𝒢,
      ∃ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀)
        (t : rightDerivedZeroLevel D c B hD hX hc F n), ρ a t = s) ∧
    ∀ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀)
        (t t' : rightDerivedZeroLevel D c B hD hX hc F n),
      ρ a t = ρ a t' →
        ∃ (m : (sys D c B hD hX hc).I) (b : m ⟶ n), ∀ k : κ,
          transitionOfGlobalSection D c B hD hX hc F b
              (((sys D c B hD hX hc).u a).obj (W₀ k))
              (rightDerivedZeroEquivGammaLevel D c B hD hX hc F n t) =
            transitionOfGlobalSection D c B hD hX hc F b
              (((sys D c B hD hX hc).u a).obj (W₀ k))
              (rightDerivedZeroEquivGammaLevel D c B hD hX hc F n t')

/-- **Stacks 09YP over the terminal sheaf, in degree zero and at its own vertex, for ABELIAN
sheaves.** `globalSections_colimit_of_level_ab` with the groups read as the degree-zero right
derived functors of global sections: `CategoryTheory.Sheaf.Γ` is left exact, so
`rightDerivedZeroIsoGammaLimit` and `rightDerivedZeroIsoGammaLevel` identify
`(Sheaf.Γ _ Ab).rightDerived 0` with `Sheaf.Γ _ Ab`, and `ρ` is pinned by `hρ` through those
identifications. -/
theorem rightDerivedZero_globalSections_colimit_of_level_ab (i₀ : (sys D c B hD hX hc).I)
    [CompactSpace (levelScheme D c B hD hX hc i₀)]
    [QuasiSeparatedSpace (levelScheme D c B hD hX hc i₀)]
    (𝒢 : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1})
    (ι : ∀ j, (F.obj j).obj ⟶ (toLimitSmall D c B hD hX hc j).op ⋙ 𝒢.obj)
    (hcolim : IsColimitPresentation.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) F 𝒢 ι)
    (ρ : ∀ {n : (sys D c B hD hX hc).I} (_ : n ⟶ i₀),
      rightDerivedZeroLevel D c B hD hX hc F n → rightDerivedZeroLimit D c B hX 𝒢)
    (hρ : ∀ {n : (sys D c B hD hX hc).I} (a : n ⟶ i₀)
        (t : rightDerivedZeroLevel D c B hD hX hc F n) (Y : (sys D c B hD hX hc).C n),
      Sheaf.ΓRes 𝒢 (op ((toLimitSmall D c B hD hX hc n).obj Y))
          (rightDerivedZeroEquivGammaLimit D c B hX 𝒢 (ρ a t)) =
        (ι n).app (op Y) (Sheaf.ΓRes (F.obj n) (op Y)
          (rightDerivedZeroEquivGammaLevel D c B hD hX hc F n t))) :
    ∃ (κ : Type) (_ : Finite κ) (W₀ : κ → (sys D c B hD hX hc).C i₀),
      IsColimitRightDerivedZeroGlobalSectionsAb D c B hD hX hc F i₀ 𝒢 W₀ ρ := by
  obtain ⟨κ, hκ, W₀, h1, h2⟩ :=
    globalSections_colimit_of_level_ab D c B hD hX hc F i₀ 𝒢 ι hcolim
      (fun {n} a t => rightDerivedZeroEquivGammaLimit D c B hX 𝒢
        (ρ a ((rightDerivedZeroEquivGammaLevel D c B hD hX hc F n).symm t)))
      (fun {n} a t Y => by
        have h := hρ a ((rightDerivedZeroEquivGammaLevel D c B hD hX hc F n).symm t) Y
        rwa [Equiv.apply_symm_apply] at h)
  refine ⟨κ, hκ, W₀, fun s => ?_, fun n a t t' htt => ?_⟩
  · obtain ⟨n, a, t, ht⟩ := h1 (rightDerivedZeroEquivGammaLimit D c B hX 𝒢 s)
    exact ⟨n, a, (rightDerivedZeroEquivGammaLevel D c B hD hX hc F n).symm t,
      (rightDerivedZeroEquivGammaLimit D c B hX 𝒢).injective ht⟩
  · refine h2 n a (rightDerivedZeroEquivGammaLevel D c B hD hX hc F n t)
      (rightDerivedZeroEquivGammaLevel D c B hD hX hc F n t') ?_
    simp only [Equiv.symm_apply_apply]
    exact congrArg (rightDerivedZeroEquivGammaLimit D c B hX 𝒢) htt

end DegreeZeroAbelian

end Level

end Stacks.EtaleCohomology.AffineEtaleTopOneHypercover

end
