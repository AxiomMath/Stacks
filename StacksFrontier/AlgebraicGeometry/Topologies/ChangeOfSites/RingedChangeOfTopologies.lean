module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.RingedBigSiteHom
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenCoarserSites
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.FinerTopologies
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoverings
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.CompositionGeneral
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.SmallModel
public import StacksCore.Tactic.StacksAttribute

/-!
# The five big topologies on one category, and `id_{τ, τ'}` as a morphism of ringed sites

The change-of-topologies list of Topologies, Section 03FE is stated "with suitable choices of
sites as in Remark 03FF", and Stacks 03FF is the statement that a chosen big fppf site `B`
carries big Zariski, étale, smooth and syntomic sites on the *same* size-bounded category of
schemes, their covering families being those chosen by `B` which are coverings for the coarser
topology.  That is what makes the identity functor `(\Sch/X)_{τ'} ⟶ (\Sch/X)_τ` available, and
hence `id_{τ, τ'} : (\Sch/X)_τ ⟶ (\Sch/X)_{τ'}` a morphism of sites, which 03FE composes with
`f_{big}`, `f_{small}` and `π_Y` to generate its twenty-seven entries.

This file supplies that generator, and with it Stacks 070R for every big-site entry of the list.
`AlgebraicGeometry.BigFppfSite.toBigZariskiSite` and its three companions already give the four
coarser sites with cutoff and covering bound *syntactically* `B`'s own, so the five localized
sites over a scheme `S` are literally one category `Over (B.obj hS)` with five topologies on it,
and the comparison is an inequality of topologies rather than a transport.

## Main definitions

* `AlgebraicGeometry.CoveringTopology.rank` and
  `AlgebraicGeometry.CoveringTopology.IsFiner`: the chain
  `Zariski ≺ étale ≺ smooth ≺ syntomic ≺ fppf`.
* `AlgebraicGeometry.BigFppfSite.carriedIsCovering`, `.carriedPrecoverage` and
  `.carriedTopology`: the covering families, precoverage and topology of the big `τ`-site
  carried by `B`, all on `B`'s own category.
* `AlgebraicGeometry.BigFppfSite.carriedOverTopology` and `.carriedOverRingedSite`: the five
  topologies on the one localized category `Over (B.obj hS)`, and the resulting ringed sites.
* `AlgebraicGeometry.BigFppfSite.idRingedSiteHom`: **`id_{τ, τ'}` as a morphism of ringed
  sites.**
* `AlgebraicGeometry.BigFppfSite.bigRingedSiteHom`: **entries (1)–(15) of the 03FE list**, the
  morphism of ringed sites `(\Sch/T)_τ ⟶ (\Sch/S)_{τ'}` for `τ` finer than `τ'`.

## Main results

* `AlgebraicGeometry.coveringPrecoverage_le_of_isFiner`: the precoverages of schemes are nested
  along the chain.
* `AlgebraicGeometry.BigFppfSite.carriedTopology_le` and `.carriedOverTopology_le`: so are
  the topologies, before and after localization.
* `AlgebraicGeometry.BigFppfSite.isMorphismOfSites_id`: the identity functor is a morphism of
  sites from the coarser to the finer localized topology, at the universe of the structure
  rings.
* `AlgebraicGeometry.BigFppfSite.idRingedSiteHom_fsharp`: `id_{τ, τ'}^♯` is the identity.

## Implementation notes

`AlgebraicGeometry.cutoff` and `AlgebraicGeometry.overTopology` dispatch on `τ`, so for a
*variable* `τ` the category `siteCategory (B.toBigSite τ)` is not syntactically `B.Schemes` and
anything stated through them would need transporting along a propositional equality of
cardinals.  The dispatch is therefore done here at the point of *definition* instead:
`carriedPrecoverage` and `carriedOverTopology` are five-case matches each of whose branches is
already a precoverage, resp. a topology, on the one category, so no transport occurs anywhere in
the file.
The bridge to the `τ`-uniform statements of
`StacksFrontier/AlgebraicGeometry/Topologies/BigSites/RingedBigSiteHom.lean` is then by `cases τ`
and `rfl`.

The nesting of the five classes of covering families is the nesting of the five morphism
properties, `AlgebraicGeometry.coveringMorphismProperty`, pushed through
`AlgebraicGeometry.Scheme.precoverage_mono`; the chosen families of the four coarser sites are
`CovBounded` of those properties against `B`'s own covering bound, so only the property changes
along the chain.  The fppf end of the chain is the one asymmetric case:
`AlgebraicGeometry.IsFppfCovering` is membership in the *comap* of the fppf precoverage rather
than in its image, and the passage is
`AlgebraicGeometry.isFppfCovering_of_mem_precoverage`.

`id_{τ, τ'}^♯` is the identity because the two sites carry the same structure sheaf: both are
presented by the one functor `CategoryTheory.Over.post B.inclusion`, so the structure presheaf
is literally the same presheaf and `AlgebraicGeometry.ChangeOfSites.structureSharp` is applied
to the identity transformation.  This is the exact analogue of `π_S^♯` being the identity.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 03FE](https://stacks.math.columbia.edu/tag/03FE)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 021N](https://stacks.math.columbia.edu/tag/021N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry

/-! ### The chain of the five topologies -/

/-- The position of a topology in the chain `Zariski ≺ étale ≺ smooth ≺ syntomic ≺ fppf`. -/
public abbrev CoveringTopology.rank : CoveringTopology → ℕ
  | .zariski => 0
  | .etale => 1
  | .smooth => 2
  | .syntomic => 3
  | .fppf => 4

/-- `τ` is finer than `τ'`: every `τ'`-covering family is a `τ`-covering family.  This is the
relation along which the change-of-topologies morphisms of Topologies, Section 03FE run. -/
public abbrev CoveringTopology.IsFiner (τ τ' : CoveringTopology) : Prop := τ'.rank ≤ τ.rank

variable {τ τ' : CoveringTopology}

/-- **Stacks 021N and its companions.**  Along the chain, the precoverages of jointly surjective
families of schemes are nested: an open immersion is étale, an étale morphism is smooth, a smooth
morphism is syntomic, and a syntomic morphism is flat and locally of finite presentation. -/
@[stacks 021N "the five precoverages of schemes are nested along the chain of topologies",
  sga "3 IV 6.6" "Diagram 6.6.1"]
public theorem coveringPrecoverage_le_of_isFiner (h : τ.IsFiner τ') :
    Scheme.precoverage (coveringMorphismProperty τ') ≤
      Scheme.precoverage (coveringMorphismProperty τ) := by
  have hz : Scheme.precoverage (coveringMorphismProperty .zariski) ≤
      Scheme.precoverage (coveringMorphismProperty .etale) :=
    Scheme.precoverage_mono fun _ _ _ hi => have := hi; inferInstance
  have he : Scheme.precoverage (coveringMorphismProperty .etale) ≤
      Scheme.precoverage (coveringMorphismProperty .smooth) :=
    Scheme.precoverage_mono fun _ _ f hf => by let : Etale f := hf; infer_instance
  have hs : Scheme.precoverage (coveringMorphismProperty .smooth) ≤
      Scheme.precoverage (coveringMorphismProperty .syntomic) :=
    Scheme.precoverage_mono fun _ _ f hf => by
      let : Smooth f := hf; exact syntomic_of_smooth f
  have hy : Scheme.precoverage (coveringMorphismProperty .syntomic) ≤
      Scheme.precoverage (coveringMorphismProperty .fppf) :=
    Scheme.syntomicPrecoverage_le_fppfPrecoverage
  cases τ <;> cases τ' <;>
    first
      | exact absurd h (by decide)
      | exact le_rfl
      | exact hz
      | exact he
      | exact hs
      | exact hy
      | exact hz.trans he
      | exact he.trans hs
      | exact hs.trans hy
      | exact hz.trans (he.trans hs)
      | exact he.trans (hs.trans hy)
      | exact hz.trans (he.trans (hs.trans hy))

/-! ### The five big topologies carried by one chosen big fppf site -/

namespace BigFppfSite

variable (B : BigFppfSite.{u})

/-- **Stacks 03FF.**  The chosen covering families of the big `τ`-site carried by `B`, as a
predicate on the covering families of `B`'s own category. -/
@[stacks 03FF "the chosen covering families of the big τ-site carried by a big fppf site"]
public def carriedIsCovering : CoveringTopology → Covering B.Schemes → Prop
  | .fppf => B.IsCovering
  | .syntomic => B.toBigSyntomicSite.IsCovering
  | .smooth => B.toBigSmoothSite.IsCovering
  | .etale => B.toBigEtaleSite.IsCovering
  | .zariski => B.toBigZariskiSite.IsCovering

/-- The precoverage of the big `τ`-site carried by `B`, on `B`'s own category. -/
public def carriedPrecoverage : CoveringTopology → Precoverage B.Schemes
  | .fppf => B.precoverage
  | .syntomic => B.toBigSyntomicSite.precoverage
  | .smooth => B.toBigSmoothSite.precoverage
  | .etale => B.toBigEtaleSite.precoverage
  | .zariski => B.toBigZariskiSite.precoverage

/-- A presieve lies in the precoverage of the big `τ`-site carried by `B` exactly when it is
represented by a chosen `τ`-covering family. -/
public theorem mem_carriedPrecoverage_iff (τ : CoveringTopology) {X : B.Schemes}
    {R : Presieve X} :
    R ∈ B.carriedPrecoverage τ X ↔
      ∃ E : PreZeroHypercover.{u + 1} X, R = E.presieve₀ ∧ B.carriedIsCovering τ ⟨X, E⟩ := by
  cases τ with
  | fppf => exact Iff.rfl
  | syntomic => exact Iff.rfl
  | smooth => exact ⟨fun ⟨E, h₁, h₂⟩ => ⟨E, h₂, h₁⟩, fun ⟨E, h₁, h₂⟩ => ⟨E, h₂, h₁⟩⟩
  | etale => exact Iff.rfl
  | zariski => exact ⟨fun ⟨E, h₁, h₂⟩ => ⟨E, h₂, h₁⟩, fun ⟨E, h₁, h₂⟩ => ⟨E, h₂, h₁⟩⟩

/-- The Zariski covering families of `B`'s category, as membership in the precoverage of
jointly surjective families of open immersions. -/
private theorem mem_zariski_iff {E : Covering B.Schemes} :
    IsZariskiCovering (κ := B.cutoff) E ↔ (E.2.map B.inclusion).presieve₀ ∈
      Scheme.precoverage (coveringMorphismProperty .zariski) (B.inclusion.obj E.1) := Iff.rfl

/-- The étale covering families of `B`'s category, as membership in the precoverage of jointly
surjective families of étale morphisms. -/
private theorem mem_etale_iff {E : Covering B.Schemes} :
    IsEtaleCovering (κ := B.cutoff) E ↔ (E.2.map B.inclusion).presieve₀ ∈
      Scheme.precoverage (coveringMorphismProperty .etale) (B.inclusion.obj E.1) := Iff.rfl

/-- The smooth covering families of `B`'s category, as membership in the precoverage of jointly
surjective families of smooth morphisms. -/
private theorem mem_smooth_iff {E : Covering B.Schemes} :
    SmoothCovering B.cutoff E ↔ (E.2.map B.inclusion).presieve₀ ∈
      Scheme.precoverage (coveringMorphismProperty .smooth) (B.inclusion.obj E.1) := Iff.rfl

/-- The syntomic covering families of `B`'s category, as membership in the precoverage of
jointly surjective families of syntomic morphisms. -/
private theorem mem_syntomic_iff {E : Covering B.Schemes} :
    SyntomicCovering B.cutoff E ↔ (E.2.map B.inclusion).presieve₀ ∈
      Scheme.precoverage (coveringMorphismProperty .syntomic) (B.inclusion.obj E.1) :=
  syntomicCovering_iff_mem_precoverage B.cutoff E

/-- A family of `B`'s category whose image is a jointly surjective family of morphisms with the
`τ`-property, and whose index type meets `B`'s covering bound, is a chosen `τ`-covering
family. -/
private theorem carriedIsCovering_of_mem (τ : CoveringTopology) {E : Covering B.Schemes}
    (h₁ : (E.2.map B.inclusion).presieve₀ ∈
      Scheme.precoverage (coveringMorphismProperty τ) (B.inclusion.obj E.1))
    (h₂ : #E.2.I₀ ≤ B.coveringBound) : B.carriedIsCovering τ E := by
  cases τ with
  | fppf => exact ⟨isFppfCovering_of_mem_precoverage B _ le_rfl h₁, h₂⟩
  | syntomic => exact ⟨(B.mem_syntomic_iff).2 h₁, h₂⟩
  | smooth => exact ⟨(B.mem_smooth_iff).2 h₁, h₂⟩
  | etale => exact ⟨(B.mem_etale_iff).2 h₁, h₂⟩
  | zariski => exact ⟨(B.mem_zariski_iff).2 h₁, h₂⟩

/-- **Stacks 03FF, the nesting of the four coarser systems.**  A chosen `τ'`-covering family is
a chosen `τ`-covering family when `τ` is finer than `τ'`: the covering bound is `B`'s own in
every one of the five cases, so only the morphism property changes, and the five properties are
nested. -/
@[stacks 03FF "the chosen covering families are nested along the chain of topologies"]
public theorem carriedIsCovering_mono (h : τ.IsFiner τ') {E : Covering B.Schemes}
    (hE : B.carriedIsCovering τ' E) : B.carriedIsCovering τ E := by
  cases τ' with
  | fppf => cases τ <;> first | exact hE | exact absurd h (by decide)
  | syntomic =>
    exact B.carriedIsCovering_of_mem τ
      (coveringPrecoverage_le_of_isFiner h _ ((B.mem_syntomic_iff).1 hE.1)) hE.2
  | _ =>
    exact B.carriedIsCovering_of_mem τ (coveringPrecoverage_le_of_isFiner h _ hE.1) hE.2

/-- The precoverages of the five big sites carried by `B` are nested along the chain. -/
public theorem carriedPrecoverage_le (h : τ.IsFiner τ') :
    B.carriedPrecoverage τ' ≤ B.carriedPrecoverage τ := by
  intro X R hR
  rw [B.mem_carriedPrecoverage_iff] at hR ⊢
  obtain ⟨E, rfl, hE⟩ := hR
  exact ⟨E, rfl, B.carriedIsCovering_mono h hE⟩

/-- The Grothendieck topology of the big `τ`-site carried by `B`, on `B`'s own category. -/
public abbrev carriedTopology (τ : CoveringTopology) : GrothendieckTopology B.Schemes :=
  (B.carriedPrecoverage τ).toGrothendieck

/-- The topologies of the five big sites carried by `B` are nested along the chain. -/
public theorem carriedTopology_le (h : τ.IsFiner τ') :
    B.carriedTopology τ' ≤ B.carriedTopology τ :=
  Precoverage.toGrothendieck_mono (B.carriedPrecoverage_le h)

/-! ### The five localized topologies, on one category -/

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03FF after localization.**  The topology of the localization at `S` of the big
`τ`-site carried by `B`.  All five live on the one category `Over (B.obj hS)`, because the four
coarser sites have `B`'s own cutoff. -/
public def carriedOverTopology : CoveringTopology → GrothendieckTopology (Over (B.obj hS))
  | .fppf => BigFppfOver.topology B S hS
  | .syntomic => BigSyntomicOver.topology B.toBigSyntomicSite S hS
  | .smooth => BigSmoothOver.topology B.toBigSmoothSite S hS
  | .etale => BigEtaleOver.topology B.toBigEtaleSite S hS
  | .zariski => BigZariskiOver.topology B.toBigZariskiSite S hS

/-- The localized topology is the localization of the topology of the big site. -/
public theorem carriedOverTopology_eq_over (τ : CoveringTopology) :
    B.carriedOverTopology S hS τ = (B.carriedTopology τ).over (B.obj hS) := by
  cases τ with
  | fppf => exact overTopology_eq_over' (τ := .fppf) B S hS
  | syntomic => exact overTopology_eq_over' (τ := .syntomic) B.toBigSyntomicSite S hS
  | smooth => exact overTopology_eq_over' (τ := .smooth) B.toBigSmoothSite S hS
  | etale => exact overTopology_eq_over' (τ := .etale) B.toBigEtaleSite S hS
  | zariski => exact overTopology_eq_over' (τ := .zariski) B.toBigZariskiSite S hS

/-- The five localized topologies are nested along the chain. -/
public theorem carriedOverTopology_le (h : τ.IsFiner τ') :
    B.carriedOverTopology S hS τ' ≤ B.carriedOverTopology S hS τ := by
  rw [B.carriedOverTopology_eq_over S hS τ', B.carriedOverTopology_eq_over S hS τ]
  exact Stacks.Sites.over_mono (B.carriedTopology_le h) _

/-- **Stacks 03DU on all five localized sites at once.**  Global functions are a sheaf of rings
on the localization at `S` of the big `τ`-site carried by `B`. -/
@[stacks 03DU "the structure sheaf of the five localized big sites carried by a big fppf site"]
public theorem carriedOver_structure_isSheaf (τ : CoveringTopology) :
    Presheaf.IsSheaf (B.carriedOverTopology S hS τ)
      (Stacks.Sites.structurePresheaf S (Over.post B.inclusion)) := by
  cases τ with
  | fppf => exact bigSite_structure_isSheaf (τ := .fppf) B S hS
  | syntomic => exact bigSite_structure_isSheaf (τ := .syntomic) B.toBigSyntomicSite S hS
  | smooth => exact bigSite_structure_isSheaf (τ := .smooth) B.toBigSmoothSite S hS
  | etale => exact bigSite_structure_isSheaf (τ := .etale) B.toBigEtaleSite S hS
  | zariski => exact bigSite_structure_isSheaf (τ := .zariski) B.toBigZariskiSite S hS

/-- The localization at `S` of the big `τ`-site carried by `B`, with its structure sheaf, as a
ringed site. -/
public noncomputable abbrev carriedOverRingedSite (τ : CoveringTopology) :
    RingedSite.{u + 1, u, u} :=
  ChangeOfSites.ringedSite S (B.carriedOverTopology S hS τ) (Over.post B.inclusion)
    (B.carriedOver_structure_isSheaf S hS τ)

/-! ### `id_{τ, τ'}` as a morphism of ringed sites -/

/-- The identity functor is continuous from the coarser to the finer of two localized
topologies: a sheaf for the finer topology is a sheaf for the coarser one. -/
public theorem isContinuous_id (h : τ.IsFiner τ') :
    (𝟭 (Over (B.obj hS))).IsContinuous
      (B.carriedOverTopology S hS τ') (B.carriedOverTopology S hS τ) where
  op_comp_isSheaf_of_types G :=
    Presieve.isSheaf_of_le _ (B.carriedOverTopology_le S hS h)
      ((isSheaf_iff_isSheaf_of_type _ _).1 G.property)

/-- **Stacks 070R, the generator `id_{τ, τ'}` of the 03FE list: it is a morphism of sites**, at
the universe of the sections of the structure sheaves.

The identity functor is representably flat, and a localized big site is essentially small at the
universe of its morphisms, so this is `isMorphismOfSites_of_essentiallySmall`. -/
@[stacks 070R "`id_{τ, τ'}` is a morphism of sites, at the universe of the structure rings"]
public theorem isMorphismOfSites_id (h : τ.IsFiner τ') :
    IsMorphismOfSites.{u} (𝟭 (Over (B.obj hS)))
      (B.carriedOverTopology S hS τ') (B.carriedOverTopology S hS τ) :=
  let : EssentiallySmall.{u} (Over (B.obj hS)) :=
    essentiallySmall_overBase (τ := .fppf) B S hS
  let : (𝟭 (Over (B.obj hS))).IsContinuous
    (B.carriedOverTopology S hS τ') (B.carriedOverTopology S hS τ) := B.isContinuous_id S hS h
  isMorphismOfSites_of_essentiallySmall _ _ _

/-- **Stacks 070R for the generator `id_{τ, τ'}`.**  The identity
`id_{τ, τ'} : (\Sch/S)_τ ⟶ (\Sch/S)_{τ'}`, for `τ` finer than `τ'`, as a morphism of ringed
sites

```
  (id_{τ, τ'}, id_{τ, τ'}^♯) : ((\Sch/S)_τ, 𝒪) ⟶ ((\Sch/S)_{τ'}, 𝒪).
```

Its structure map is the identity, by
`AlgebraicGeometry.BigFppfSite.idRingedSiteHom_fsharp`. -/
@[stacks 070R "`id_{τ, τ'}` as a morphism of ringed sites"]
public noncomputable def idRingedSiteHom (h : τ.IsFiner τ') :
    RingedSite.HomGeneral (B.carriedOverRingedSite S hS τ) (B.carriedOverRingedSite S hS τ') :=
  ChangeOfSites.ringedSiteHom (B.carriedOverTopology S hS τ') (B.carriedOverTopology S hS τ)
    (Over.post B.inclusion) (Over.post B.inclusion) (𝟭 (Over (B.obj hS)))
    (B.isMorphismOfSites_id S hS h) (𝟙 _) (B.carriedOver_structure_isSheaf S hS τ')
    (B.carriedOver_structure_isSheaf S hS τ)

/-- The underlying functor of `id_{τ, τ'}` is the identity functor of the schemes over `S`. -/
@[simp]
public theorem idRingedSiteHom_u (h : τ.IsFiner τ') :
    (B.idRingedSiteHom S hS h).u = 𝟭 (Over (B.obj hS)) := rfl

/-- **`id_{τ, τ'}^♯` is the identity.**  The two sites are presented by the one functor to the
schemes over `S`, so their structure presheaves are literally the same presheaf and no
comparison map intervenes. -/
@[stacks 070R "`id_{τ, τ'}^♯` is the identity"]
public theorem idRingedSiteHom_fsharp (h : τ.IsFiner τ') :
    (B.idRingedSiteHom S hS h).fsharp = 𝟙 _ := rfl

/-! ### `f_big` on the five localized sites carried by `B` -/

variable {S} {T : Scheme.{u}} {hS} {hT : B.Contains T}

/-- **Stacks 070R, part (1) on the sites carried by `B`.**  Base change along `f` defines a
morphism of sites between the localizations at `T` and at `S` of the big `τ`-site carried by
`B`, at the universe of the structure rings. -/
public theorem isMorphismOfSites_baseChange (τ : CoveringTopology)
    (f : B.obj hT ⟶ B.obj hS) :
    IsMorphismOfSites.{u} (Over.pullback f)
      (B.carriedOverTopology S hS τ) (B.carriedOverTopology T hT τ) := by
  cases τ with
  | fppf => exact isMorphismOfSites_bigSiteBaseChange (τ := .fppf) B f
  | syntomic => exact isMorphismOfSites_bigSiteBaseChange (τ := .syntomic) B.toBigSyntomicSite f
  | smooth => exact isMorphismOfSites_bigSiteBaseChange (τ := .smooth) B.toBigSmoothSite f
  | etale => exact isMorphismOfSites_bigSiteBaseChange (τ := .etale) B.toBigEtaleSite f
  | zariski => exact isMorphismOfSites_bigSiteBaseChange (τ := .zariski) B.toBigZariskiSite f

/-- The projections `T ×_S S' ⟶ S'` of underlying schemes, on the localized sites carried
by `B`. -/
public noncomputable def baseChangeProjections (f : B.obj hT ⟶ B.obj hS) :
    Over.pullback f ⋙ Over.post B.inclusion ⋙ Over.forget T ⟶
      Over.post B.inclusion ⋙ Over.forget S :=
  Functor.whiskerRight (Over.pullbackForget f) B.inclusion

/-- **Stacks 070R, part (1) on the sites carried by `B`.**  `f_big` as a morphism of ringed
sites, for each of the five topologies. -/
@[stacks 070R "part (1): `f_big` on the five big sites carried by one big fppf site"]
public noncomputable def bigBaseChangeRingedSiteHom (τ : CoveringTopology)
    (f : B.obj hT ⟶ B.obj hS) :
    RingedSite.HomGeneral (B.carriedOverRingedSite T hT τ) (B.carriedOverRingedSite S hS τ) :=
  ChangeOfSites.ringedSiteHom (B.carriedOverTopology S hS τ) (B.carriedOverTopology T hT τ)
    (Over.post B.inclusion) (Over.post B.inclusion) (Over.pullback f)
    (B.isMorphismOfSites_baseChange τ f) (B.baseChangeProjections f)
    (B.carriedOver_structure_isSheaf S hS τ) (B.carriedOver_structure_isSheaf T hT τ)

/-- The underlying functor of `f_big` is base change `Over.pullback f` along `f`. -/
@[simp]
public theorem bigBaseChangeRingedSiteHom_u (τ : CoveringTopology)
    (f : B.obj hT ⟶ B.obj hS) :
    (B.bigBaseChangeRingedSiteHom τ f).u = Over.pullback f := rfl

/-! ### Entries (1)–(15) of the change-of-topologies list -/

/-- **Stacks 070R for every big-site entry of the change-of-topologies list.**  For a morphism of
schemes `f : T ⟶ S` of a chosen big fppf site and `τ` finer than `τ'`, the morphism of sites
`f_{sites} : (\Sch/T)_τ ⟶ (\Sch/S)_{τ'}` of Topologies, Section 03FE is a morphism of ringed
sites

```
  (f_{sites}, f_{sites}^♯) : ((\Sch/T)_τ, 𝒪_T) ⟶ ((\Sch/S)_{τ'}, 𝒪_S).
```

This is entries (1)–(15) of that list: `f_{sites}` is `id_{τ, τ'} ∘ f_{big}`, and the
composition of morphisms of ringed sites is Stacks 03AD, part (3). -/
@[stacks 070R "entries (1)-(15) of the 03FE list: `(Sch/T)_τ ⟶ (Sch/S)_τ'` for τ finer than τ'"]
public noncomputable def bigRingedSiteHom (h : τ.IsFiner τ') (f : B.obj hT ⟶ B.obj hS) :
    RingedSite.HomGeneral (B.carriedOverRingedSite T hT τ) (B.carriedOverRingedSite S hS τ') :=
  (B.bigBaseChangeRingedSiteHom τ f).comp (B.idRingedSiteHom S hS h)

/-- The underlying functor of `f_{sites}` is the identity followed by base change along `f`. -/
@[simp]
public theorem bigRingedSiteHom_u (h : τ.IsFiner τ') (f : B.obj hT ⟶ B.obj hS) :
    (B.bigRingedSiteHom h f).u = 𝟭 (Over (B.obj hS)) ⋙ Over.pullback f := rfl

end BigFppfSite

end AlgebraicGeometry

end
