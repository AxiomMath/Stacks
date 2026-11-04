module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.ComparisonFunctoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SheafCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickeningScheme

/-!
# The first-order comparison datum of a crystal on `Cris(X/S)`

Let `F` be a crystal in `𝒪_{X/S}`-modules on the small crystalline site `Cris(X/S)` of a global
crystalline situation, that is, a sheaf of `𝒪_{X/S}`-modules all of whose comparison maps
`c_f : f^* F_{T'} ⟶ F_T` of sheaves of modules are isomorphisms
(`Crystalline.GlobalCrystallineSituation.SmallSite.IsSheafCrystal`).  Let `(U, T, δ)` be an object
of `Cris(X/S)` and let `(U, T', δ')` be its first-order universal thickening of
[Stacks, Tag 07J2], an object of `Cris(X/S)` by
`Crystalline.GlobalCrystallineSituation.firstOrderThickeningCrysObject`, with the two projections
`p₀, p₁ : T' ⟶ T` and the diagonal `i : T ⟶ T'` satisfying `p₀ ∘ i = p₁ ∘ i = id`.

Evaluating `F` at `(U, T', δ')` and reading the comparison maps at the two projections gives two
isomorphisms

`c₀ : p₀^* F_T ≅ F_{T'}`   and   `c₁ : p₁^* F_T ≅ F_{T'}`,

and `ε = c₁⁻¹ ∘ c₀ : p₀^* F_T ≅ p₁^* F_T` is the **first-order comparison datum** of the crystal:
the identification of the two pullbacks of `F_T` along the two projections, which is the input of
[Stacks, Tag 07JG].  This module builds `ε`, proves it functorial in the crystal, and proves that
it is the identity on the diagonal — the three things a reduction
{crystals on `Cris(X/S)`} ⟶ {first-order comparison data} has to supply.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`, the
functoriality of the comparison map in the module in its subnamespace `CohomologyRestriction`.

* `CohomologyRestriction.moduleRestrictionMap` and
  `CohomologyRestriction.moduleRestrictionSheafMap` — the restriction `F ↦ F_T` to the ambient
  scheme of an object of `Cris(X/S)`, made functorial in the module, for presheaves and for
  sheaves of modules.
* `firstOrderComparisonP₀` and `firstOrderComparisonP₁` — the comparison isomorphisms
  `c₀ : p₀^* F_T ≅ F_{T'}` and `c₁ : p₁^* F_T ≅ F_{T'}` of a crystal at the two projections of the
  first-order universal thickening.
* `firstOrderComparison` — **the first-order comparison datum** `ε = c₁⁻¹ ∘ c₀`.
* `firstOrderComparisonUnit` — the datum of the structure sheaf `𝒪_{X/S}`, which witnesses that
  the construction is not vacuous.

## Main results

* `CohomologyRestriction.moduleFMap_naturality`,
  `CohomologyRestriction.moduleFMapSheaf_naturality` and
  `CohomologyRestriction.moduleComparisonSheaf_naturality` — **the `f`-map and the comparison map
  of [Stacks, Tag 07IQ] on the small crystalline site are natural in the module.**
* `firstOrderComparison_naturality` — **the comparison datum is natural in the crystal**, which is
  the functoriality of the reduction of [Stacks, Tag 07JG].
* `map_crysι_crysP₀` and `map_crysι_crysP₁` — **both projections retract the diagonal on sections
  of the crystal**, so the comparison datum is the identity modulo the ideal of `i`, which
  [Stacks, Tag 07J2] identifies with `Ω_{T/S,δ} = (Ω_{X/S})_T`.
* `restrictOpenMap_comp` — the restrictions of a morphism of `Cris(X/S)` over the opens of the
  ambient schemes compose, the small-site form of
  `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenMap_comp`.

## Scope

What is proved is the *construction* half of [Stacks, Tag 07JG] at the level of sheaves: a crystal
on `Cris(X/S)` determines, functorially, an isomorphism `ε : p₀^* F_T ≅ p₁^* F_T` of sheaves of
`𝒪_{T'}`-modules which is the identity on the diagonal.  The datum is built over every object of
`Cris(X/S)`, so [Stacks, Tag 07JN], which identifies `Spec(D)` and its finite levels with objects
of the site, is not needed for it; it is needed only to specialize to the ring `D` of
[Stacks, Situation 07MD] in which `Crystalline.firstOrderCrystalsToPairs` is written.

The passage from `ε` to the algebraic datum `Crystalline.FirstOrderComparison`, the source of the
functor `Crystalline.firstOrderCrystalsToPairs`, is not made here.
`Crystalline.FirstOrderComparison` asks for a map `M → (D ⊕ Ω) ⊗_D M` on a `D`-module `M`.  Taking
`D = Γ(T, 𝒪_T)` with its divided powers, `Ω = Γ(T, Ω_{T/S,δ})` and `M = Γ(T, F_T)`, the sections
of `𝒪_{T'}` are `D ⊕ Ω` and the candidate map is the restriction of a section along `p₁`, read
inside `(D ⊕ Ω) ⊗_D M` through `ε`.
Reading it there needs the *sections* of `SheafOfModules.pullback` to be the base change
`(D ⊕ Ω) ⊗_D M`, which is the datum
`Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange`.  The canonical map
`(D ⊕ Ω) ⊗_D M → Γ(T', F_{T'})`, `a ⊗ s ↦ a · p₀^* s`, is balanced by
`Crystalline.GlobalCrystallineSituation.firstOrderThickeningDiffSection_smul_balanced`; the datum
asks for its inverse.

For the pullback of *presheaves* of modules that inverse exists:
`Stacks.NoncommChangeOfRings.Presheaf.objIsoOfIsIso` identifies the sections of the pullback with
the base change for a change of rings on a fixed site, which is the shape `p₀` and `p₁` have — `T`
and `T'` have the same underlying space and both projections have identity base — and
`Stacks.PullbackEquivalence.pullbackObjIsoBaseChange` does the same for a fully faithful functor of
sites.  Both consume invertibility of the comparison map of presheaves of modules, that is
`Crystalline.GlobalCrystallineSituation.IsCrystal`.  The hypothesis used here is the sheaf-level
`IsSheafCrystal`, which is weaker
(`Crystalline.GlobalCrystallineSituation.isSheafCrystal_of_isCrystal`): it says that `c₀` is an
isomorphism of sheaves, which gives `Γ(T', p₀^* F_T) ≅ Γ(T', F_{T'})` for the sheaf-level
pullback, but says nothing about the left-hand side being a tensor product, the sheaf-level
pullback being the sheafification of `W ↦ 𝒪_{T'}(W) ⊗_{𝒪_T(W)} F_T(W)`.  This is where the
quasi-coherence hypothesis in the source of [Stacks, Tag 07JG] enters.

The conditions (07JB) `p`-adic completeness, (07JD) integrability and (07JE) topological
quasi-nilpotence of [Stacks, Tag 07JG] are properties of the module `M` and of the connection, and
are not addressed here.  For the data of `Crystalline.TaylorCrystal` they are
`Crystalline.TaylorCrystal.isPAdicallyComplete`, `Crystalline.TaylorCrystal.isIntegrable` and
`Crystalline.TaylorCrystal.isTopologicallyQuasiNilpotent`.

## Implementation notes

The functoriality of the restriction `F ↦ F_T` in the module is proved here for the small site
rather than reused, because the library has it only for the big site
(`Crystalline.GlobalCrystallineSituation.Thickening.moduleRestrictionMap` and its naturality
lemmas) and a sheaf of modules on `Cris(X/S)` is in general not the restriction of one on
`CRIS(X/S)`, so the big-site statements do not typecheck for it.  The proofs are the big-site
proofs verbatim: the
`f`-map is, over an open `W` of the ambient scheme of the target, the restriction map of the module
along the restriction of the morphism over `W`, so its naturality square is that of the morphism of
modules, and naturality of the comparison map follows by transposing along the adjunction between
pullback and pushforward.

The two retraction statements are about restriction along a morphism of the *site*, not along a
morphism of opens, so no preimage of an open appears in them and they need no transport.  The
corresponding statement about `CrystallineThickening.restrictOpenMap`, where the preimage does
appear, is not type-correct at the
reduced transparency at which the rewriting tactics operate — the two sides are indexed by opens
that are equal only by unfolding the structure sheaf of `T'` — which is why the composition law
`restrictOpenMap_comp` is proved here but the identity law is not stated.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### The restrictions of a morphism of `Cris(X/S)` over the opens compose -/

/-- **The restrictions of a morphism of `Cris(X/S)` over the opens of the ambient schemes
compose.**  For `f : (U, T, δ) ⟶ (U', T', δ')` and `g : (U', T', δ') ⟶ (U'', T'', δ'')` and an open
`W` of `T''`, the restriction of `f ≫ g` over `W` is the restriction of `f` over `g⁻¹W` followed by
the restriction of `g` over `W`.  Both sides are the restriction of the corresponding morphism of
`CRIS(X/S)`, so this is
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenMap_comp`. -/
theorem restrictOpenMap_comp {S : GlobalCrystallineSituation.{u}}
    {A B C : CrystallineThickening S} (g : A ⟶ B) (h : B ⟶ C)
    (W : C.obj.thickening.target.scheme.Opens) :
    CrystallineThickening.restrictOpenMap (g ≫ h) W =
      CrystallineThickening.restrictOpenMap g (h.hom.targetHom.hom ⁻¹ᵁ W) ≫
        CrystallineThickening.restrictOpenMap h W :=
  ObjectProperty.hom_ext _ (Thickening.restrictOpenMap_comp g.hom h.hom W)

namespace CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} {A B : CrystallineThickening S}

/-! ### The comparison map of the small site is natural in the module -/

/-- **The restriction to the ambient scheme of an object of `Cris(X/S)` of a morphism of presheaves
of `𝒪_{X/S}`-modules.**  Over an open `W` it is the given morphism over the restriction of the
object to `W`; this makes the restriction `F ↦ F_T` of [Stacks, Tag 07IQ] a functor in the module,
being the image under the pushforward along the restrictions to the opens of the ambient
scheme. -/
def moduleRestrictionMap {M N : PresheafOfModules.{u} (crisRing S)} (φ : M ⟶ N)
    (A : CrystallineThickening S) : moduleRestriction M A ⟶ moduleRestriction N A :=
  (PresheafOfModules.pushforward₀ (CrystallineThickening.restrictOpenFunctor A)
    (crisRing S)).map φ

/-- **The `f`-map of [Stacks, Tag 07IQ] on the small crystalline site is natural in the presheaf of
modules.**  Over an open `W` of the ambient scheme of the target both sides are the restriction map
along the restriction of the morphism over `W` followed, in the two possible orders, by the given
morphism of presheaves of modules; so the square is the naturality square of that morphism. -/
theorem moduleFMap_naturality {M N : PresheafOfModules.{u} (crisRing S)} (φ : M ⟶ N)
    (g : A ⟶ B) :
    moduleRestrictionMap φ B ≫ moduleFMap N g =
      moduleFMap M g ≫ (PresheafOfModules.pushforward
        (F := Opens.map g.hom.targetHom.hom.base)
        (restrictionFMap (crisRing S) g)).map (moduleRestrictionMap φ A) := by
  ext W x
  exact (PresheafOfModules.naturality_apply φ
    (CrystallineThickening.restrictOpenMap g W.unop).op x).symm

/-- **The restriction to the ambient scheme of an object of `Cris(X/S)` of a morphism of sheaves of
`𝒪_{X/S}`-modules.**  It is the restriction of the underlying morphism of presheaves of modules,
the restriction of a sheaf being computed on the same sections; this makes the restriction
`F ↦ F_T` a functor in the module at sheaf level, which is the level at which the crystal condition
of [Stacks, Tag 07IS] is read. -/
def moduleRestrictionSheafMap {M N : SheafOfModules.{u} (structureSheaf S)} (ψ : M ⟶ N)
    (A : CrystallineThickening S) :
    moduleRestrictionSheaf M A ⟶ moduleRestrictionSheaf N A :=
  ⟨moduleRestrictionMap ψ.val A⟩

/-- The restriction of a morphism of sheaves of modules is the restriction of the underlying
morphism of presheaves of modules. -/
@[simp]
theorem moduleRestrictionSheafMap_val {M N : SheafOfModules.{u} (structureSheaf S)} (ψ : M ⟶ N)
    (A : CrystallineThickening S) :
    (moduleRestrictionSheafMap ψ A).val = moduleRestrictionMap ψ.val A := rfl

/-- **The `f`-map of [Stacks, Tag 07IQ] on the small crystalline site, for sheaves of modules, is
natural in the module.**  A morphism of sheaves of modules is its underlying morphism of presheaves
of modules, so this is
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.moduleFMap_naturality`. -/
theorem moduleFMapSheaf_naturality {M N : SheafOfModules.{u} (structureSheaf S)} (ψ : M ⟶ N)
    (g : A ⟶ B) :
    moduleRestrictionSheafMap ψ B ≫ moduleFMapSheaf N g =
      moduleFMapSheaf M g ≫
        (SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap g.hom)).map
          (moduleRestrictionSheafMap ψ A) :=
  SheafOfModules.Hom.ext (moduleFMap_naturality ψ.val g)

/-- **The comparison map `c_f : f^* F_{T'} ⟶ F_T` of sheaves of modules on the small crystalline
site is natural in the module.**  This is the sense in which a crystal determines a comparison
*datum* functorially in the crystal: the proof transposes along the adjunction between pullback and
pushforward of sheaves of modules, under which the comparison map corresponds to the `f`-map, and
the two transposed sides are the two sides of `moduleFMapSheaf_naturality`. -/
theorem moduleComparisonSheaf_naturality {M N : SheafOfModules.{u} (structureSheaf S)}
    (ψ : M ⟶ N) (g : A ⟶ B) :
    (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g.hom)).map
          (moduleRestrictionSheafMap ψ B) ≫ moduleComparisonSheaf N g =
      moduleComparisonSheaf M g ≫ moduleRestrictionSheafMap ψ A := by
  refine ((SheafOfModules.pullbackPushforwardAdjunction.{u}
    (Thickening.ringRestrictionSheafFMap g.hom)).homEquiv (moduleRestrictionSheaf M B)
      (moduleRestrictionSheaf N A)).injective ?_
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    ← moduleFMapSheaf_eq_moduleComparisonSheaf, ← moduleFMapSheaf_eq_moduleComparisonSheaf]
  exact moduleFMapSheaf_naturality ψ g

end CohomologyRestriction

/-! ### Both projections retract the diagonal on sections -/

variable {S : GlobalCrystallineSituation.{u}}

/-- Restricting a section along `p` and then along a section `i` of `p` recovers the section. -/
private theorem map_map_of_comp_eq_id (M : PresheafOfModules.{u} (crisRing S))
    {B C : CrystallineThickening S} (i : B ⟶ C) (p : C ⟶ B) (h : i ≫ p = 𝟙 B)
    (x : M.obj (op B)) : M.map i.op (M.map p.op x) = x := by
  have h' : p.op ≫ i.op = 𝟙 (op B) := congrArg Quiver.Hom.op h
  rw [← PresheafOfModules.map_comp_apply, M.congr_map_apply h',
    ← PresheafOfModules.presheaf_map_apply_coe, M.presheaf.map_id]
  rfl

/-- **The first projection of the first-order universal thickening is a section of the diagonal on
the sections of a module.**  Restricting a section of `F` over `(U, T, δ)` along `p₀` and then
along `i` recovers it, because `p₀ ∘ i = id` in `Cris(X/S)`.  Together with the same statement for
`p₁` this is the condition that the comparison datum of [Stacks, Tag 07JG] is the identity modulo
the ideal of the diagonal, which [Stacks, Tag 07J2] identifies with `Ω_{T/S,δ} = (Ω_{X/S})_T`. -/
theorem map_crysι_crysP₀ (M : PresheafOfModules.{u} (crisRing S))
    (B : CrystallineThickening S) (x : M.obj (op B)) :
    M.map (firstOrderThickeningCrysι S B).op
      (M.map (firstOrderThickeningCrysP₀ S B).op x) = x :=
  map_map_of_comp_eq_id M _ _ (firstOrderThickeningCrysι_comp_P₀ S B) x

/-- **The second projection of the first-order universal thickening is a section of the diagonal on
the sections of a module.**  Restricting a section of `F` over `(U, T, δ)` along `p₁` and then
along `i` recovers it, because `p₁ ∘ i = id` in `Cris(X/S)`. -/
theorem map_crysι_crysP₁ (M : PresheafOfModules.{u} (crisRing S))
    (B : CrystallineThickening S) (x : M.obj (op B)) :
    M.map (firstOrderThickeningCrysι S B).op
      (M.map (firstOrderThickeningCrysP₁ S B).op x) = x :=
  map_map_of_comp_eq_id M _ _ (firstOrderThickeningCrysι_comp_P₁ S B) x

/-- **The two projections agree on the diagonal.**  The two restrictions of a section of `F` over
`(U, T, δ)` to `(U, T', δ')` become the same section after restricting along the diagonal, both
being the section itself.

For a crystal these two restrictions are the two legs of the comparison datum
`firstOrderComparison` read through the isomorphism `c₁`, so this is the clause that the datum is
the identity modulo the ideal of `i`, which [Stacks, Tag 07J2] identifies with
`Ω_{T/S,δ} = (Ω_{X/S})_T`.  As stated it needs nothing of `F`: it is an identity between
restriction maps along two equal morphisms of the site, so the quantifier runs over all presheaves
of `𝒪_{X/S}`-modules and the crystal hypothesis is what makes it a statement about the datum. -/
theorem map_crysι_crysP₀_eq_map_crysι_crysP₁ (M : PresheafOfModules.{u} (crisRing S))
    (B : CrystallineThickening S) (x : M.obj (op B)) :
    M.map (firstOrderThickeningCrysι S B).op
        (M.map (firstOrderThickeningCrysP₀ S B).op x) =
      M.map (firstOrderThickeningCrysι S B).op
        (M.map (firstOrderThickeningCrysP₁ S B).op x) :=
  (map_crysι_crysP₀ M B x).trans (map_crysι_crysP₁ M B x).symm

/-! ### The comparison datum -/

open CohomologyRestriction

variable (F : SheafOfModules.{u} (structureSheaf S))

/-- **The comparison isomorphism of a crystal at the first projection**, `c₀ : p₀^* F_T ≅ F_{T'}`:
the comparison map of [Stacks, Tag 07IQ] at the morphism `p₀ : (U, T', δ') ⟶ (U, T, δ)` of
`Cris(X/S)`, which is an isomorphism because `F` is a crystal. -/
def firstOrderComparisonP₀ (hF : IsSheafCrystal F) (B : CrystallineThickening S) :
    (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap
          (firstOrderThickeningCrysP₀ S B).hom)).obj (moduleRestrictionSheaf F B) ≅
      moduleRestrictionSheaf F (firstOrderThickeningCrysObject S B) :=
  haveI := hF _ _ (firstOrderThickeningCrysP₀ S B)
  asIso (moduleComparisonSheaf F (firstOrderThickeningCrysP₀ S B))

/-- **The comparison isomorphism of a crystal at the second projection**,
`c₁ : p₁^* F_T ≅ F_{T'}`. -/
def firstOrderComparisonP₁ (hF : IsSheafCrystal F) (B : CrystallineThickening S) :
    (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap
          (firstOrderThickeningCrysP₁ S B).hom)).obj (moduleRestrictionSheaf F B) ≅
      moduleRestrictionSheaf F (firstOrderThickeningCrysObject S B) :=
  haveI := hF _ _ (firstOrderThickeningCrysP₁ S B)
  asIso (moduleComparisonSheaf F (firstOrderThickeningCrysP₁ S B))

/-- The forward map of the comparison isomorphism at the first projection is the comparison map of
[Stacks, Tag 07IQ] at that projection. -/
@[simp]
theorem firstOrderComparisonP₀_hom (hF : IsSheafCrystal F) (B : CrystallineThickening S) :
    (firstOrderComparisonP₀ F hF B).hom =
      moduleComparisonSheaf F (firstOrderThickeningCrysP₀ S B) := rfl

/-- The forward map of the comparison isomorphism at the second projection is the comparison map of
[Stacks, Tag 07IQ] at that projection. -/
@[simp]
theorem firstOrderComparisonP₁_hom (hF : IsSheafCrystal F) (B : CrystallineThickening S) :
    (firstOrderComparisonP₁ F hF B).hom =
      moduleComparisonSheaf F (firstOrderThickeningCrysP₁ S B) := rfl

/-- **The first-order comparison datum of a crystal on `Cris(X/S)`.**  For an object `(U, T, δ)` of
`Cris(X/S)` with first-order universal thickening `(U, T', δ')` of [Stacks, Tag 07J2], the
isomorphism

`ε = c₁⁻¹ ∘ c₀ : p₀^* F_T ≅ p₁^* F_T`

of sheaves of `𝒪_{T'}`-modules obtained by evaluating the crystal at `(U, T', δ')` and reading the
comparison maps of [Stacks, Tag 07IQ] at the two projections.  This is the datum from which
[Stacks, Tag 07JG] builds the pair `(M, ∇)`: it identifies the two pullbacks of `F_T` along the two
projections, it is the identity on the diagonal (`map_crysι_crysP₀_eq_map_crysι_crysP₁`), and it
is functorial in the crystal (`firstOrderComparison_naturality`).

This is the input of the functor of the tag, not the functor itself.  The passage from the
geometric datum to the algebraic one, `Crystalline.FirstOrderComparison`, and hence to the pairs
`(M, ∇)`, needs the sections of `SheafOfModules.pullback` to be a base change — the datum
`Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange`, which follows from
invertibility of the comparison map of *presheaves* of modules and not from the sheaf-level
crystal condition assumed here; see the module documentation. -/
def firstOrderComparison (hF : IsSheafCrystal F) (B : CrystallineThickening S) :
    (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap
          (firstOrderThickeningCrysP₀ S B).hom)).obj (moduleRestrictionSheaf F B) ≅
      (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap
          (firstOrderThickeningCrysP₁ S B).hom)).obj (moduleRestrictionSheaf F B) :=
  firstOrderComparisonP₀ F hF B ≪≫ (firstOrderComparisonP₁ F hF B).symm

/-- The comparison datum is the comparison map at `p₀` followed by the inverse of the comparison
map at `p₁`. -/
theorem firstOrderComparison_hom (hF : IsSheafCrystal F) (B : CrystallineThickening S) :
    (firstOrderComparison F hF B).hom =
      moduleComparisonSheaf F (firstOrderThickeningCrysP₀ S B) ≫
        (firstOrderComparisonP₁ F hF B).inv := rfl

/-- **The first-order comparison datum is natural in the crystal.**  A morphism `ψ : F ⟶ G` of
sheaves of `𝒪_{X/S}`-modules between two crystals carries the datum of `F` to the datum of `G`:
the square formed by `ε_F`, `ε_G` and the two pullbacks of the restriction of `ψ` commutes.

This is the functoriality of the reduction of [Stacks, Tag 07JG] — the half of the statement that
makes it a functor rather than an assignment on objects.  The proof is the naturality in the module
of the comparison map at the two projections,
`CohomologyRestriction.moduleComparisonSheaf_naturality`, the second of the two squares being
inverted.

The square is the one of the comparison data `ε : p₀^* F_T ≅ p₁^* F_T`.  The corresponding square
of the pairs `(M, ∇)` is `Crystalline.GlobalCrystallineSituation.moduleSiteMap_crystalConnection`.
-/
theorem firstOrderComparison_naturality {F G : SheafOfModules.{u} (structureSheaf S)}
    (hF : IsSheafCrystal F) (hG : IsSheafCrystal G) (ψ : F ⟶ G)
    (B : CrystallineThickening S) :
    (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap
            (firstOrderThickeningCrysP₀ S B).hom)).map
          (moduleRestrictionSheafMap ψ B) ≫ (firstOrderComparison G hG B).hom =
      (firstOrderComparison F hF B).hom ≫
        (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap
            (firstOrderThickeningCrysP₁ S B).hom)).map
          (moduleRestrictionSheafMap ψ B) := by
  have h0 := moduleComparisonSheaf_naturality ψ (firstOrderThickeningCrysP₀ S B)
  have h1 := moduleComparisonSheaf_naturality ψ (firstOrderThickeningCrysP₁ S B)
  have key : moduleRestrictionSheafMap ψ (firstOrderThickeningCrysObject S B) ≫
        (firstOrderComparisonP₁ G hG B).inv =
      (firstOrderComparisonP₁ F hF B).inv ≫
        (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap
          (firstOrderThickeningCrysP₁ S B).hom)).map (moduleRestrictionSheafMap ψ B) := by
    rw [Iso.comp_inv_eq, Category.assoc, firstOrderComparisonP₁_hom, h1, ← Category.assoc,
      ← firstOrderComparisonP₁_hom F hF B, Iso.inv_hom_id, Category.id_comp]
  rw [firstOrderComparison_hom, firstOrderComparison_hom, ← Category.assoc, h0, Category.assoc,
    key, ← Category.assoc]

/-- **The structure sheaf of `Cris(X/S)` is a crystal in `𝒪_{X/S}`-modules.**  It is the
restriction to `Cris(X/S)` of the structure sheaf of `CRIS(X/S)`, which is a crystal by
`Crystalline.GlobalCrystallineSituation.isSheafCrystal_unit`, and the crystal condition is
inherited by restriction. -/
theorem isSheafCrystal_restrictUnit (S : GlobalCrystallineSituation.{u}) :
    IsSheafCrystal
      (restrictSheafOfModules (SheafOfModules.unit (crystallineStructureSheaf S))) :=
  isSheafCrystal_restrictSheafOfModules (isSheafCrystal_unit S)

/-- **The first-order comparison datum of the structure sheaf `𝒪_{X/S}`.**  The one crystal whose
datum is known outright, which witnesses that the construction above is not vacuous; by
`Crystalline.GlobalCrystallineSituation.crystalConnection_unit` the connection it determines is the
universal divided power derivation `d_{T/S,δ}`. -/
def firstOrderComparisonUnit (S : GlobalCrystallineSituation.{u})
    (B : CrystallineThickening S) :
    (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap
          (firstOrderThickeningCrysP₀ S B).hom)).obj
        (moduleRestrictionSheaf
          (restrictSheafOfModules (SheafOfModules.unit (crystallineStructureSheaf S))) B) ≅
      (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap
          (firstOrderThickeningCrysP₁ S B).hom)).obj
        (moduleRestrictionSheaf
          (restrictSheafOfModules (SheafOfModules.unit (crystallineStructureSheaf S))) B) :=
  firstOrderComparison _ (isSheafCrystal_restrictUnit S) B

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
