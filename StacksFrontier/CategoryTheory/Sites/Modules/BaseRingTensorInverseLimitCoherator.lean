module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite
public import StacksFrontier.CategoryTheory.Sites.Modules.BaseRingTensorInverseLimit
import StacksCore.Tactic.StacksAttribute

/-!
# The two readings of the headline of Stacks 0D3F

Let `(C, J)` be a site, let `O` be a sheaf of commutative rings on it, let `R` be a base ring for
`O` given by a ring map `φ : R →+* Γ(C, O)`, and let `(M_n)` be an inverse system of `R`-modules.
`StacksFrontier.CategoryTheory.Sites.Modules.BaseRingTensorInverseLimit` builds the module
`𝒪_X ⊗_R M` of Stacks 0D3F and the canonical map
`𝒪_X ⊗_R (lim M_n) ⟶ lim (𝒪_X ⊗_R M_n)`.

The headline of Stacks 0D3F asserts that this canonical map *induces an isomorphism from its
source onto `DQ_X` applied to its target*, where `DQ_X` is the derived coherator of Stacks 0CR4,
the right adjoint of the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`.  The source immediately rereads that
assertion (`spaces-perfect.tex`): "The statement means that for any object `E` of
`D_QCoh(𝒪_X)` the induced map `Hom(E, 𝒪_X ⊗_R lim M_n) → Hom(E, lim 𝒪_X ⊗_R M_n)` is an
isomorphism."

**That rereading is what this file proves**, and nothing more.  It is a formal consequence of
`DQ_X` being a right adjoint of a fully faithful inclusion, so it needs no hypothesis on `f`, on
the inverse system or on the site; and it is proved here for the comparison map of Stacks 0D3F
itself, so it identifies the two framings of the headline as the same statement.  **Neither
framing is proved**: see "What this file does not prove" below.

## Main results

* `CategoryTheory.Adjunction.bijective_comp_map_iff_isIso_homEquiv`: the general fact.  For a
  fully faithful `ι : 𝒞 ⥤ 𝒟` with right adjoint `DQ`, an object `A` of `𝒞`, an object `B` of `𝒟`
  and a morphism `g : ι.obj A ⟶ B`, the transpose `A ⟶ DQ.obj B` of `g` is an isomorphism exactly
  when composition with `g` is bijective on morphisms out of `ι.obj E` for every object `E`
  of `𝒞`.
* `Stacks.Cohomology.SiteModules.isIso_homEquiv_baseRingTensorLimitComparison_iff`: the same
  equivalence for the canonical map of Stacks 0D3F and the inclusion
  `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`.

## What this file does not prove

The headline of Stacks 0D3F is the assertion that, when `f : X → Spec(R)` is proper, flat and of
finite presentation and the transition maps of `(M_n)` are surjective, the two equivalent
conditions above *hold*.  Nothing here proves either of them, and no declaration here assumes
either of them or any half of either: the statement below is an `Iff` between them, with the
quantified bijectivity on the right and the invertibility of the transpose on the left, and its
proof uses only the adjunction.

The source's proof of the headline reduces to perfect `E` using a perfect generator of
`D_QCoh(𝒪_X)` (Stacks 09IY), replaces the ordinary limit by the derived limit (Stacks 0D3E,
clause (1)), exchanges `R Hom_X(E, -)` with the derived limit, identifies each term with
`R Γ(X, E^∨) ⊗^L_R M_n` by the projection formula (Stacks 08IN) and the perfectness of
`R Γ(X, E^∨)` over `R` (Stacks 0CTM), and concludes with Stacks 0D2L.  Of these the repository
carries Stacks 0D2L (`Stacks.PseudoCoherent.DerivedInverseLimit.derivedLimit_tensor_iso`) and
clauses (1), (2) and (3) of Stacks 0D3E; it carries no form of Stacks 09IY, Stacks 08IN or
Stacks 0CTM, and no statement exchanging `R Hom_X(E, -)` with a derived limit in the covariant
variable.

## Implementation notes

*Where `D_QCoh` comes from.*  `SheafOfModules.isQuasicoherentOnSite` is a property of a sheaf of
modules on an arbitrary site, and `DerivedCategoryB.derivedCategoryB` turns any object property
on an abelian category into one on its derived category, so `D_QCoh(𝒪_X)` is available on the
same abstract site as the comparison map, over the very category
`SheafOfModules (ringSheafOfSite O)` in which the comparison map lives.  No small étale site of
an algebraic space, and no sheaf-of-modules tensor beyond the one
`StacksFrontier.CategoryTheory.Sites.Modules.BaseRingTensorInverseLimit` already uses, is needed to
state the headline.

*The existence of `DQ_X` is a hypothesis, named as such.*  On the small étale site of a
quasi-compact quasi-separated algebraic space the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` does have a
right adjoint: that is Stacks 0CR4,
`AlgebraicGeometry.Space.quasicoherentDerivedInclusion_isLeftAdjoint`.  On a general site there
is no such theorem and none is expected, so the adjunction is taken as an explicit argument.  It
is not the conclusion in disguise: an adjunction `ι ⊣ DQ` says nothing about any particular
morphism, and the right-hand side of the equivalence below does not mention `DQ` at all.

*Why the source is assumed quasi-coherent.*  `DQ_X` applied to the target is an object of
`D_QCoh(𝒪_X)`, so for the headline to be the assertion that the comparison map *induces an
isomorphism onto it* the source must lie in `D_QCoh(𝒪_X)` as well.  That membership is therefore
part of the shape of the statement rather than part of its content, and it is supplied as the
hypothesis `hsrc`.  In the geometric situation it is automatic: `𝒪_X ⊗_R M` is quasi-coherent by
`Stacks.Cohomology.SiteModules.isQuasicoherentOnSite_sectionTensor` wherever the universes of
that lemma permit.

*The model of the derived category* is `CategoryTheory.HasDerivedCategory.standard`, the one at
which `AlgebraicGeometry.Space.QuasicoherentDerivedCategory` of Stacks 071X and the coherator of
Stacks 0CR4 are stated.

*Universes.*  The module universe is `max u r w` with `w` free, the one at which
`StacksFrontier.CategoryTheory.Sites.Modules.BaseRingTensorInverseLimit` states the comparison map;
nothing here narrows it.  Abelianness of the `O`-modules is an instance *assumption* rather than
an appeal to `Stacks.SheafOfModules.sheafModulesGrothendieck`, because that theorem needs the
module universe to contain the universe `v` of the morphisms of the site, which `max u r w` need
not.  Making it an assumption keeps the statement at the comparison map's own universe instead of
restricting to `max u v r w`; it is satisfied by instance search in every case where the module
universe does contain `v`.  This is the idiom of
`Stacks.SheafOfModules.balanced_of_abelian`.

## References

* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 0CR4](https://stacks.math.columbia.edu/tag/0CR4)
* [Stacks Project, Tag 071X](https://stacks.math.columbia.edu/tag/071X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Adjunction

/-- **Invertibility of a transpose, read on morphisms out of the subcategory.**  Let
`ι : 𝒞 ⥤ 𝒟` be fully faithful with right adjoint `DQ`, let `A` be an object of `𝒞`, let `B` be an
object of `𝒟` and let `g : ι.obj A ⟶ B`.  The transpose `A ⟶ DQ.obj B` of `g` is an isomorphism
exactly when composition with `g` is bijective on morphisms out of `ι.obj E`, for every object
`E` of `𝒞`.

Both directions are the naturality of the adjunction bijection in its left variable, which turns
composition with `g` into composition with the transpose, together with fullness and
faithfulness of `ι`, which turn morphisms `ι.obj E ⟶ ι.obj A` into morphisms `E ⟶ A`; the
quantified form on the right is then invertibility by the Yoneda lemma. -/
theorem bijective_comp_map_iff_isIso_homEquiv {𝒞 : Type*} [Category 𝒞] {𝒟 : Type*} [Category 𝒟]
    {ι : 𝒞 ⥤ 𝒟} [ι.Full] [ι.Faithful] {DQ : 𝒟 ⥤ 𝒞} (adj : ι ⊣ DQ)
    (A : 𝒞) (B : 𝒟) (g : ι.obj A ⟶ B) :
    (∀ E : 𝒞, Function.Bijective (fun a : ι.obj E ⟶ ι.obj A => a ≫ g)) ↔
      IsIso (adj.homEquiv A B g) := by
  have hmap : ∀ E : 𝒞, Function.Bijective (ι.map : (E ⟶ A) → (ι.obj E ⟶ ι.obj A)) :=
    fun E => ⟨fun _ _ h => ι.map_injective h, fun a => ι.map_surjective a⟩
  have hiff : ∀ E : 𝒞,
      Function.Bijective (fun a' : E ⟶ A => a' ≫ adj.homEquiv A B g) ↔
        Function.Bijective (fun a : ι.obj E ⟶ ι.obj A => a ≫ g) := by
    intro E
    have hcomp : (fun a' : E ⟶ A => a' ≫ adj.homEquiv A B g) =
        (adj.homEquiv E B) ∘ ((fun a : ι.obj E ⟶ ι.obj A => a ≫ g) ∘ ι.map) := by
      funext a'
      exact (adj.homEquiv_naturality_left a' g).symm
    rw [hcomp, (adj.homEquiv E B).bijective.of_comp_iff', (hmap E).of_comp_iff]
  constructor
  · intro h
    exact isIso_of_yoneda_map_bijective _ fun E => (hiff E).2 (h E)
  · intro h E
    refine (hiff E).1 ⟨fun _ _ hab => (cancel_mono (adj.homEquiv A B g)).1 hab, fun b => ?_⟩
    exact ⟨b ≫ inv (adj.homEquiv A B g), by simp⟩

end CategoryTheory.Adjunction

namespace Stacks.Cohomology.SiteModules

universe u v r w t

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {O : Sheaf J CommRingCat.{r}}
  [HasWeakSheafify J AddCommGrpCat.{max u r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r w}]
  [Abelian (SheafOfModules.{max u r w} (ringSheafOfSite O))]
  {R : Type t} [CommRing R]

/-- **The subcategory `D_QCoh(𝒪_X)` of Stacks 071X on an abstract site**: the objects of the
unbounded derived category of `O`-modules whose cohomology sheaves are all quasi-coherent.  It is
`DerivedCategoryB.derivedCategoryB` applied to quasi-coherence on the site, and it is the
property that the right-hand side of
`Stacks.Cohomology.SiteModules.isIso_homEquiv_baseRingTensorLimitComparison_iff` quantifies
over. -/
abbrev quasicoherentDerivedOnSite (O : Sheaf J CommRingCat.{r})
    [Abelian (SheafOfModules.{max u r w} (ringSheafOfSite O))] :
    ObjectProperty (DerivedCategory (SheafOfModules.{max u r w} (ringSheafOfSite O))) :=
  DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherentOnSite.{u, v, r, max u r w} (ringSheafOfSite O))

variable (φ : R →+* GlobalFunctionRing O)
  (Msys : ℕᵒᵖ ⥤ ModuleCat.{max u r w} R) (c : Cone Msys)
  (d : Cone (Msys ⋙ baseRingTensorFunctor φ)) (hd : IsLimit d)

/-- **The two readings of the headline of Stacks 0D3F agree.**  Let `DQ_X` be a right adjoint of
the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` — on the small étale site of a quasi-compact
quasi-separated algebraic space one exists by Stacks 0CR4,
`AlgebraicGeometry.Space.quasicoherentDerivedInclusion_isLeftAdjoint`, and on a general site it
is the hypothesis `adj` — and suppose the source `𝒪_X ⊗_R (lim M_n)` of the canonical map of
Stacks 0D3F lies in `D_QCoh(𝒪_X)`.  Then:

the canonical map `𝒪_X ⊗_R (lim M_n) ⟶ lim (𝒪_X ⊗_R M_n)` induces an isomorphism from its source
onto `DQ_X` applied to its target **if and only if** composition with it is bijective on
morphisms out of every object of `D_QCoh(𝒪_X)`.

This is the source's own rereading of its headline.  **Neither side is proved**: the statement is
an equivalence of the two framings, and its proof is
`CategoryTheory.Adjunction.bijective_comp_map_iff_isIso_homEquiv`, that is the adjunction alone.
No properness, flatness or finite-presentation hypothesis appears, and the transition maps of
`(M_n)` are not assumed surjective, because the equivalence needs none of them. -/
@[stacks 0D3F "the source's rereading of the headline, proved as an equivalence: the canonical \
map induces an isomorphism from its source onto DQ_X of its target iff composition with it is \
bijective on morphisms out of every object of D_QCoh(𝒪_X). Neither side is proved; the \
bijectivity asserted by the headline under properness, flatness and finite presentation is NOT \
proved here, and is not assumed. The existence of DQ_X is a named hypothesis, which is Stacks \
0CR4 on the small étale site of a quasi-compact quasi-separated algebraic space"]
theorem isIso_homEquiv_baseRingTensorLimitComparison_iff
    {DQ : DerivedCategory (SheafOfModules.{max u r w} (ringSheafOfSite O)) ⥤
      (quasicoherentDerivedOnSite.{u, v, r, w} O).FullSubcategory}
    (adj : (quasicoherentDerivedOnSite.{u, v, r, w} O).ι ⊣ DQ)
    (hsrc : quasicoherentDerivedOnSite.{u, v, r, w} O
      ((DerivedCategory.singleFunctor _ 0).obj ((baseRingTensorFunctor φ).obj c.pt))) :
    IsIso (adj.homEquiv ⟨_, hsrc⟩ ((DerivedCategory.singleFunctor _ 0).obj d.pt)
        ((DerivedCategory.singleFunctor _ 0).map
          (baseRingTensorLimitComparison φ Msys c d hd))) ↔
      ∀ E : (quasicoherentDerivedOnSite.{u, v, r, w} O).FullSubcategory,
        Function.Bijective
          (fun a : E.obj ⟶
              (DerivedCategory.singleFunctor _ 0).obj ((baseRingTensorFunctor φ).obj c.pt) =>
            a ≫ (DerivedCategory.singleFunctor _ 0).map
              (baseRingTensorLimitComparison φ Msys c d hd)) :=
  (CategoryTheory.Adjunction.bijective_comp_map_iff_isIso_homEquiv adj ⟨_, hsrc⟩ _ _).symm

end Stacks.Cohomology.SiteModules

end
