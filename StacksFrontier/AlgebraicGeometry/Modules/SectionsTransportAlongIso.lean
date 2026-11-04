module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.ModelComparison

/-!
# Global sections transported along a morphism of schemes

A sheaf of modules `F` on `Z` and a sheaf of modules `G` on `Y` live over different rings of
functions, so an identification of their global sections cannot be an isomorphism of
`Γ(Z, ⊤)`-modules on the nose: the two sides are modules over `Γ(Z, ⊤)` and over `Γ(Y, ⊤)`.
What makes them comparable is a morphism `f : Y ⟶ Z` together with an identification of `F` with
the direct image `f_* G`. Then

* `Γ(Z, f_* G)` **is** `Γ(Y, G)` with scalars restricted along `f` on global sections — the two
  functors `Y.Modules ⥤ ModuleCat Γ(Z, ⊤)` are equal, not merely isomorphic, because
  `f ⁻¹ᵁ ⊤ = ⊤` definitionally (`AlgebraicGeometry.pushforward_comp_evaluation_top`);
* so the identification `F ≅ f_* G`, read on sections over `⊤`, is the comparison wanted.

No hypothesis on `f` is needed for this. The case the development actually meets is the one where
`f` is an isomorphism of schemes `d : Y ≅ Z` and the identification is given on the *inverse*
image, as `d^* F ≅ G`: a model `Y` of a scheme `Z` carrying an understood module, and a module on
the model identified with the inverse image. The transpose `F ≅ d_* G` of such an identification
is `AlgebraicGeometry.Scheme.Modules.pushforwardIsoOfPullbackIso`, and the comparison of sections
follows.

Both forms are also given over a base: for a commutative ring `A` and structure morphisms
`g : Z ⟶ Spec A` and `h : Y ⟶ Spec A` with `f ≫ g = h`, the comparison is an isomorphism of
`A`-modules, `AlgebraicGeometry.globalSectionsOver` being `A`-linear global sections. This is the
form a ring-level statement about sections consumes, and the commuting triangle is taken as an
argument rather than derived so that the consumer supplies its own compatibility and no transport
along an equality of morphisms is left behind.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pushforwardIsoOfPullbackIso`: the transpose `F ≅ d_* G` of an
  identification `d^* F ≅ G` along an isomorphism of schemes `d`.
* `AlgebraicGeometry.Scheme.Modules.pushforwardSectionsTopIso`: **the comparison.** For
  `f : Y ⟶ Z` and `F ≅ f_* G`, the global sections of `F` are the global sections of `G` with
  scalars restricted along `f`.
* `AlgebraicGeometry.Scheme.Modules.pullbackSectionsTopIso`: the same for an isomorphism of
  schemes `d : Y ≅ Z` and an identification `d^* F ≅ G`.
* `AlgebraicGeometry.Scheme.Modules.pullbackSectionsTopLinearEquiv`: that comparison as a
  `Γ(Z, ⊤)`-linear equivalence `Γ(F, ⊤) ≃ₗ Γ(G, ⊤)`, the action on the target being the one
  through `d` on global sections.
* `AlgebraicGeometry.globalSectionsOverPushforwardNatIso`: the comparison over a base `Spec A`,
  before any identification of modules is given — the `A`-linear global sections of a direct
  image along a morphism over `A`, as a natural isomorphism of functors `Y.Modules ⥤ ModuleCat A`.
* `AlgebraicGeometry.globalSectionsOverPushforwardIso` and
  `AlgebraicGeometry.globalSectionsOverPullbackIso`: both comparisons over a base, as
  isomorphisms of `A`-modules.

## Implementation notes

`AlgebraicGeometry.pushforward_comp_evaluation_top` is an equality of functors proved by `rfl`,
so `AlgebraicGeometry.Scheme.Modules.pushforwardSectionsTopIso` is the image of the given
isomorphism under evaluation over `⊤` and nothing else; the restriction of scalars in its
statement is supplied by that equality and costs no comparison map. Over a base one further
coherence is needed, the composite of two restrictions of scalars against the restriction along
the composite, and that is Mathlib's `ModuleCat.restrictScalarsComp'App`. The route is the
degree-zero reading of `AlgebraicGeometry.cohomologyOverFieldPushforwardIso`, which does the same
two steps after a right derived functor and over a field.

The base version is stated first as a natural isomorphism of functors and only then evaluated
against a given identification of modules; the commuting triangle `f ≫ g = h` is an argument
rather than a conclusion, so a consumer whose two structure morphisms are already related by a
lemma of its own supplies that lemma and is left with no transport along an equality of
morphisms.

`AlgebraicGeometry.Scheme.Modules.pullbackSectionsTopLinearEquiv` generalizes
`AlgebraicGeometry.sectionsPullbackIsoOfIsIso` — which is its case `G = d^* F`, with the
identification the identity, stated in the other direction — and
`AlgebraicGeometry.Scheme.Modules.sectionsTopLinearEquivOfIso`, which is the case of one fixed
scheme.

## What is not proved

Nothing here is about stalks. A comparison of sections over `⊤` says nothing about the sections
over a smaller open or about the germ at a point, because a direct image along a morphism that is
not an isomorphism does not commute with taking a stalk. The isomorphism-of-schemes case does
transport stalks, but through the map on points, and that comparison is not stated here.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

variable {Y Z : Scheme.{u}}

namespace Scheme.Modules

/-- **The transpose of an identification of an inverse image.** For an isomorphism of schemes
`d : Y ≅ Z`, a module `F` on `Z` and a module `G` on `Y`, an identification `d^* F ≅ G` of `G`
with the inverse image of `F` is the same thing as an identification `F ≅ d_* G` of `F` with the
direct image of `G`: the direct image of the inverse image along an isomorphism is the module
itself, by `Stacks.Cohomology.SchemeIso.pushforwardPullbackIso`. -/
def pushforwardIsoOfPullbackIso (d : Y ≅ Z) {F : Z.Modules} {G : Y.Modules}
    (e : (Scheme.Modules.pullback d.hom).obj F ≅ G) :
    F ≅ (Scheme.Modules.pushforward d.hom).obj G :=
  (Stacks.Cohomology.SchemeIso.pushforwardPullbackIso d F).symm ≪≫
    (Scheme.Modules.pushforward d.hom).mapIso e

/-- **Global sections transported along a morphism of schemes.** Let `f : Y ⟶ Z` be a morphism of
schemes, `F` a module on `Z` and `G` a module on `Y`, and let `F ≅ f_* G` identify `F` with the
direct image of `G`. Then the global sections of `F` are the global sections of `G`, as modules
over `Γ(Z, ⊤)` acting on the latter through `f` on global sections.

The comparison is the given isomorphism read on sections over `⊤`. The restriction of scalars in
the statement is free: evaluation over `⊤` of a direct image **is** evaluation over `⊤` followed
by restriction of scalars, by `AlgebraicGeometry.pushforward_comp_evaluation_top`. -/
def pushforwardSectionsTopIso (f : Y ⟶ Z) {F : Z.Modules} {G : Y.Modules}
    (φ : F ≅ (Scheme.Modules.pushforward f).obj G) :
    (SheafOfModules.evaluation Z.ringCatSheaf (op (⊤ : Z.Opens))).obj F ≅
      (ModuleCat.restrictScalars f.appTop.hom).obj
        ((SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).obj G) :=
  (SheafOfModules.evaluation Z.ringCatSheaf (op (⊤ : Z.Opens))).mapIso φ

/-- **Global sections transported along an isomorphism of schemes and an isomorphism of
modules.** For `d : Y ≅ Z`, a module `F` on `Z` and a module `G` on `Y` identified with the
inverse image `d^* F`, the global sections of `F` are the global sections of `G`, over `Γ(Z, ⊤)`
acting through `d`. -/
def pullbackSectionsTopIso (d : Y ≅ Z) {F : Z.Modules} {G : Y.Modules}
    (e : (Scheme.Modules.pullback d.hom).obj F ≅ G) :
    (SheafOfModules.evaluation Z.ringCatSheaf (op (⊤ : Z.Opens))).obj F ≅
      (ModuleCat.restrictScalars d.hom.appTop.hom).obj
        ((SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).obj G) :=
  pushforwardSectionsTopIso d.hom (pushforwardIsoOfPullbackIso d e)

/-- `AlgebraicGeometry.Scheme.Modules.pullbackSectionsTopIso` as a linear equivalence of the
modules of sections themselves, `Γ(Z, ⊤)` acting on the sections of `G` through `d` on global
sections. -/
def pullbackSectionsTopLinearEquiv (d : Y ≅ Z) {F : Z.Modules} {G : Y.Modules}
    (e : (Scheme.Modules.pullback d.hom).obj F ≅ G) :
    letI : Module Γ(Z, ⊤) Γ(G, ⊤) := Module.compHom _ d.hom.appTop.hom
    Γ(F, ⊤) ≃ₗ[Γ(Z, ⊤)] Γ(G, ⊤) :=
  (pullbackSectionsTopIso d e).toLinearEquiv

end Scheme.Modules

/-- **`A`-linear global sections of a direct image.** Let `g : Z ⟶ Spec A` and `h : Y ⟶ Spec A`
be schemes over a commutative ring `A` and let `f : Y ⟶ Z` be a morphism over `A`, in the sense
that `f ≫ g = h`. Then the `A`-linear global sections of the direct image along `f` are the
`A`-linear global sections of the source: the two functors `Y.Modules ⥤ ModuleCat A` are
isomorphic.

Over `Γ(Z, ⊤)` instead of over `A` the corresponding statement is an *equality* of functors,
`AlgebraicGeometry.pushforward_comp_evaluation_top`. Cutting the scalars down to `A` leaves the
one coherence `ModuleCat.restrictScalarsComp'App` between restricting along `g` and then along
`f` and restricting along `h` in one step; on sections it is the identity, so the naturality
square is a definitional identity. -/
def globalSectionsOverPushforwardNatIso {A : Type u} [CommRing A] (f : Y ⟶ Z)
    (g : Z ⟶ Spec (.of A)) (h : Y ⟶ Spec (.of A)) (hfg : f ≫ g = h) :
    Scheme.Modules.pushforward f ⋙ globalSectionsOver g ≅ globalSectionsOver h :=
  NatIso.ofComponents
    (fun G => (ModuleCat.restrictScalarsComp'App
      ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom f.appTop.hom
      ((Scheme.ΓSpecIso (.of A)).inv ≫ h.appTop).hom
      (by
        rw [← CommRingCat.hom_comp]
        refine congrArg CommRingCat.Hom.hom ?_
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, hfg])
      ((SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).obj G)).symm)
    (fun _ => rfl)

/-- **`A`-linear global sections transported along a morphism of schemes over `A`.** Let
`g : Z ⟶ Spec A` and `h : Y ⟶ Spec A` be schemes over a commutative ring `A` and let `f : Y ⟶ Z`
be a morphism over `A`, in the sense that `f ≫ g = h`. An identification `F ≅ f_* G` of a module
`F` on `Z` with the direct image of a module `G` on `Y` identifies their `A`-linear global
sections.

This is the given identification read on `A`-linear global sections, followed by
`AlgebraicGeometry.globalSectionsOverPushforwardNatIso` at `G`. -/
def globalSectionsOverPushforwardIso {A : Type u} [CommRing A] (f : Y ⟶ Z)
    (g : Z ⟶ Spec (.of A)) (h : Y ⟶ Spec (.of A)) (hfg : f ≫ g = h)
    {F : Z.Modules} {G : Y.Modules} (φ : F ≅ (Scheme.Modules.pushforward f).obj G) :
    (globalSectionsOver g).obj F ≅ (globalSectionsOver h).obj G :=
  (globalSectionsOver g).mapIso φ ≪≫ (globalSectionsOverPushforwardNatIso f g h hfg).app G

/-- **`A`-linear global sections transported along an isomorphism of schemes over `A`.** For an
isomorphism `d : Y ≅ Z` over `Spec A`, a module `F` on `Z` and a module `G` on `Y` identified
with the inverse image `d^* F`, the `A`-linear global sections of `F` and of `G` agree.

This is the form in which a module on a *model* `Y` of `Z`, given as the inverse image of the
module that is understood on `Z`, has its sections read on `Z`. -/
def globalSectionsOverPullbackIso {A : Type u} [CommRing A] (d : Y ≅ Z)
    (g : Z ⟶ Spec (.of A)) (h : Y ⟶ Spec (.of A)) (hdg : d.hom ≫ g = h)
    {F : Z.Modules} {G : Y.Modules} (e : (Scheme.Modules.pullback d.hom).obj F ≅ G) :
    (globalSectionsOver g).obj F ≅ (globalSectionsOver h).obj G :=
  globalSectionsOverPushforwardIso d.hom g h hdg (Scheme.Modules.pushforwardIsoOfPullbackIso d e)

end AlgebraicGeometry

end
