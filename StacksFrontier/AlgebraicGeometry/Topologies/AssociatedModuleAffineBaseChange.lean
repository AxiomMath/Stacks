module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcOverSiteDichotomy

/-!
# The associated module of Tag 03DU is cartesian on affine objects

Let `S` be a scheme and `F` a quasi-coherent `𝒪_S`-module.  Tag 03DS attaches to `F` the
abelian presheaf `T ↦ Γ(T, T.hom⁺ F)` on the schemes over `S`, and Tag 03DU turns its
restriction along a site `C ⥤ Over S` into the *associated module* `Fᵃ` over the structure
sheaf of the site, whose sections over an object are the global sections of the pullback of `F`
to the underlying scheme (`Stacks.Sites.associatedPresheaf`,
`Stacks.Sites.siteAssociatedModule`).  The restriction map of `Fᵃ` along a morphism of the site
is `AlgebraicGeometry.pullbackSectionsMap`, semilinear over the restriction map of global
functions by `AlgebraicGeometry.pullbackSectionsMap_smul`.

This file proves that *between affine objects that restriction map is a base change*: for a
morphism `g : X ⟶ Y` of schemes over `S` whose two underlying schemes are affine,

`Γ(X.left, 𝒪) ⊗_{Γ(Y.left, 𝒪)} Fᵃ(Y) ≅ Fᵃ(X)`,

normalised by sending `1 ⊗ m` to the restriction of `m`.  This is the base change clause of
Descent, Proposition 03DX(2) for a module *in the image of* `(-)ᵃ`, and it is the one clause of
Tag 03DX that needs no descent: it is Tag 02KH in degree zero between two affine schemes, which
is `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`.  What is *not* proved here — and
what the rest of Tag 03DX is — is that every quasi-coherent module on the site is isomorphic to
some `Fᵃ`; see the implementation notes.

## Main definitions

* `Stacks.Sites.pullbackSectionsComparison` is the canonical isomorphism
  `g.left⁺ (Y.hom⁺ F) ≅ X.hom⁺ F` of modules on the scheme underlying `X`, assembled from the
  composition and congruence isomorphisms of the pullback pseudofunctor.
* `Stacks.Sites.affineAssociatedBaseChangeIso` is the base change isomorphism
  `Γ(X.left, 𝒪) ⊗_{Γ(Y.left, 𝒪)} Γ(Y.hom⁺ F, ⊤) ≅ Γ(X.hom⁺ F, ⊤)` for `X.left` and `Y.left`
  affine, in the `CategoryTheory.ModuleCat.extendScalars` form.

## Main results

* `Stacks.Sites.pullbackSectionsMap_eq_comp`: the restriction map of the associated presheaf is
  the unit of `g.left⁺ ⊣ (g.left)_*` on global sections followed by
  `Stacks.Sites.pullbackSectionsComparison` on global sections.
* `Stacks.Sites.pullbackSectionsComparison_pullbackSection`: the same identification as an
  equation between sections.
* `Stacks.Sites.affineAssociatedBaseChangeIso_hom_one_tmul`: **the normalisation.**  The base
  change isomorphism sends `1 ⊗ m` to `AlgebraicGeometry.pullbackSectionsMap F g m`.
* `Stacks.Sites.bijective_affineAssociatedBaseChangeIso_hom`: it is bijective on sections.

## Implementation notes

The ring map the base change is taken along is `g.left.appLE ⊤ ⊤ h`, with
`h : ⊤ ≤ g.left ⁻¹ᵁ ⊤` an explicit argument, rather than
`AlgebraicGeometry.Scheme.Hom.appTop`.  The two are *equal* —
`AlgebraicGeometry.Scheme.Hom.appLE_eq_app` proves `g.left.appLE ⊤ ⊤ h = g.left.appTop`, the
two opens being definitionally equal — but not definitionally equal, because `appLE` carries an
application of `CategoryTheory.Functor.map` to an identity morphism which only
`CategoryTheory.Functor.map_id` removes.  Stating the isomorphism at `appLE` is what lets it be
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` composed with an isomorphism and no
transport along that equation; a consumer wanting the `appTop` form transports once.

The statements are in the `ModuleCat.extendScalars` form of
`affinePullbackSectionsBaseChangeIso` and not in the bare `TensorProduct` form of
`AlgebraicGeometry.Space.sectionsBaseChange`.  The two carriers are definitionally equal: the
`Module Γ(Y.left, 𝒪) Γ(X.left, 𝒪)` instance that `CategoryTheory.ModuleCat.restrictScalars`
produces is `Module.compHom`, which is the `Algebra.toModule` of `RingHom.toAlgebra` by `rfl`.
But the `Semiring Γ(X.left, 𝒪)` instance reached through `CommRingCat` and the one reached
through `CommRing.toCommSemiring` are different *terms*, so no rewrite crosses the boundary, and
the one defeq check that does cross it exhausts the default recursion depth at these concrete
sheaf-section types.  Translating to the bare form is therefore left to the consumer, which has
to pin its scalar structures anyway — exactly as
`Stacks.AlgebraicGeometry.SectionsBaseChange.isBaseChange_appTop_pullbackSections` does.

`AlgebraicGeometry.sectionsLinearEquivOfIso` is used to read
`Stacks.Sites.pullbackSectionsComparison` on sections, rather than
`CategoryTheory.SheafOfModules.evaluation`: the latter lands in modules over the `RingCat`-valued
`AlgebraicGeometry.Scheme.ringCatSheaf`, whose `Semiring` instance is not the one
`CategoryTheory.ModuleCat.of Γ(X.left, ⊤) _` carries, and composing the two isomorphisms then
forces exactly the defeq check described above.

No `@[stacks]` attribute is claimed.  Tag 03DX(2) is an equivalence of categories; what is here
is the base change clause of its object half, restricted to the image of `(-)ᵃ`.  Neither full
faithfulness (Tag 0GN7) nor essential surjectivity — which is where Tag 023T, effective descent
for quasi-coherent modules, enters — is proved.  Note that the source's proof of Tag 03DX cites
Tags 03DV, 0GN7, 023T, 03DL and 03EM, and does *not* cite Tag 03DW: the cohomology comparison of
Tag 03DW is a later proposition and is not an input to Tag 03DX.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped ChangeOfRings

universe u

namespace Stacks.Sites

variable {S : Scheme.{u}} (F : S.Modules) {X Y : Over S} (g : X ⟶ Y)

/-! ### The comparison isomorphism of the two pullbacks -/

/-- The canonical isomorphism `g.left⁺ (Y.hom⁺ F) ≅ X.hom⁺ F` of modules on the scheme
underlying `X`, for a morphism `g : X ⟶ Y` of schemes over `S`: the composition isomorphism of
the pullback pseudofunctor followed by the congruence isomorphism for the commuting triangle
`CategoryTheory.Over.w g`.

This is the isomorphism implicit in `AlgebraicGeometry.pullbackSectionsMap`, which is the unit
of `g.left⁺ ⊣ (g.left)_*` on global sections followed by it; see
`Stacks.Sites.pullbackSectionsMap_eq_comp`. -/
noncomputable def pullbackSectionsComparison :
    (Scheme.Modules.pullback g.left).obj ((Scheme.Modules.pullback Y.hom).obj F) ≅
      (Scheme.Modules.pullback X.hom).obj F :=
  (Scheme.Modules.pullbackComp g.left Y.hom).app F ≪≫
    (Scheme.Modules.pullbackCongr (Over.w g)).app F

/-- **The restriction map of Tag 03DU, factored.**  The pullback map on global sections of
Tag 03DS is the unit of `g.left⁺ ⊣ (g.left)_*` on global sections, followed by
`Stacks.Sites.pullbackSectionsComparison` on global sections. -/
theorem pullbackSectionsMap_eq_comp :
    pullbackSectionsMap F g =
      (((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
          ((Scheme.Modules.pullback Y.hom).obj F)).app ⊤) ≫
        (pullbackSectionsComparison F g).hom.app ⊤ := by
  rw [pullbackSectionsMap_eq_topUnitMap, topUnitMap, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app]
  rfl

/-- **The restriction map of Tag 03DU is the pulling back of a section.**  Reading
`Stacks.Sites.pullbackSectionsComparison` on global sections and applying it to the pullback of
a global section along `g.left` gives the restriction map of the associated presheaf. -/
theorem pullbackSectionsComparison_pullbackSection
    (h : (⊤ : X.left.Opens) ≤ g.left ⁻¹ᵁ (⊤ : Y.left.Opens))
    (m : Γ((Scheme.Modules.pullback Y.hom).obj F, ⊤)) :
    sectionsLinearEquivOfIso (pullbackSectionsComparison F g) ⊤
        (Scheme.Modules.pullbackSection g.left
          ((Scheme.Modules.pullback Y.hom).obj F) ⊤ ⊤ h m) =
      pullbackSectionsMap F g m :=
  have hk := congrArg (fun φ => (ConcreteCategory.hom φ) m) (pullbackSectionsMap_eq_comp F g)
  (congrArg (ConcreteCategory.hom ((pullbackSectionsComparison F g).hom.app ⊤))
    (Scheme.Modules.pullbackSection_top g.left ((Scheme.Modules.pullback Y.hom).obj F) h m)).trans
    hk.symm

/-! ### The base change isomorphism between affine objects -/

variable [F.IsQuasicoherent] [IsAffine X.left] [IsAffine Y.left]

/-- **The associated module of Tag 03DU is cartesian on affine objects.**  For a morphism
`g : X ⟶ Y` of schemes over `S` whose two underlying schemes are affine, and `F` a
quasi-coherent `𝒪_S`-module, the sections of `Fᵃ` over `X` are the base change along `g.left`
of its sections over `Y`:

`Γ(X.left, 𝒪) ⊗_{Γ(Y.left, 𝒪)} Γ(Y.hom⁺ F, ⊤) ≅ Γ(X.hom⁺ F, ⊤)`.

This is the base change clause of Descent, Proposition 03DX(2) for a module in the image of
`(-)ᵃ`.  Its normalisation is
`Stacks.Sites.affineAssociatedBaseChangeIso_hom_one_tmul`. -/
noncomputable def affineAssociatedBaseChangeIso
    (h : (⊤ : X.left.Opens) ≤ g.left ⁻¹ᵁ (⊤ : Y.left.Opens)) :
    (ModuleCat.extendScalars (g.left.appLE ⊤ ⊤ h).hom).obj
        (ModuleCat.of Γ(Y.left, ⊤) Γ((Scheme.Modules.pullback Y.hom).obj F, ⊤)) ≅
      ModuleCat.of Γ(X.left, ⊤) Γ((Scheme.Modules.pullback X.hom).obj F, ⊤) :=
  affinePullbackSectionsBaseChangeIso g.left ((Scheme.Modules.pullback Y.hom).obj F)
      (isAffineOpen_top Y.left) (isAffineOpen_top X.left) h ≪≫
    (sectionsLinearEquivOfIso (pullbackSectionsComparison F g) ⊤).toModuleIso

/-- `Stacks.Sites.affineAssociatedBaseChangeIso` is the affine base change isomorphism of
Tag 02KH in degree zero followed by `Stacks.Sites.pullbackSectionsComparison` on sections. -/
theorem affineAssociatedBaseChangeIso_hom
    (h : (⊤ : X.left.Opens) ≤ g.left ⁻¹ᵁ (⊤ : Y.left.Opens)) :
    (affineAssociatedBaseChangeIso F g h).hom =
      (affinePullbackSectionsBaseChangeIso g.left ((Scheme.Modules.pullback Y.hom).obj F)
          (isAffineOpen_top Y.left) (isAffineOpen_top X.left) h).hom ≫
        (sectionsLinearEquivOfIso (pullbackSectionsComparison F g) ⊤).toModuleIso.hom := rfl

/-- **The normalisation.**  `Stacks.Sites.affineAssociatedBaseChangeIso` sends `1 ⊗ m` to the
restriction map of the associated presheaf of Tag 03DU applied to `m`. -/
theorem affineAssociatedBaseChangeIso_hom_one_tmul
    (h : (⊤ : X.left.Opens) ≤ g.left ⁻¹ᵁ (⊤ : Y.left.Opens))
    (m : Γ((Scheme.Modules.pullback Y.hom).obj F, ⊤)) :
    (affineAssociatedBaseChangeIso F g h).hom
        ((1 : Γ(X.left, ⊤)) ⊗ₜ[Γ(Y.left, ⊤), (g.left.appLE ⊤ ⊤ h).hom] m) =
      pullbackSectionsMap F g m := by
  rw [affineAssociatedBaseChangeIso_hom]
  refine (CategoryTheory.comp_apply _ _ _).trans ?_
  rw [affinePullbackSectionsBaseChangeIso_one_tmul]
  exact pullbackSectionsComparison_pullbackSection F g h m

/-- **The comparison is bijective on sections.**  Every section of `Fᵃ` over an affine object
`X` comes from the base change of the sections over an affine object `Y` above it, and the
element of the base change producing it is unique. -/
theorem bijective_affineAssociatedBaseChangeIso_hom
    (h : (⊤ : X.left.Opens) ≤ g.left ⁻¹ᵁ (⊤ : Y.left.Opens)) :
    Function.Bijective (affineAssociatedBaseChangeIso F g h).hom :=
  ConcreteCategory.bijective_of_isIso _

end Stacks.Sites

end
