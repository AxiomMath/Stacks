module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Restriction
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.BaseDegreeSheaf
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree

/-!
# Restriction and base change of the canonical map `(𝒪_S[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)`

Let `S` be a scheme, let `f : ℙⁿ_S ⟶ S` be the structure morphism of projective `n`-space and let
`d` be an integer.
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.toPushforwardTwistOver` is the
canonical morphism of `𝒪_S`-modules

`(𝒪_S[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)`,

the basis vector of a degree-`d` monomial going to the global section of `𝒪(d)` that the monomial
defines. The degree-zero row of the display of [Stacks, Tag 01XW] asserts that it is an
isomorphism, and that assertion is local on `S`: it suffices to invert the morphism over the
affine opens of a basis, and over an affine open it is a statement about a polynomial ring. This
file supplies what that localisation argument consumes, namely the behaviour of the morphism under
restriction to an open of `S` and under a base change `S' ⟶ S`.

The names below are relative to the `Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage`
namespace.

## Main definitions

* `monomialBasisHom` and `twistOverSectionHom`: the inclusion `𝒪_S ⟶ (𝒪_S[T₀, …, Tₙ])_d` of the
  copy of the structure sheaf indexed by a degree-`d` multidegree, and the morphism
  `𝒪_{ℙⁿ_S} ⟶ 𝒪(d)` attached to the global section `T^e`.
* `restrictGlobalSection`: the restriction of a global section of a module to an open subscheme.
* `restrictBaseDegreeSheafIso` and `toPushforwardRestrictTwistOver`: the restriction to an open
  `V ≤ S` of `(𝒪_S[T₀, …, Tₙ])_d`, and the canonical morphism over `V` built from the restrictions
  to `f⁻¹V` of the global sections `T^e`.
* `pullbackBaseDegreeSheafIso`: **`(𝒪_S[T₀, …, Tₙ])_d` is stable under base change**, the
  companion of `twistOverPullbackIso`, which says the same of `𝒪(d)`.
* `twistOverPushforwardHom` and `baseDegreeSheafPushforwardHom`: those two base-change
  isomorphisms transposed, i.e. the maps restricting sections along `ℙⁿ_{S'} ⟶ ℙⁿ_S` and along
  `S' ⟶ S`.

## Main results

* `monomialBasisHom_comp_toPushforwardTwistOver`: **the canonical morphism on the `e`-th summand
  of the free sheaf** is the direct image along `f` of the morphism attached to `T^e`. Every
  statement below is proved from this one, a morphism out of a free sheaf being determined by its
  restrictions to the summands.
* `toPushforwardTwistOver_app_monomialBasisHom_app`: **the canonical morphism on sections over an
  open `W` of the base**: the tautological section of the `e`-th summand scaled by a regular
  function `r` goes to `r` times the restriction of `T^e` to `f⁻¹W`. Over a quasi-compact open
  this describes the morphism completely, by `Stacks.Sites.bijective_freeSectionsMap`.
* `restrict_toPushforwardTwistOver`: **restriction to an open `V ≤ S`.** Restricted to `V` and
  read through `Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`, the canonical
  morphism is the canonical morphism over `V` built from the restricted sections.
* `twistOverPullbackIso_hom_app_twistOverSection` and `pullback_map_twistOverSectionHom`: **the
  global section `T^e` of `𝒪(d)` is stable under base change.**
* `toPushforwardTwistOver_baseChange`: **base change for the canonical morphism.** Its pullback
  along `g : S' ⟶ S`, followed by the base-change morphism `g^* f_* ⟶ f'_* p^*` of
  [Stacks, Tag 02KG] and the base-change isomorphism of the twists, is the canonical morphism for
  `S'`. `toPushforwardTwistOver_pushforwardSquare` is the same statement transposed, with no
  inverse images in it.

## Implementation notes

**Everything is reduced to the summands of the free sheaf.** A morphism out of
`CategoryTheory.SheafOfModules.free I` is determined by the family of its restrictions to the
copies of the structure sheaf, and `monomialBasisHom_comp_toPushforwardTwistOver` identifies
those restrictions for the canonical morphism. Each of the two squares is therefore proved by
transposing it, when necessary, so that it becomes a square of morphisms out of
`(𝒪_S[T₀, …, Tₙ])_d`, and then checking it on the summands, where only morphisms out of the
structure sheaf remain. On those, base change for the morphism is base change for the global
section `T^e` (the content of `pullback_map_twistOverSectionHom`) together with the compatibility
of the structure-sheaf maps with the base-change square
(`unitToPushforwardUnit_pushforwardSquareIso`); restriction to an open is restriction of `T^e`
(`restrict_twistOverSectionHom`) together with the restriction square for the structure-sheaf map
(`restrictUnitToPushforwardUnitSquare`).

**The base-change square is read through the mate.** The base-change morphism
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` is defined as a mate, and
`CategoryTheory.unit_mateEquiv_symm` turns the statement about it into the statement about the
identification of the two composite direct images around the square, which is where the
structure-sheaf computation happens.

**Two spellings of the structure sheaf as a module over itself.** The library carries both
`AlgebraicGeometry.Scheme.unitModule` and `Stacks.IdealSheafRestrict.unitModule`, definitionally
equal but distinct, and the identifications used here are stated at different ones:
`AlgebraicGeometry.Scheme.Modules.unitToPushforwardUnit` and
`AlgebraicGeometry.Scheme.Modules.unitHomEquivTop` at the former,
`Stacks.Conormal.Restriction.restrictStructureMapRestrictSquare` at the latter, and Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso` at neither — its type names the structure
sheaf as `CategoryTheory.SheafOfModules.unit`, whose type is not syntactically `S.Modules`.
Rewriting cannot cross those gaps: the type-correctness check of `rw` works at a transparency
that unfolds none of them. `restrictUnitModuleIso` and `restrictUnitToPushforwardUnitSquare`
below therefore name the restriction isomorphism and the restriction square at the
`Scheme.unitModule` spelling used throughout this file, each by a term-level identity with the
existing declaration. They add no mathematics, and the name `restrictStructureMapSquare` is
avoided because `Stacks.IdealSheafRestrict.restrictStructureMapSquare` is a different square:
there the source of the morphism is left whole, here it is cut down to `f⁻¹V`.

**Restriction versus base change at an open immersion.** Taking `g = V.ι` for an open `V ≤ S` in
`toPushforwardTwistOver_baseChange` compares the canonical morphism for `S` with the canonical
morphism for the scheme `V`, since `ℙⁿ_V` is the fibre product
(`isPullback_projectiveSpaceOverMap`) and so maps isomorphically to `f⁻¹V`;
`restrict_toPushforwardTwistOver` compares it instead with the morphism over `V` whose target is
the direct image of `𝒪(d)|_{f⁻¹V}` along `f ∣_ V`, with no cartesian square needed.

**What is not proved here.** Nothing is claimed about `toPushforwardTwistOver` being an
isomorphism and no `stacks` attribute is attached: the degree-zero row of [Stacks, Tag 01XW] is
that assertion, and these are among its prerequisites.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.AffinePushforward
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-! ### Morphisms out of a free sheaf given by global sections of a direct image -/

/-- The morphism out of the structure sheaf attached to a section acts on sections over an open
set by multiplication with that section. -/
theorem unitHomEquiv_symm_app {X : Scheme.{u}} (M : X.Modules) (s : M.sections) (U : X.Opens)
    (r : Γ(X, U)) :
    Scheme.Modules.Hom.app
        ((SheafOfModules.unitHomEquiv M).symm s : Scheme.unitModule X ⟶ M) U r =
      (M.smul r).hom (s.val (op U)) :=
  rfl

/-- The morphism out of the structure sheaf attached to a global section acts on sections over an
open set by multiplication with the restriction of that global section. -/
theorem unitHomEquivTop_app {X : Scheme.{u}} (M : X.Modules) (x : Γ(M, ⊤)) (U : X.Opens)
    (r : Γ(X, U)) :
    (Scheme.Modules.unitHomEquivTop M x).app U r =
      (M.smul r).hom (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op x) :=
  (unitHomEquiv_symm_app M (Scheme.Modules.sectionsTopEquiv M x) U r).trans
    (congrArg (M.smul r).hom (Scheme.Modules.sectionsTopEquiv_val M x (op U)))

/-- **A morphism out of a free sheaf prescribed by global sections of a direct image, read on
the `i`-th summand.** The morphism `free I ⟶ p_* M` whose `i`-th section is the direct image of
the global section `s i` of `M` restricts on the `i`-th copy of the structure sheaf to the
direct image along `p` of the morphism `𝒪_X ⟶ M` named by `s i`. -/
theorem ιFree_comp_freeHomEquiv_symm_pushforwardSections {X Y : Scheme.{u}} (p : X ⟶ Y)
    {I : Type u} (M : X.Modules) (s : I → Γ(M, ⊤)) (i : I) :
    (SheafOfModules.ιFree i :
          Scheme.unitModule Y ⟶ (SheafOfModules.free (R := Y.ringCatSheaf) I : Y.Modules)) ≫
        (SheafOfModules.freeHomEquiv _).symm (fun j ↦ SheafOfModules.pushforwardSections
          p.toRingCatSheafHom (Scheme.Modules.sectionsTopEquiv M (s j))) =
      Scheme.Modules.unitToPushforwardUnit p ≫
        (Scheme.Modules.pushforward p).map (Scheme.Modules.unitHomEquivTop M (s i)) := by
  apply (SheafOfModules.unitHomEquiv _).injective
  refine (congrFun (Equiv.apply_symm_apply (SheafOfModules.freeHomEquiv
    ((Scheme.Modules.pushforward p).obj M)) _) i).trans ?_
  refine Eq.trans ?_ (SheafOfModules.pushforwardSections_unitHomEquiv p.toRingCatSheafHom
    (Scheme.Modules.unitHomEquivTop M (s i)))
  exact congrArg (SheafOfModules.pushforwardSections _)
    (Scheme.Modules.unitHomEquiv_unitHomEquivTop M (s i)).symm

/-! ### The canonical map on the basis vectors -/

/-- The inclusion of the `e`-th copy of `𝒪_S` into `(𝒪_S[T₀, …, Tₙ])_d`, the basis vector of
the monomial `T^e`. This is `CategoryTheory.SheafOfModules.ιFree` at the type `S.Modules`. -/
def monomialBasisHom (n : ℕ) (S : Scheme.{u}) (d : ℤ) (e : MonomialIndex.{u} n d) :
    Scheme.unitModule S ⟶ baseDegreeSheaf n S d :=
  SheafOfModules.ιFree e

/-- The morphism `𝒪_X ⟶ 𝒪(d)` on `ℙⁿ_S` attached to the global section `T^e`. -/
def twistOverSectionHom (n : ℕ) (S : Scheme.{u}) (d : ℤ) (e : MonomialIndex.{u} n d) :
    Scheme.unitModule (projectiveSpaceOver n S) ⟶ twistOver n S d :=
  Scheme.Modules.unitHomEquivTop (twistOver n S d) (twistOverSection n S d e)

/-- **The canonical morphism `(𝒪_S[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)`, read on the `e`-th summand of
the free sheaf.** Precomposed with the inclusion of the `e`-th copy of `𝒪_S`, it is the direct
image along `f` of the morphism `𝒪_X ⟶ 𝒪(d)` named by `T^e`. -/
theorem monomialBasisHom_comp_toPushforwardTwistOver (n : ℕ) (S : Scheme.{u}) (d : ℤ)
    (e : MonomialIndex.{u} n d) :
    monomialBasisHom n S d e ≫ toPushforwardTwistOver n S d =
      Scheme.Modules.unitToPushforwardUnit (projectiveSpaceOver n S ↘ S) ≫
        (Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).map
          (twistOverSectionHom n S d e) :=
  ιFree_comp_freeHomEquiv_symm_pushforwardSections (projectiveSpaceOver n S ↘ S)
    (twistOver n S d) (twistOverSection n S d) e

/-- Two morphisms out of `(𝒪_S[T₀, …, Tₙ])_d` agreeing on every summand are equal. -/
private theorem hom_ext_of_monomialBasisHom_comp {n : ℕ} {S : Scheme.{u}} {d : ℤ}
    {M : S.Modules} {a b : baseDegreeSheaf n S d ⟶ M}
    (h : ∀ e, monomialBasisHom n S d e ≫ a = monomialBasisHom n S d e ≫ b) : a = b :=
  (SheafOfModules.freeHomEquiv _).injective
    (funext fun e ↦ congrArg (SheafOfModules.unitHomEquiv _) (h e))

/-- **The canonical morphism `(𝒪_S[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)` on sections over an open set.**
On the tautological section of the `e`-th summand of the free sheaf scaled by a regular function
`r` on an open `W` of the base, it is `r` times the restriction of the global section `T^e` of
`𝒪(d)` to `f⁻¹W`.

Over a quasi-compact open — in particular over an affine open — every section of the free sheaf
is a finite sum of such, by `Stacks.Sites.bijective_freeSectionsMap`, whose comparison map is
`Stacks.Sites.freeSectionsMap` and sends `Finsupp.single e r` to the section appearing here. -/
theorem toPushforwardTwistOver_app_monomialBasisHom_app (n : ℕ) (S : Scheme.{u}) (d : ℤ)
    (W : S.Opens) (e : MonomialIndex.{u} n d) (r : Γ(S, W)) :
    (toPushforwardTwistOver n S d).app W ((monomialBasisHom n S d e).app W r) =
      ((twistOver n S d).smul ((projectiveSpaceOver n S ↘ S).app W r)).hom
        ((twistOver n S d).presheaf.map
          (homOfLE (le_top : (projectiveSpaceOver n S ↘ S) ⁻¹ᵁ W ≤ ⊤)).op
          (twistOverSection n S d e)) :=
  (congrArg (fun k : Scheme.unitModule S ⟶
      (Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).obj (twistOver n S d) ↦
        k.app W r) (monomialBasisHom_comp_toPushforwardTwistOver n S d e)).trans
    (unitHomEquivTop_app (twistOver n S d) (twistOverSection n S d e) _
      ((projectiveSpaceOver n S ↘ S).app W r))

/-! ### Restriction to an open of the base -/

section Restriction

/-- Restriction along an open immersion carries the structure sheaf to the structure sheaf.
This names `AlgebraicGeometry.Scheme.Modules.restrictUnitIso` at the type
`AlgebraicGeometry.Scheme.unitModule`, as `Stacks.IdealSheafRestrict.restrictUnitModuleIso`
names it at the type `Stacks.IdealSheafRestrict.unitModule`; no mathematics is added, and the
reason the ascription is needed is in this file's module docstring. -/
def restrictUnitModuleIso {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctor j).obj (Scheme.unitModule Y) ≅ Scheme.unitModule X :=
  Scheme.Modules.restrictUnitIso j

/-- The restriction to an open subscheme of a global section of a module. -/
def restrictGlobalSection {X : Scheme.{u}} (U : X.Opens) (M : X.Modules) (x : Γ(M, ⊤)) :
    Γ((Scheme.Modules.restrictFunctor U.ι).obj M, ⊤) :=
  (Scheme.Modules.restrictAppIso U.ι M ⊤).inv
    (M.presheaf.map (homOfLE (le_top : (U.ι ''ᵁ ⊤) ≤ ⊤)).op x)

/-- A global section restricted to an open subscheme and then to a smaller open is the
restriction of the global section to that smaller open. -/
theorem presheaf_map_restrictGlobalSection {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (x : Γ(M, ⊤)) (W : U.toScheme.Opens) :
    ((Scheme.Modules.restrictFunctor U.ι).obj M).presheaf.map
        (homOfLE (le_top : W ≤ ⊤)).op (restrictGlobalSection U M x) =
      M.presheaf.map (homOfLE (le_top : (U.ι ''ᵁ W) ≤ ⊤)).op x := by
  refine (Scheme.Modules.presheaf_map_comp_apply M
    (homOfLE (le_top : (U.ι ''ᵁ ⊤) ≤ ⊤)).op
    (U.ι.opensFunctor.map (homOfLE (le_top : W ≤ ⊤))).op x).trans ?_
  exact congrArg (fun k ↦ M.presheaf.map k x) (Subsingleton.elim _ _)

/-- **The morphism out of the structure sheaf attached to a global section restricts to the
morphism attached to the restricted section.** -/
theorem restrict_unitHomEquivTop {X : Scheme.{u}} (U : X.Opens) (M : X.Modules) (x : Γ(M, ⊤)) :
    (Scheme.Modules.restrictFunctor U.ι).map (Scheme.Modules.unitHomEquivTop M x) =
      (restrictUnitModuleIso U.ι).hom ≫
        Scheme.Modules.unitHomEquivTop ((Scheme.Modules.restrictFunctor U.ι).obj M)
          (restrictGlobalSection U M x) := by
  ext W r
  refine (unitHomEquivTop_app M x (U.ι ''ᵁ W) r).trans ?_
  refine Eq.trans ?_ (congrArg (fun z ↦ Scheme.Modules.Hom.app
      (Scheme.Modules.unitHomEquivTop ((Scheme.Modules.restrictFunctor U.ι).obj M)
        (restrictGlobalSection U M x)) W z)
    (Stacks.Conormal.Restriction.restrictUnitModuleIso_ι_hom_app U W r)).symm
  refine Eq.trans ?_ (unitHomEquivTop_app ((Scheme.Modules.restrictFunctor U.ι).obj M)
    (restrictGlobalSection U M x) W r).symm
  refine Eq.trans ?_ (congrArg (((Scheme.Modules.restrictFunctor U.ι).obj M).smul r).hom
    (presheaf_map_restrictGlobalSection U M x W)).symm
  have hsmul : ((Scheme.Modules.restrictFunctor U.ι).obj M).smul r =
      M.smul ((U.ι.appIso W).inv r) := rfl
  rw [hsmul, Scheme.Opens.ι_appIso]
  rfl

/-- **Restriction to an open `V` of the target of the structure-sheaf map of `f`**, with the
source cut down to `f⁻¹V`: it is the structure-sheaf map of `f ∣_ V`. This is
`Stacks.Conormal.Restriction.restrictStructureMapRestrictSquare`, named at the spelling
`AlgebraicGeometry.Scheme.Modules.unitToPushforwardUnit` of the structure-sheaf map. -/
theorem restrictUnitToPushforwardUnitSquare {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) :
    (Scheme.Modules.restrictFunctor V.ι).map (Scheme.Modules.unitToPushforwardUnit f) ≫
        (restrictPushforwardIso f V).hom.app (Scheme.unitModule X) ≫
        (Scheme.Modules.pushforward (f ∣_ V)).map
          (restrictUnitModuleIso (f ⁻¹ᵁ V).ι).hom =
      (restrictUnitModuleIso V.ι).hom ≫
        Scheme.Modules.unitToPushforwardUnit (f ∣_ V) :=
  Stacks.Conormal.Restriction.restrictStructureMapRestrictSquare f V

/-- **The degree-`d` sheaf on the base restricts to the degree-`d` sheaf on an open
subscheme**: restriction along an open immersion preserves free sheaves. -/
def restrictBaseDegreeSheafIso (n : ℕ) (S : Scheme.{u}) (d : ℤ) (V : S.Opens) :
    baseDegreeSheaf n V.toScheme d ≅
      (Scheme.Modules.restrictFunctor V.ι).obj (baseDegreeSheaf n S d) :=
  Stacks.Modules.freeRestrictIso V.ι (MonomialIndex.{u} n d)

/-- The inclusion of the `e`-th copy of `𝒪_V` into the restriction to `V` of
`(𝒪_S[T₀, …, Tₙ])_d`. -/
theorem monomialBasisHom_comp_restrictBaseDegreeSheafIso_hom (n : ℕ) (S : Scheme.{u}) (d : ℤ)
    (V : S.Opens) (e : MonomialIndex.{u} n d) :
    monomialBasisHom n V.toScheme d e ≫ (restrictBaseDegreeSheafIso n S d V).hom =
      (restrictUnitModuleIso V.ι).inv ≫
        (Scheme.Modules.restrictFunctor V.ι).map (monomialBasisHom n S d e) := by
  let F := Scheme.Modules.restrictFunctor V.ι
  let h : PreservesColimitsOfShape.{u, u} (Discrete (MonomialIndex.{u} n d)) F :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} F
  exact @SheafOfModules.ιFree_mapFreeIso_hom _ _ _ _ _ _ _ _ _ _ _ _ F
    (MonomialIndex.{u} n d) h (restrictUnitModuleIso V.ι).symm e

/-- **The canonical morphism `(𝒪_V[T₀, …, Tₙ])_d ⟶ (f ∣_ V)_* (𝒪(d)|_{f⁻¹V})`** built from the
restrictions to `f⁻¹V` of the global sections `T^e` of `𝒪(d)`. -/
def toPushforwardRestrictTwistOver (n : ℕ) (S : Scheme.{u}) (d : ℤ) (V : S.Opens) :
    baseDegreeSheaf n V.toScheme d ⟶
      (Scheme.Modules.pushforward ((projectiveSpaceOver n S ↘ S) ∣_ V)).obj
        ((Scheme.Modules.restrictFunctor ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V).ι).obj
          (twistOver n S d)) :=
  (SheafOfModules.freeHomEquiv _).symm fun e ↦
    SheafOfModules.pushforwardSections ((projectiveSpaceOver n S ↘ S) ∣_ V).toRingCatSheafHom
      (Scheme.Modules.sectionsTopEquiv _
        (restrictGlobalSection ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V) (twistOver n S d)
          (twistOverSection n S d e)))

/-- The canonical morphism over `V` on the `e`-th summand of the free sheaf. -/
theorem monomialBasisHom_comp_toPushforwardRestrictTwistOver (n : ℕ) (S : Scheme.{u}) (d : ℤ)
    (V : S.Opens) (e : MonomialIndex.{u} n d) :
    monomialBasisHom n V.toScheme d e ≫ toPushforwardRestrictTwistOver n S d V =
      Scheme.Modules.unitToPushforwardUnit ((projectiveSpaceOver n S ↘ S) ∣_ V) ≫
        (Scheme.Modules.pushforward ((projectiveSpaceOver n S ↘ S) ∣_ V)).map
          (Scheme.Modules.unitHomEquivTop
            ((Scheme.Modules.restrictFunctor ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V).ι).obj
              (twistOver n S d))
            (restrictGlobalSection ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V) (twistOver n S d)
              (twistOverSection n S d e))) :=
  ιFree_comp_freeHomEquiv_symm_pushforwardSections ((projectiveSpaceOver n S ↘ S) ∣_ V) _ _ e

/-- The morphism attached to `T^e` restricts to the morphism attached to the restriction of
`T^e` to `f⁻¹V`. -/
theorem restrict_twistOverSectionHom (n : ℕ) (S : Scheme.{u}) (d : ℤ) (V : S.Opens)
    (e : MonomialIndex.{u} n d) :
    (Scheme.Modules.restrictFunctor ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V).ι).map
        (twistOverSectionHom n S d e) =
      (restrictUnitModuleIso ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V).ι).hom ≫
        Scheme.Modules.unitHomEquivTop
          ((Scheme.Modules.restrictFunctor ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V).ι).obj
            (twistOver n S d))
          (restrictGlobalSection ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V) (twistOver n S d)
            (twistOverSection n S d e)) :=
  restrict_unitHomEquivTop ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V) (twistOver n S d)
    (twistOverSection n S d e)

/-- **Restriction to an open of the base of the canonical morphism
`(𝒪_S[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)`.** Restricted to `V` and read through the identification of the
restricted direct image with the direct image along `f ∣_ V`, it is the canonical morphism over
`V` built from the restrictions of the global sections `T^e`. -/
theorem restrict_toPushforwardTwistOver (n : ℕ) (S : Scheme.{u}) (d : ℤ) (V : S.Opens) :
    (restrictBaseDegreeSheafIso n S d V).hom ≫
        (Scheme.Modules.restrictFunctor V.ι).map (toPushforwardTwistOver n S d) ≫
        (restrictPushforwardIso (projectiveSpaceOver n S ↘ S) V).hom.app (twistOver n S d) =
      toPushforwardRestrictTwistOver n S d V := by
  refine hom_ext_of_monomialBasisHom_comp fun e ↦ ?_
  have hnat : (Scheme.Modules.restrictFunctor V.ι).map
        ((Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).map
          (twistOverSectionHom n S d e)) ≫
        (restrictPushforwardIso (projectiveSpaceOver n S ↘ S) V).hom.app (twistOver n S d) =
      (restrictPushforwardIso (projectiveSpaceOver n S ↘ S) V).hom.app
          (Scheme.unitModule (projectiveSpaceOver n S)) ≫
        (Scheme.Modules.pushforward ((projectiveSpaceOver n S ↘ S) ∣_ V)).map
          ((Scheme.Modules.restrictFunctor ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V).ι).map
            (twistOverSectionHom n S d e)) :=
    (restrictPushforwardIso (projectiveSpaceOver n S ↘ S) V).hom.naturality
      (twistOverSectionHom n S d e)
  rw [← Category.assoc (monomialBasisHom n V.toScheme d e),
    monomialBasisHom_comp_restrictBaseDegreeSheafIso_hom,
    monomialBasisHom_comp_toPushforwardRestrictTwistOver]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, monomialBasisHom_comp_toPushforwardTwistOver, Functor.map_comp]
  simp only [Category.assoc]
  rw [hnat, restrict_twistOverSectionHom, Functor.map_comp]
  rw [reassoc_of% restrictUnitToPushforwardUnitSquare (projectiveSpaceOver n S ↘ S) V,
    Iso.inv_hom_id_assoc]

end Restriction

/-! ### Base change -/

section BaseChange

variable (n : ℕ) {S' S : Scheme.{u}} (g : S' ⟶ S) (d : ℤ)

/-- The base-change morphism of projective spaces lies over the morphism of bases. -/
theorem projectiveSpaceOverMap_comp :
    projectiveSpaceOverMap n g ≫ (projectiveSpaceOver n S ↘ S) =
      (projectiveSpaceOver n S' ↘ S') ≫ g :=
  projectiveSpaceOverMap_fst n g

/-- The two factors of `twistOverPullbackIso`, read on global sections. -/
theorem twistOverPullbackIso_hom_app_top
    (x : Γ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj (twistOver n S d), ⊤)) :
    (twistOverPullbackIso n g d).hom.app ⊤ x =
      ((Scheme.Modules.pullbackCongr (projectiveSpaceOverMap_snd n g)).hom.app
          (projectiveSpaceAtUniverseTwistingSheaf.{u} n d)).app ⊤
        (((Scheme.Modules.pullbackComp (projectiveSpaceOverMap n g)
            (projectiveSpaceOver.toIntegralAtUniverse n S)).hom.app
          (projectiveSpaceAtUniverseTwistingSheaf.{u} n d)).app ⊤ x) :=
  rfl

/-- **The global section `T^e` of `𝒪(d)` is stable under base change**: its pullback along
`ℙⁿ_{S'} ⟶ ℙⁿ_S` is the global section `T^e` of `𝒪(d)` on `ℙⁿ_{S'}`. -/
theorem twistOverPullbackIso_hom_app_twistOverSection (e : MonomialIndex.{u} n d) :
    (twistOverPullbackIso n g d).hom.app ⊤
        (pullbackGlobalSections (projectiveSpaceOverMap n g) (twistOver n S d)
          (twistOverSection n S d e)) =
      twistOverSection n S' d e := by
  rw [twistOverPullbackIso_hom_app_top, twistOverSection, twistOverSection,
    AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp]
  exact AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_congr
    (projectiveSpaceOverMap_snd n g)
    (projectiveSpaceAtUniverseTwistingSheaf.{u} n d) (monomialSectionAtUniverse e)

/-- **The morphism out of the structure sheaf attached to `T^e` is stable under base change.**
Its pullback along `ℙⁿ_{S'} ⟶ ℙⁿ_S`, read through the base-change isomorphisms of the structure
sheaf and of the twist, is the morphism attached to `T^e` on `ℙⁿ_{S'}`. -/
theorem pullback_map_twistOverSectionHom (e : MonomialIndex.{u} n d) :
    (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map (twistOverSectionHom n S d e) ≫
        (twistOverPullbackIso n g d).hom =
      (Scheme.Modules.pullbackUnitIso (projectiveSpaceOverMap n g)).hom ≫
        twistOverSectionHom n S' d e := by
  refine Eq.trans (Scheme.Modules.pullbackUnitIso_sections_naturality
    (projectiveSpaceOverMap n g) (twistOver n S d) (twistOver n S' d)
    (twistOverPullbackIso n g d).hom (twistOverSection n S d e)).symm ?_
  refine congrArg (fun z ↦ (Scheme.Modules.pullbackUnitIso
    (projectiveSpaceOverMap n g)).hom ≫ Scheme.Modules.unitHomEquivTop (twistOver n S' d) z) ?_
  refine Eq.trans ?_ (twistOverPullbackIso_hom_app_twistOverSection n g d e)
  rw [Adjunction.homEquiv_unit]
  exact (Scheme.Modules.Hom.app_presheaf_map (twistOverPullbackIso n g d).hom
    (eqToHom (show (⊤ : (projectiveSpaceOver n S').Opens) =
      projectiveSpaceOverMap n g ⁻¹ᵁ ⊤ by simp))
    (((Scheme.Modules.pullbackPushforwardAdjunction
      (projectiveSpaceOverMap n g)).unit.app (twistOver n S d)).app ⊤
        (twistOverSection n S d e))).symm

/-- **The degree-`d` sheaf on the base is stable under base change**: the pullback of
`(𝒪_S[T₀, …, Tₙ])_d` along `g` is `(𝒪_{S'}[T₀, …, Tₙ])_d`, a free sheaf pulling back to the free
sheaf on the same index type. -/
def pullbackBaseDegreeSheafIso :
    (Scheme.Modules.pullback g).obj (baseDegreeSheaf n S d) ≅ baseDegreeSheaf n S' d :=
  have : (Opens.map g.base).Final := CategoryTheory.final_of_representablyFlat _
  have : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  SheafOfModules.pullbackObjFreeIso g.toRingCatSheafHom (MonomialIndex.{u} n d)

/-- The base-change isomorphism of `(𝒪_S[T₀, …, Tₙ])_d` on the `e`-th summand of the free
sheaf. -/
theorem pullback_map_monomialBasisHom_comp_pullbackBaseDegreeSheafIso_hom
    (e : MonomialIndex.{u} n d) :
    (Scheme.Modules.pullback g).map (monomialBasisHom n S d e) ≫
        (pullbackBaseDegreeSheafIso n g d).hom =
      (Scheme.Modules.pullbackUnitIso g).hom ≫ monomialBasisHom n S' d e :=
  have : (Opens.map g.base).Final := CategoryTheory.final_of_representablyFlat _
  have : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom g.toRingCatSheafHom e

/-- The morphism `𝒪(d) ⟶ p_* 𝒪(d)` transposing the base-change isomorphism of the twists: the
map restricting a section of `𝒪(d)` on `ℙⁿ_S` to a section of `𝒪(d)` on `ℙⁿ_{S'}`. -/
def twistOverPushforwardHom :
    twistOver n S d ⟶
      (Scheme.Modules.pushforward (projectiveSpaceOverMap n g)).obj (twistOver n S' d) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (projectiveSpaceOverMap n g)).homEquiv _ _
    (twistOverPullbackIso n g d).hom

/-- The morphism `(𝒪_S[T₀, …, Tₙ])_d ⟶ g_* (𝒪_{S'}[T₀, …, Tₙ])_d` transposing the base-change
isomorphism of the degree-`d` sheaves on the bases. -/
def baseDegreeSheafPushforwardHom :
    baseDegreeSheaf n S d ⟶ (Scheme.Modules.pushforward g).obj (baseDegreeSheaf n S' d) :=
  (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
    (pullbackBaseDegreeSheafIso n g d).hom

/-- The transposed base-change isomorphism of `(𝒪_S[T₀, …, Tₙ])_d` on the `e`-th summand. -/
theorem monomialBasisHom_comp_baseDegreeSheafPushforwardHom (e : MonomialIndex.{u} n d) :
    monomialBasisHom n S d e ≫ baseDegreeSheafPushforwardHom n g d =
      Scheme.Modules.unitToPushforwardUnit g ≫
        (Scheme.Modules.pushforward g).map (monomialBasisHom n S' d e) := by
  rw [baseDegreeSheafPushforwardHom, ← Adjunction.homEquiv_naturality_left,
    pullback_map_monomialBasisHom_comp_pullbackBaseDegreeSheafIso_hom,
    Adjunction.homEquiv_naturality_right, Scheme.Modules.pullbackUnitIso_homEquiv]

/-- **The morphism out of the structure sheaf attached to `T^e` is stable under base change**,
in the direct-image form: composing it with the restriction map of sections of `𝒪(d)` gives the
direct image along `ℙⁿ_{S'} ⟶ ℙⁿ_S` of the morphism attached to `T^e` on `ℙⁿ_{S'}`. -/
theorem twistOverSectionHom_comp_twistOverPushforwardHom (e : MonomialIndex.{u} n d) :
    twistOverSectionHom n S d e ≫ twistOverPushforwardHom n g d =
      Scheme.Modules.unitToPushforwardUnit (projectiveSpaceOverMap n g) ≫
        (Scheme.Modules.pushforward (projectiveSpaceOverMap n g)).map
          (twistOverSectionHom n S' d e) := by
  rw [twistOverPushforwardHom, ← Adjunction.homEquiv_naturality_left,
    pullback_map_twistOverSectionHom, Adjunction.homEquiv_naturality_right,
    Scheme.Modules.pullbackUnitIso_homEquiv]

/-- The structure-sheaf maps of equal morphisms of schemes agree. -/
theorem unitToPushforwardUnit_pushforwardCongr {X Y : Scheme.{u}} {a b : X ⟶ Y} (h : a = b) :
    Scheme.Modules.unitToPushforwardUnit a ≫
        (Scheme.Modules.pushforwardCongr h).hom.app (Scheme.unitModule X) =
      Scheme.Modules.unitToPushforwardUnit b := by
  subst h
  refine Eq.trans ?_ (Category.comp_id (Scheme.Modules.unitToPushforwardUnit a))
  refine congrArg (fun k ↦ Scheme.Modules.unitToPushforwardUnit a ≫ k) ?_
  ext U
  simp

/-- **The structure sheaf of `ℙⁿ_{S'}` sees the base-change square.** The two ways around the
square of structure-sheaf maps agree, through the identification of the two composite direct
images. -/
theorem unitToPushforwardUnit_pushforwardSquareIso :
    Scheme.Modules.unitToPushforwardUnit (projectiveSpaceOver n S ↘ S) ≫
        (Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).map
          (Scheme.Modules.unitToPushforwardUnit (projectiveSpaceOverMap n g)) ≫
        (pushforwardSquareIso (projectiveSpaceOverMap_comp n g)).hom.app
          (Scheme.unitModule (projectiveSpaceOver n S')) =
      Scheme.Modules.unitToPushforwardUnit g ≫
        (Scheme.Modules.pushforward g).map
          (Scheme.Modules.unitToPushforwardUnit (projectiveSpaceOver n S' ↘ S')) := by
  have h1 := Scheme.Modules.unitToPushforwardUnit_comp (projectiveSpaceOverMap n g)
    (projectiveSpaceOver n S ↘ S)
  have h2 := Scheme.Modules.unitToPushforwardUnit_comp (projectiveSpaceOver n S' ↘ S') g
  have h3 := unitToPushforwardUnit_pushforwardCongr (projectiveSpaceOverMap_comp n g)
  have key : Scheme.Modules.unitToPushforwardUnit (projectiveSpaceOver n S ↘ S) ≫
        (Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).map
          (Scheme.Modules.unitToPushforwardUnit (projectiveSpaceOverMap n g)) ≫
        (pushforwardSquareIso (projectiveSpaceOverMap_comp n g)).hom.app
          (Scheme.unitModule (projectiveSpaceOver n S')) =
      (Scheme.Modules.unitToPushforwardUnit (projectiveSpaceOver n S ↘ S) ≫
          (Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).map
            (Scheme.Modules.unitToPushforwardUnit (projectiveSpaceOverMap n g)) ≫
          (Scheme.Modules.pushforwardComp (projectiveSpaceOverMap n g)
            (projectiveSpaceOver n S ↘ S)).hom.app
            (Scheme.unitModule (projectiveSpaceOver n S'))) ≫
        (Scheme.Modules.pushforwardCongr (projectiveSpaceOverMap_comp n g)).hom.app
          (Scheme.unitModule (projectiveSpaceOver n S')) ≫
        (Scheme.Modules.pushforwardComp (projectiveSpaceOver n S' ↘ S') g).inv.app
          (Scheme.unitModule (projectiveSpaceOver n S')) := by
    rw [pushforwardSquareIso]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [key, h1, ← Category.assoc, h3, ← h2]
  simp

/-- **Base change for the canonical morphism `(𝒪_S[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)`, in the
direct-image form.** Following the canonical morphism for `S` by the restriction of sections of
`𝒪(d)` to `ℙⁿ_{S'}` is the same as following the restriction of sections of
`(𝒪_S[T₀, …, Tₙ])_d` to `S'` by the canonical morphism for `S'`. -/
theorem toPushforwardTwistOver_pushforwardSquare :
    toPushforwardTwistOver n S d ≫
        (Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).map
          (twistOverPushforwardHom n g d) ≫
        (pushforwardSquareIso (projectiveSpaceOverMap_comp n g)).hom.app (twistOver n S' d) =
      baseDegreeSheafPushforwardHom n g d ≫
        (Scheme.Modules.pushforward g).map (toPushforwardTwistOver n S' d) := by
  refine hom_ext_of_monomialBasisHom_comp fun e ↦ ?_
  have hnat : (Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).map
        ((Scheme.Modules.pushforward (projectiveSpaceOverMap n g)).map
          (twistOverSectionHom n S' d e)) ≫
        (pushforwardSquareIso (projectiveSpaceOverMap_comp n g)).hom.app (twistOver n S' d) =
      (pushforwardSquareIso (projectiveSpaceOverMap_comp n g)).hom.app
          (Scheme.unitModule (projectiveSpaceOver n S')) ≫
        (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.pushforward (projectiveSpaceOver n S' ↘ S')).map
            (twistOverSectionHom n S' d e)) :=
    (pushforwardSquareIso (projectiveSpaceOverMap_comp n g)).hom.naturality
      (twistOverSectionHom n S' d e)
  rw [← Category.assoc (monomialBasisHom n S d e),
    monomialBasisHom_comp_toPushforwardTwistOver,
    ← Category.assoc (monomialBasisHom n S d e),
    monomialBasisHom_comp_baseDegreeSheafPushforwardHom]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [← Functor.map_comp_assoc, twistOverSectionHom_comp_twistOverPushforwardHom,
    monomialBasisHom_comp_toPushforwardTwistOver n S' d e]
  simp only [Functor.map_comp, Category.assoc]
  rw [hnat, reassoc_of% unitToPushforwardUnit_pushforwardSquareIso n g]

/-- The restriction map of sections of `𝒪(d)` along `ℙⁿ_{S'} ⟶ ℙⁿ_S` as the unit of the
pullback–pushforward adjunction followed by the base-change isomorphism of the twists. -/
theorem twistOverPushforwardHom_eq :
    twistOverPushforwardHom n g d =
      (Scheme.Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverMap n g)).unit.app (twistOver n S d) ≫
        (Scheme.Modules.pushforward (projectiveSpaceOverMap n g)).map
          (twistOverPullbackIso n g d).hom :=
  Adjunction.homEquiv_unit ..

/-- **Base change for the canonical morphism `(𝒪_S[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)`.** Its pullback
along `g`, followed by the base-change morphism `g^* f_* ⟶ f'_* p^*` of
[Stacks, Tag 02KG] and the base-change isomorphism of the twists, is the canonical morphism
for `S'`, read through the base-change isomorphism of `(𝒪_S[T₀, …, Tₙ])_d`. -/
theorem toPushforwardTwistOver_baseChange :
    (Scheme.Modules.pullback g).map (toPushforwardTwistOver n S d) ≫
        (baseChangeNatTrans (projectiveSpaceOverMap_comp n g)).app (twistOver n S d) ≫
        (Scheme.Modules.pushforward (projectiveSpaceOver n S' ↘ S')).map
          (twistOverPullbackIso n g d).hom =
      (pullbackBaseDegreeSheafIso n g d).hom ≫ toPushforwardTwistOver n S' d := by
  have hstar : (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((baseChangeNatTrans (projectiveSpaceOverMap_comp n g)).app (twistOver n S d)) =
      (Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (projectiveSpaceOverMap n g)).unit.app (twistOver n S d)) ≫
        (pushforwardSquareIso (projectiveSpaceOverMap_comp n g)).hom.app
          ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj (twistOver n S d)) := by
    rw [Adjunction.homEquiv_unit]
    exact (unit_mateEquiv_symm
      (Scheme.Modules.pullbackPushforwardAdjunction (projectiveSpaceOverMap n g))
      (Scheme.Modules.pullbackPushforwardAdjunction g)
      (pushforwardSquareIso (projectiveSpaceOverMap_comp n g)).hom (twistOver n S d)).symm
  have hnat : (Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).map
        ((Scheme.Modules.pushforward (projectiveSpaceOverMap n g)).map
          (twistOverPullbackIso n g d).hom) ≫
        (pushforwardSquareIso (projectiveSpaceOverMap_comp n g)).hom.app (twistOver n S' d) =
      (pushforwardSquareIso (projectiveSpaceOverMap_comp n g)).hom.app
          ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj (twistOver n S d)) ≫
        (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.pushforward (projectiveSpaceOver n S' ↘ S')).map
            (twistOverPullbackIso n g d).hom) :=
    (pushforwardSquareIso (projectiveSpaceOverMap_comp n g)).hom.naturality
      (twistOverPullbackIso n g d).hom
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right, hstar]
  simp only [Category.assoc]
  rw [← hnat]
  simp only [← Functor.map_comp_assoc]
  rw [← twistOverPushforwardHom_eq]
  exact toPushforwardTwistOver_pushforwardSquare n g d

end BaseChange

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
