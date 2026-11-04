module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperSupportModel.AffinePushforwardSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction

/-!
# The scheme-theoretic support of a module with proper support, and its base changes

Let `X` be a scheme and `G` a quasi-coherent `𝒪_X`-module of finite type. Its scheme-theoretic
support is a closed subscheme `ι : Z ⟶ X` carrying `G' = ι^* G` with `ι_* G' ≅ G`. If the
support of `G` lies in a closed subset proper over a base `S`, then `Z` is proper over `S`, hence
separated over `S`, even when `X` is not. This file proves that, flatness of `G'` over the base,
and the behaviour of the support under base change `g : X' ⟶ X`: with `Z' = Z ×_X X'`, affine
base change gives `g^* G ≅ ι'_* (g_Z^* G')`, and hence `RΓ(Z', g_Z^* G') ≅ RΓ(X', g^* G)` over
the base.

## Main definitions

* `supportScheme`, `supportι`, `supportModule`, `supportModuleIso`: the scheme-theoretic support
  `Z`, its closed immersion `ι`, the module `G' = ι^* G` and `ι_* G' ≅ G`.
* `supportPullback`, `supportFst`, `supportSnd`: `Z' = Z ×_X X'` and its two projections.
* `supportBaseChangeIso`: `g^* G ≅ ι'_* (g_Z^* G')`.
* `supportComparisonIso`: `RΓ(Z', g_Z^* G') ≅ RΓ(X', g^* G)` over the base.
* `supportTowerMap`: the canonical `Z'' ⟶ Z'` for a second base change.

## Main results

* `isProper_supportι_comp`: `Z` is proper over the base.
* `isFlatOver_supportModule`: `G'` is flat over the base if `G` is.
* `isPullback_support`, `isPullback_supportTowerMap`, `isPullback_supportTower`: the cartesian
  squares for the supports.

## References

* [Stacks Project, Tag 0CYS](https://stacks.math.columbia.edu/tag/0CYS)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0FLM](https://stacks.math.columbia.edu/tag/0FLM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportModel

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}} (G : X.Modules) [G.IsQuasicoherent] [G.IsFiniteType]

/-- The ideal sheaf of the scheme-theoretic support of `G`. -/
abbrev supportIdeal : X.IdealSheafData := Scheme.Modules.schemeTheoreticSupport G

/-- The scheme-theoretic support of `G`, as a closed subscheme `Z` of `X`. -/
abbrev supportScheme : Scheme.{u} := (supportIdeal G).subscheme

/-- The closed immersion `ι : Z ⟶ X` of the scheme-theoretic support of `G`. -/
abbrev supportι : supportScheme G ⟶ X := (supportIdeal G).subschemeι

/-- The restriction `G' = ι^* G` of `G` to its scheme-theoretic support. -/
abbrev supportModule : (supportScheme G).Modules :=
  (Scheme.Modules.pullback (supportι G)).obj G

/-- `ι_* G' ≅ G`, the inverse of the unit of the pullback--pushforward adjunction. -/
abbrev supportModuleIso : (Scheme.Modules.pushforward (supportι G)).obj (supportModule G) ≅ G :=
  Scheme.Modules.pushforwardPullbackSchemeTheoreticSupportIso G

/-- The scheme-theoretic support is proper over the base as soon as the support of `G` lies in a
closed subset proper over the base. -/
theorem isProper_supportι_comp {S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (hsupp : ∃ Z : Closeds X, IsProperOver f Z ∧ SheafOfModules.supp G ⊆ (Z : Set X)) :
    IsProper (supportι G ≫ f) := by
  obtain ⟨Z, hZ, hGZ⟩ := hsupp
  exact (Scheme.Modules.isProperOver_supp_iff_isProper_schemeTheoreticSupport f G).1
    (isProperOver_of_le f
      (show (⟨SheafOfModules.supp G, SheafOfModules.isClosed_supp G⟩ : Closeds X) ≤ Z from hGZ)
      hZ)

/-- `G'` is flat over the base if `G` is. -/
theorem isFlatOver_supportModule {S : Scheme.{u}} (f : X ⟶ S)
    (hflat : IsFlatOver f.toLRSHom.toShHom G) :
    IsFlatOver (supportι G ≫ f).toLRSHom.toShHom (supportModule G) :=
  (isFlatOver_pushforward_iff (supportι G) f (supportModule G)).2
    ((isFlatOver_iff_of_iso f (supportModuleIso G)).2 hflat)

section BaseChange

variable {X' : Scheme.{u}} (g : X' ⟶ X)

/-- The base change `Z' = Z ×_X X'` of the scheme-theoretic support along `g : X' ⟶ X`. -/
abbrev supportPullback : Scheme.{u} := Limits.pullback (supportι G) g

/-- The projection `Z' ⟶ Z`. -/
abbrev supportFst : supportPullback G g ⟶ supportScheme G := pullback.fst _ _

/-- The closed immersion `Z' ⟶ X'`. -/
abbrev supportSnd : supportPullback G g ⟶ X' := pullback.snd _ _

/-- Affine base change for the support: `g^* G ≅ ι'_* (g_Z^* G')`. -/
def supportBaseChangeIso :
    (Scheme.Modules.pullback g).obj G ≅
      (Scheme.Modules.pushforward (supportSnd G g)).obj
        ((Scheme.Modules.pullback (supportFst G g)).obj (supportModule G)) :=
  (Scheme.Modules.pullback g).mapIso (supportModuleIso G).symm ≪≫
    @asIso _ _ _ _
      ((AffinePushforward.baseChangeNatTrans
        (IsPullback.of_hasPullback (supportι G) g).w).app (supportModule G))
      (Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
        (IsPullback.of_hasPullback (supportι G) g) (supportModule G))

variable {A' : Type u} [CommRing A']

/-- `RΓ(Z', g_Z^* G') ≅ RΓ(X', g^* G)` over the base, for `f' : X' ⟶ Spec A'`: the comparison
along the affine morphism `ι' : Z' ⟶ X'` followed by affine base change for the support. -/
def supportComparisonIso (f' : X' ⟶ Spec (.of A')) :
    derivedGlobalSectionsOverBase (supportSnd G g ≫ f')
        ((Scheme.Modules.pullback (supportFst G g)).obj (supportModule G)) ≅
      derivedGlobalSectionsOverBase f' ((Scheme.Modules.pullback g).obj G) :=
  derivedGlobalSectionsOverBasePushforwardIso f' (supportSnd G g) _ ≪≫
    derivedGlobalSectionsOverBaseMapIso f' (supportBaseChangeIso G g).symm

variable {A : Type u} [CommRing A] (f : X ⟶ Spec (.of A))

/-- A cartesian square over `Spec A' ⟶ Spec A` for `X` induces one for its support: `Z'` is the
base change of `Z` along `Spec A' ⟶ Spec A`. -/
theorem isPullback_support (φ : A →+* A') {f' : X' ⟶ Spec (.of A')}
    (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) :
    IsPullback (supportFst G g) (supportSnd G g ≫ f') (supportι G ≫ f)
      (Spec.map (CommRingCat.ofHom φ)) :=
  (IsPullback.of_hasPullback (supportι G) g).paste_vert hsq

end BaseChange

section Tower

variable {X' X'' : Scheme.{u}} (g : X' ⟶ X) (g' : X'' ⟶ X')

/-- The canonical map `Z'' ⟶ Z'` from the support base change along `g' ≫ g` to the one along
`g`. -/
def supportTowerMap : supportPullback G (g' ≫ g) ⟶ supportPullback G g :=
  pullback.lift (supportFst G (g' ≫ g)) (supportSnd G (g' ≫ g) ≫ g')
    (by rw [pullback.condition, Category.assoc])

/-- The canonical map `Z'' ⟶ Z'` lies over `Z`. -/
theorem supportTowerMap_fst :
    supportTowerMap G g g' ≫ supportFst G g = supportFst G (g' ≫ g) :=
  pullback.lift_fst _ _ _

/-- The canonical map `Z'' ⟶ Z'` lies over `g' : X'' ⟶ X'`. -/
theorem supportTowerMap_snd :
    supportTowerMap G g g' ≫ supportSnd G g = supportSnd G (g' ≫ g) ≫ g' :=
  pullback.lift_snd _ _ _

/-- `Z'' = Z' ×_{X'} X''`: the support base change along a composite is the iterated one. -/
theorem isPullback_supportTowerMap :
    IsPullback (supportTowerMap G g g') (supportSnd G (g' ≫ g)) (supportSnd G g) g' :=
  IsPullback.of_right (by
      rw [supportTowerMap_fst]
      exact IsPullback.of_hasPullback (supportι G) (g' ≫ g))
    (supportTowerMap_snd G g g') (IsPullback.of_hasPullback (supportι G) g)

variable {A' A'' : Type u} [CommRing A'] [CommRing A''] (ψ : A' →+* A'')

/-- A cartesian square over `Spec A'' ⟶ Spec A'` for `X'` induces one for the supports: `Z''`
is the base change of `Z'` along `Spec A'' ⟶ Spec A'`. -/
theorem isPullback_supportTower {f' : X' ⟶ Spec (.of A')} {f'' : X'' ⟶ Spec (.of A'')}
    (hsq' : IsPullback g' f'' f' (Spec.map (CommRingCat.ofHom ψ))) :
    IsPullback (supportTowerMap G g g') (supportSnd G (g' ≫ g) ≫ f'') (supportSnd G g ≫ f')
      (Spec.map (CommRingCat.ofHom ψ)) :=
  (isPullback_supportTowerMap G g g').paste_vert hsq'

end Tower

end Stacks.AlgebraicGeometry.ProperSupportModel
