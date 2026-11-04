module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDifferentialsCorepresentable
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDifferentialsInvertible

/-!
# Localizing a derivation of `𝒪_{X_étale}` along an object of the small étale site

Let `f : X ⟶ Y` be a morphism of schemes with `X` in a big étale site `B`, and let `D` be a
derivation of the structure sheaf `𝒪_{X_étale}` of the small étale site of `X` with values in a
sheaf of `𝒪_{X_étale}`-modules `𝓕`.

`AlgebraicGeometry.SmallEtale.zariskiRestrictionData`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDifferentials.lean`) restricts
`D` to the small Zariski site of `X` itself.  This module does the same for the scheme `T` of an
arbitrary object `h : T ⟶ X` of the small étale site: it produces a derivation of `𝒪_T` whose
value over an open `W` of `T` is the value of `D` over the object `W ↪ T ⟶ X`.

The comparison map `c''` of the invertibility clause of Stacks 04CS is built from the restriction
of `D` to the small Zariski site of `X` alone, so recovering `D` from it needs the values of `D`
over *every* object of the small étale site to be determined by the Zariski ones.  They are, and
by a shorter route than this module's:
`AlgebraicGeometry.SmallEtale.eq_of_zariskiRestrictionData_eq` proves it outright, with no
hypothesis on the functions pulled back from `Y`, and that is what
`AlgebraicGeometry.SmallEtale.associatedDerivation_postcomp_differentialsComparison` below uses.
The localization built here is a second route, carried as far as
`AlgebraicGeometry.SmallEtale.objTransport_universalRelativeDerivation`, and it stands on its own
as the localization of a derivation along an object of the small étale site.

## Main definitions

* `AlgebraicGeometry.SmallEtale.objZariskiModule` is the sheaf of `𝒪_T`-modules
  `W ↦ 𝓕(W ↪ T ⟶ X)`, obtained by pushing `𝓕` forward along the morphism of ringed sites
  `(X_étale/V, 𝒪) ⟶ (T_Zar, 𝒪_T)` of
  `AlgebraicGeometry.SmallEtale.objSliceStructureMap`.
* `AlgebraicGeometry.SmallEtale.objZariskiRestrictionData` is the localization of `D` along the
  object, as bare derivation data over the constant presheaf of rings `ℤ`.
* `AlgebraicGeometry.SmallEtale.objZariskiRestriction` is the same localization carrying the
  vanishing over `(h ≫ f)⁻¹𝒪_Y`, i.e. an ordinary `Y`-derivation of `𝒪_T`.  It is therefore an
  admissible input to the universal property of `Ω_{T/Y}`.
* `AlgebraicGeometry.SmallEtale.objOpenHom` is the factorization of the object
  `h⁻¹W ↪ T ⟶ X` through the object `W ↪ X`, for `W` an open of `X`.
* `AlgebraicGeometry.SmallEtale.objDesc` is the factorization of that `Y`-derivation through
  `Ω_{T/Y}`, given by that module's universal property, and
  `AlgebraicGeometry.SmallEtale.objTransport` is the same morphism read on `X`, through
  Stacks 04BX (`AlgebraicGeometry.SmallEtale.objDifferentialsIso`) and the adjunction
  `h^* ⊣ h_*`.

## Main results

* `AlgebraicGeometry.SmallEtale.objZariskiRestrictionData_d`: its value over an open `W` of `T`
  is the value of `D` over the object `W ↪ T ⟶ X`, read through the identification of `Γ(T, W)`
  with the global functions of the open subscheme `W`.
* `AlgebraicGeometry.SmallEtale.map_structureSection`: a section of `𝒪_X` over an open `W`,
  read as a section of `𝒪_{X_étale}` over the object `W ↪ X`, restricts along that factorization
  to its pullback along `h`.  Both are the image of the section under the comorphism of
  `h⁻¹W ↪ T ⟶ X`.  This is the compatibility the whole argument runs on, and
  `AlgebraicGeometry.SmallEtale.map_pullbackSection` is its instance at `W = f⁻¹W` which the
  vanishing condition needs.
* `AlgebraicGeometry.SmallEtale.objZariskiRestrictionData_comorphism_eq_zero`: hence the
  localization of a derivation annihilating the functions pulled back from `Y` again annihilates
  them, which is what `AlgebraicGeometry.SheafOfModules.ofComorphism` consumes.
* `AlgebraicGeometry.SmallEtale.objTransport_universalRelativeDerivation`: **the bridge.**  Over
  an open `W` of `X` the transported factorization carries `d_{X/Y} a` to the restriction, along
  `AlgebraicGeometry.SmallEtale.objOpenHom`, of the value of the small Zariski restriction of `D`
  on `a`.  So the transported factorization depends on `D` only through that restriction, while
  the factorization it came from determines the values of `D` over `T`; the universal property of
  `Ω_{X/Y}` joins the two.

## Implementation notes

The target module is taken as the pushforward along
`AlgebraicGeometry.SmallEtale.objSliceStructureMap`, i.e. on the *slice* `X_étale/V`, rather than
as the crossover `AlgebraicGeometry.SmallEtale.objRestrict` to the small étale site of `T`.  Both
have the same sections, but `objRestrict` is a composite of two pushforwards, and the
restriction-of-scalars in each does not unfold at reducible transparency: the `d_map` field of the
derivation then asks the elaborator to identify two spellings of the restriction map of `𝓕` and
exhausts its heartbeats.  Against a single pushforward the identification is immediate, which is
exactly why `AlgebraicGeometry.SmallEtale.zariskiRestrictionData` is written against
`AlgebraicGeometry.SmallEtale.restrictModule`; this module reuses that shape.

For the same reason the object of the small étale site of `X` carrying the value of `D` over an
open `W` of `T` is spelled `((objToSmallEtaleOver B X hX V).obj W).left` — the slice object's
underlying object — rather than through
`AlgebraicGeometry.SmallEtale.postcompose`, which is the same object but reached by unfolding
`CategoryTheory.ObjectProperty.lift`.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), the associated module on
  the small étale site and its right adjoint.
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R), the morphism of ringed
  sites `(S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)

/-- The sheaf of `𝒪_T`-modules attached to a sheaf of `𝒪_{X_étale}`-modules `𝓕` and an object
`V` of the small étale site of `X` with scheme `T`: over an open `W` of `T` its sections are the
sections of `𝓕` over the object `W ↪ T ⟶ X`.

It is the pushforward of the restriction of `𝓕` to the slice `X_étale/V` along the morphism of
ringed sites `(X_étale/V, 𝒪) ⟶ (T_Zar, 𝒪_T)`, which is the morphism of Stacks 070R for `T` read
in the slice. -/
public noncomputable abbrev objZariskiModule
    (F : SheafOfModules.{u} (structureSheaf B X hX)) (V : SmallEtale B X hX) :
    (objScheme B X hX V).Modules :=
  (SheafOfModules.pushforward.{u} (objSliceStructureMap B X hX V)).obj (F.over V)

variable {F : SheafOfModules.{u} (structureSheaf B X hX)}
  {R : (SmallEtale B X hX)ᵒᵖ ⥤ CommRingCat.{u}}
  {ψ : R ⟶ (commRingStructureSheaf B X hX).obj}
  (D : PresheafOfModules.Derivation'
    (R := (commRingStructureSheaf B X hX).obj) F.val ψ)
  (V : SmallEtale B X hX)

/-- **The localization of a derivation of `𝒪_{X_étale}` along an object of the small étale
site**, as bare derivation data: over an open `W` of the scheme `T` of the object it is the
derivation `D` taken over the object `W ↪ T ⟶ X` of the small étale site of `X`, read through the
identification of `Γ(T, W)` with the global functions of the open subscheme `W` given by the
structure map of the morphism of ringed sites of Stacks 070R for `T`.

The vanishing condition recorded here is only the Leibniz rule, over the constant presheaf of
rings `ℤ`; the vanishing over `(h ≫ f)⁻¹𝒪_Y` is added separately, exactly as it is for
`AlgebraicGeometry.SmallEtale.zariskiRestrictionData`. -/
public noncomputable def objZariskiRestrictionData :
    (objZariskiModule B hX F V).val.Derivation'
      (SheafOfModules.constIntMap (objScheme B X hX V).presheaf) where
  d {W} := (D.d (X := op (((objToSmallEtaleOver B X hX V).obj W.unop).left))).comp
    ((commRingStructureMap B (objScheme B X hX V)
      (contains_objScheme B X hX V)).hom.app W).hom.toAddMonoidHom
  d_mul {W} a b :=
    Eq.trans (congrArg (D.d (X := op (((objToSmallEtaleOver B X hX V).obj W.unop).left)))
      (map_mul ((commRingStructureMap B (objScheme B X hX V)
        (contains_objScheme B X hX V)).hom.app W).hom a b)) (D.d_mul _ _)
  d_map {W W'} g x := by
    refine Eq.trans (congrArg
      (D.d (X := op (((objToSmallEtaleOver B X hX V).obj W'.unop).left))) ?_)
      (D.d_map ((objToSmallEtaleOver B X hX V ⋙ Over.forget V).map g.unop).op
        (((commRingStructureMap B (objScheme B X hX V)
          (contains_objScheme B X hX V)).hom.app W).hom x))
    exact congrArg (fun m : CommRingCat.Hom _ _ => m.hom x)
      ((commRingStructureMap B (objScheme B X hX V)
        (contains_objScheme B X hX V)).hom.naturality g)
  d_app {W} a := by
    refine SheafOfModules.constIntMap_app_eq_zero
      ((D.d (X := op (((objToSmallEtaleOver B X hX V).obj W.unop).left))).comp
        ((commRingStructureMap B (objScheme B X hX V)
          (contains_objScheme B X hX V)).hom.app W).hom.toAddMonoidHom) ?_ a
    refine Eq.trans (congrArg
      (D.d (X := op (((objToSmallEtaleOver B X hX V).obj W.unop).left)))
      (map_one ((commRingStructureMap B (objScheme B X hX V)
        (contains_objScheme B X hX V)).hom.app W).hom)) ?_
    exact D.d_one _

/-- The localization of `D` along an object takes, over an open `W` of the scheme `T` of the
object, the value of `D` over the object `W ↪ T ⟶ X` of the small étale site of `X`. -/
public theorem objZariskiRestrictionData_d {W : ((objScheme B X hX V).Opens)ᵒᵖ}
    (a : Γ(objScheme B X hX V, W.unop)) :
    (objZariskiRestrictionData B hX D V).d a =
      D.d (X := op (((objToSmallEtaleOver B X hX V).obj W.unop).left))
        (((commRingStructureMap B (objScheme B X hX V)
          (contains_objScheme B X hX V)).hom.app W).hom a) :=
  rfl

section Vanishing

/-- The structure morphism of an object of the small étale site of `X` which factors through an
open `U` of `X` is that factorization followed by the open immersion of `U`.  This is
`CategoryTheory.Over.w` of the factorization, read on underlying schemes. -/
public theorem toScheme_map_comp_ι {Z : SmallEtale B X hX} (U : X.Opens)
    (k : Z ⟶ (opensToSmallEtale B X hX).obj U) :
    (toScheme B X hX).map k ≫ ((opensToSmallEtale B X hX).obj U).obj.hom.hom =
      Z.obj.hom.hom :=
  congrArg (fun m : Z.obj.left ⟶ B.obj X hX => m.hom) (Over.w k.hom)

/-- **The object `h⁻¹W ↪ T ⟶ X` of the small étale site of `X` factors through the object
`W ↪ X`.**  Its structure morphism over `X` is `h⁻¹W ↪ T ⟶ X`, whose range lies in `W`, and the
small Zariski site of `X` is a full subcategory on which such a factorization is unique. -/
public noncomputable def objOpenHom (W : X.Opens) :
    ((objToSmallEtaleOver B X hX V).obj (objHom B X hX V ⁻¹ᵁ W)).left ⟶
      (opensToSmallEtale B X hX).obj W :=
  homOfRangeLe B X hX W
    (range_le_of_le_preimage B X hX V W (objHom B X hX V ⁻¹ᵁ W) le_rfl)

/-- A section of `𝒪_X` over an open `W`, read as a global function on the open subscheme `W`, is
the image of that section under the comorphism of `W ↪ X`. -/
public theorem structureSection_eq_appLE (W : X.Opens) (a : Γ(X, W)) :
    ((commRingStructureMap B X hX).hom.app (op W)).hom a =
      W.ι.appLE W ⊤ (Scheme.Opens.top_le_ι_preimage (U := W) le_rfl) a :=
  congrArg (fun m : Γ(X, W) ⟶ Γ(W.toScheme, ⊤) => ConcreteCategory.hom m a)
    (Scheme.Opens.ι_appLE_top W
      (Scheme.Opens.top_le_ι_preimage (U := W) le_rfl)).symm

/-- The function on `h⁻¹W ⊆ T` pulled back from a section of `𝒪_X` over `W`, read through the
identification of `Γ(T, h⁻¹W)` with the global functions of the open subscheme `h⁻¹W`, is the
image of that section under the comorphism of `h⁻¹W ↪ T ⟶ X`. -/
public theorem objStructureSection_eq_appLE (W : X.Opens) (a : Γ(X, W)) :
    ((commRingStructureMap B (objScheme B X hX V)
        (contains_objScheme B X hX V)).hom.app
          (op (objHom B X hX V ⁻¹ᵁ W))).hom
        (((objHom B X hX V).app W).hom a) =
      ((objHom B X hX V ⁻¹ᵁ W).ι ≫ objHom B X hX V).appLE W ⊤
        (Scheme.Opens.top_le_ι_preimage
          (U := objHom B X hX V ⁻¹ᵁ W) le_rfl) a := by
  change ((Scheme.Opens.topIso (objHom B X hX V ⁻¹ᵁ W)).inv).hom
    ((Scheme.Hom.app (objHom B X hX V) W).hom a) = _
  rw [← Scheme.Opens.ι_appLE_top (objHom B X hX V ⁻¹ᵁ W)
    (Scheme.Opens.top_le_ι_preimage
      (U := objHom B X hX V ⁻¹ᵁ W) le_rfl),
    ← ConcreteCategory.comp_apply, ← Scheme.Hom.appLE_eq_app,
    Scheme.Hom.appLE_comp_appLE]

/-- **A section of `𝒪_{X_étale}` over an open of `X` restricts, along the factorization
`AlgebraicGeometry.SmallEtale.objOpenHom`, to its pullback along `h`.**  Both are the image of the
section under the comorphism of `h⁻¹W ↪ T ⟶ X`.

The two composites differ only by that factorization, so the two `appLE` maps agree once their
underlying morphisms do; the transport is by `Eq.subst` on the morphism rather than by rewriting
under `appLE`, whose `≤`-argument is a proof and makes the motive proof-dependent.
`AlgebraicGeometry.Scheme.Hom.appLE_eq_app` is proved by `simp` and not by `rfl`, so the
identification of the global-sections map with `appLE` from the top open is supplied explicitly
rather than left to definitional unfolding. -/
public theorem map_structureSection (W : X.Opens) (a : Γ(X, W)) :
    (commRingStructureSheaf B X hX).obj.map (objOpenHom B hX V W).op
        (((commRingStructureMap B X hX).hom.app (op W)).hom a) =
      ((commRingStructureMap B (objScheme B X hX V)
        (contains_objScheme B X hX V)).hom.app
          (op (objHom B X hX V ⁻¹ᵁ W))).hom
        (((objHom B X hX V).app W).hom a) := by
  have hΓ : (commRingStructureSheaf B X hX).obj.map (objOpenHom B hX V W).op =
      ((toScheme B X hX).map (objOpenHom B hX V W)).appLE ⊤ ⊤ le_rfl :=
    (Scheme.Hom.appLE_eq_app ((toScheme B X hX).map (objOpenHom B hX V W))).symm
  have hk : (toScheme B X hX).map (objOpenHom B hX V W) ≫ W.ι =
      (objHom B X hX V ⁻¹ᵁ W).ι ≫ objHom B X hX V :=
    Eq.trans (toScheme_map_comp_ι B hX W (objOpenHom B hX V W))
      (objToSmallEtaleOver_obj_left_obj_hom_hom B X hX V _)
  have key : ∀ (φ₁ φ₂ : (objHom B X hX V ⁻¹ᵁ W).toScheme ⟶ X), φ₁ = φ₂ →
      ∀ (e₁ : (⊤ : (objHom B X hX V ⁻¹ᵁ W).toScheme.Opens) ≤ φ₁ ⁻¹ᵁ W)
        (e₂ : (⊤ : (objHom B X hX V ⁻¹ᵁ W).toScheme.Opens) ≤ φ₂ ⁻¹ᵁ W),
      φ₁.appLE W ⊤ e₁ = φ₂.appLE W ⊤ e₂ := by
    intro φ₁ φ₂ hφ e₁ e₂
    subst hφ
    rfl
  refine Eq.trans ?_ (objStructureSection_eq_appLE B hX V W a).symm
  refine Eq.trans (congrArg
    ((commRingStructureSheaf B X hX).obj.map (objOpenHom B hX V W).op)
    (structureSection_eq_appLE B hX W a)) ?_
  refine Eq.trans (congrArg (fun m : Γ(W.toScheme, ⊤) ⟶
      Γ((objHom B X hX V ⁻¹ᵁ W).toScheme, ⊤) => ConcreteCategory.hom m _) hΓ) ?_
  refine Eq.trans (ConcreteCategory.comp_apply
    (W.ι.appLE W ⊤ (Scheme.Opens.top_le_ι_preimage (U := W) le_rfl))
    (((toScheme B X hX).map (objOpenHom B hX V W)).appLE ⊤ ⊤ le_rfl) a).symm ?_
  exact congrArg (fun m : Γ(X, W) ⟶ Γ((objHom B X hX V ⁻¹ᵁ W).toScheme, ⊤) =>
    ConcreteCategory.hom m a)
    (Eq.trans (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _) (key _ _ hk _ _))

variable {Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The function pulled back from `Y` restricts to the function pulled back from `Y`.**
`AlgebraicGeometry.SmallEtale.pullbackSection` is the function on `f⁻¹W ⊆ X` pulled back from
`b : Γ(Y, W)`; carrying it along `AlgebraicGeometry.SmallEtale.objOpenHom` gives the function on
`(h ≫ f)⁻¹W ⊆ T` pulled back from `b`, which is the section the localized derivation is asked to
annihilate.

This is `AlgebraicGeometry.SmallEtale.map_structureSection` at the open `f⁻¹W` and the section
pulled back from `b`, the two readings of that section being
`AlgebraicGeometry.Scheme.Hom.comp_app`. -/
public theorem map_pullbackSection (W : Y.Opens) (b : Γ(Y, W)) :
    (commRingStructureSheaf B X hX).obj.map (objOpenHom B hX V (f ⁻¹ᵁ W)).op
        (pullbackSection B hX f W b) =
      ((commRingStructureMap B (objScheme B X hX V)
        (contains_objScheme B X hX V)).hom.app
          (op ((objHom B X hX V ≫ f) ⁻¹ᵁ W))).hom
        (((objHom B X hX V ≫ f).app W).hom b) :=
  Eq.trans (map_structureSection B hX V (f ⁻¹ᵁ W) ((f.app W).hom b))
    (congrArg
      ((commRingStructureMap B (objScheme B X hX V)
        (contains_objScheme B X hX V)).hom.app
          (op ((objHom B X hX V ≫ f) ⁻¹ᵁ W)))
      (ConcreteCategory.comp_apply (f.app W)
        ((objHom B X hX V).app (f ⁻¹ᵁ W)) b).symm)

/-- **The localization along an object of a derivation annihilating the functions pulled back
from `Y` again annihilates the functions pulled back from `Y`**, now along the composite
`T ⟶ X ⟶ Y`.

The function on `(h ≫ f)⁻¹W ⊆ T` pulled back from `b : Γ(Y, W)` is the restriction, along the
factorization `AlgebraicGeometry.SmallEtale.objOpenHom`, of the function on `f⁻¹W ⊆ X` pulled
back from `b`; so this is the compatibility of `D` with restriction applied to the hypothesis. -/
public theorem objZariskiRestrictionData_comorphism_eq_zero
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0)
    (W : Y.Opens) (b : Γ(Y, W)) :
    (objZariskiRestrictionData B hX D V).d
        (((objHom B X hX V ≫ f).app W).hom b) = 0 := by
  refine Eq.trans (objZariskiRestrictionData_d B hX D V _) ?_
  refine Eq.trans (congrArg (D.d (X := op (((objToSmallEtaleOver B X hX V).obj
    ((objHom B X hX V ≫ f) ⁻¹ᵁ W)).left))) (map_pullbackSection B hX V f W b).symm) ?_
  refine Eq.trans
    (D.d_map (objOpenHom B hX V (f ⁻¹ᵁ W)).op (pullbackSection B hX f W b)) ?_
  exact Eq.trans (congrArg _ (hD W b)) (map_zero _)

/-- **The localization of a derivation of `𝒪_{X_étale}` along an object of the small étale site,
as a `Y`-derivation of `𝒪_T`.**  For an object `h : T ⟶ X` of the small étale site of `X` this is
an ordinary derivation of `𝒪_T` relative to `(h ≫ f)⁻¹𝒪_Y`, with values in the sheaf of
`𝒪_T`-modules `W ↦ 𝓕(W ↪ T ⟶ X)`.

It is therefore an admissible input to the universal property of `Ω_{T/Y}`, which is what carries
the Zariski-site information about `D` on `X` to its values over `T`. -/
public noncomputable def objZariskiRestriction
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0) :
    SheafOfModules.SheafDerivation
        (inverseImageStructureMap (objHom B X hX V ≫ f))
      (objZariskiModule B hX F V) :=
  SheafOfModules.ofComorphism (objHom B X hX V ≫ f)
    (objZariskiRestrictionData B hX D V)
    (fun W b => objZariskiRestrictionData_comorphism_eq_zero B hX D V f hD W b)

end Vanishing


section Transport

variable {Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Stacks 04BX at the spelling of an object of the small étale site.**  The structure
morphism `h : T ⟶ X` of an object is étale, so the canonical map `h^*Ω_{X/Y} ⟶ Ω_{T/Y}` of
Stacks 01UV is an isomorphism; this is that isomorphism, taken at the composite `h ≫ f` as the
object presents it. -/
public noncomputable abbrev objDifferentialsIso :
    (Scheme.Modules.pullback (objHom B X hX V)).obj
        (Scheme.Hom.relativeDifferentials f) ≅
      Scheme.Hom.relativeDifferentials (objHom B X hX V ≫ f) :=
  Scheme.Hom.etaleRelativeDifferentialsIso (objHom B X hX V) f
    (objHom B X hX V ≫ f) rfl

/-- **The factorization of the localized derivation through `Ω_{T/Y}`.**  The localization of `D`
along the object is a `Y`-derivation of `𝒪_T`, so the universal property of `Ω_{T/Y}` provides a
unique morphism `Ω_{T/Y} ⟶ 𝓕(· ↪ T ⟶ X)` carrying `d_{T/Y}` to it. -/
public noncomputable def objDesc
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0) :
    Scheme.Hom.relativeDifferentials (objHom B X hX V ≫ f) ⟶
      objZariskiModule B hX F V :=
  (SheafOfModules.universalDerivation_isUniversal
    (inverseImageStructureMap (objHom B X hX V ≫ f))).desc
      (objZariskiRestriction B hX D V f hD)

/-- The universal derivation of `Ω_{T/Y}` followed by `objDesc` is the localized derivation. -/
private theorem postcomp_universalDerivation_objDesc
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0) :
    (SheafOfModules.universalDerivation
      (inverseImageStructureMap (objHom B X hX V ≫ f))).postcomp
        (objDesc B hX D V f hD).val = objZariskiRestriction B hX D V f hD :=
  (SheafOfModules.universalDerivation_isUniversal
    (inverseImageStructureMap (objHom B X hX V ≫ f))).postcomp_desc _

/-- **The factorization transported to `X`.**  Stacks 04BX identifies `Ω_{T/Y}` with
`h^*Ω_{X/Y}`, and the adjunction `h^* ⊣ h_*` turns the factorization above into a morphism
`Ω_{X/Y} ⟶ h_*𝓕(· ↪ T ⟶ X)` of `𝒪_X`-modules.

This is the step which makes the values of `D` over `T` visible on the small Zariski site of `X`,
where the universal property of `Ω_{X/Y}` can be applied to them. -/
public noncomputable def objTransport
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0) :
    Scheme.Hom.relativeDifferentials f ⟶
      (Scheme.Modules.pushforward (objHom B X hX V)).obj
        (objZariskiModule B hX F V) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B X hX V)).homEquiv
      (Scheme.Hom.relativeDifferentials f) (objZariskiModule B hX F V))
    ((objDifferentialsIso B hX V f).hom ≫ objDesc B hX D V f hD)

/-- **The transported factorization, evaluated on the universal differential, sees only the small
Zariski restriction of `D`.**  Over an open `W` of `X` it carries `d_{X/Y} a` to the restriction,
along `AlgebraicGeometry.SmallEtale.objOpenHom`, of the value of the small Zariski restriction of
`D` on `a`.

This is the whole point of the transport, and it is what the universal property of `Ω_{X/Y}` then
turns into a statement about `D` itself: two derivations with the same small Zariski restriction
have the same transported factorization, hence — the transport being injective — the same
localization along every object.

The chain is: the adjunct of a composite splits
(`CategoryTheory.Adjunction.homEquiv_naturality_right`); the first factor is the characterizing
property of the map of Stacks 01UV
(`AlgebraicGeometry.Scheme.Hom.isRelativeDifferentialsMap_etaleRelativeDifferentialsIso`), which
replaces `d_{X/Y} a` by `d_{T/Y}` of the pullback of `a`; the second factor is the universal
property of `Ω_{T/Y}`, which replaces that by the localized derivation; and
`AlgebraicGeometry.SmallEtale.map_structureSection` identifies the pullback of `a` with its
restriction, so the compatibility of `D` with restriction finishes. -/
public theorem objTransport_universalRelativeDerivation
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0)
    (W : X.Opens) (a : Γ(X, W)) :
    (objTransport B hX D V f hD).val.app (op W)
        ((f.universalRelativeDerivation).d a) =
      F.val.map (objOpenHom B hX V W).op
        ((zariskiRestrictionData B hX D).d (X := op W) a) := by
  have hsplit : objTransport B hX D V f hD =
      ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B X hX V)).homEquiv
          (Scheme.Hom.relativeDifferentials f)
          (Scheme.Hom.relativeDifferentials (objHom B X hX V ≫ f)))
            (objDifferentialsIso B hX V f).hom ≫
        (Scheme.Modules.pushforward (objHom B X hX V)).map
          (objDesc B hX D V f hD) :=
    Adjunction.homEquiv_naturality_right _ _ _
  refine Eq.trans (congrArg (fun m : Scheme.Hom.relativeDifferentials f ⟶
      (Scheme.Modules.pushforward (objHom B X hX V)).obj
        (objZariskiModule B hX F V) =>
      m.val.app (op W) ((f.universalRelativeDerivation).d a)) hsplit) ?_
  refine Eq.trans (congrArg
    ((objDesc B hX D V f hD).val.app (op (objHom B X hX V ⁻¹ᵁ W)))
    (Scheme.Hom.isRelativeDifferentialsMap_etaleRelativeDifferentialsIso
      (objHom B X hX V) f (objHom B X hX V ≫ f) rfl W a)) ?_
  refine Eq.trans (Eq.trans (PresheafOfModules.Derivation.postcomp_d_apply
      (SheafOfModules.universalDerivation
        (inverseImageStructureMap (objHom B X hX V ≫ f)))
      (objDesc B hX D V f hD).val (((objHom B X hX V).app W).hom a)).symm
    (PresheafOfModules.Derivation.congr_d
      (postcomp_universalDerivation_objDesc B hX D V f hD)
      (((objHom B X hX V).app W).hom a))) ?_
  refine Eq.trans (objZariskiRestrictionData_d B hX D V
    (W := op (objHom B X hX V ⁻¹ᵁ W)) (((objHom B X hX V).app W).hom a)) ?_
  refine Eq.trans (congrArg (D.d (X := op (((objToSmallEtaleOver B X hX V).obj
    (objHom B X hX V ⁻¹ᵁ W)).left))) (map_structureSection B hX V W a).symm) ?_
  exact D.d_map (objOpenHom B hX V W).op
    (((commRingStructureMap B X hX).hom.app (op W)).hom a)

/-- **Two derivations of `𝒪_{X_étale}` with the same small Zariski restriction have the same
localization along every object of the small étale site.**

By `AlgebraicGeometry.SmallEtale.objTransport_universalRelativeDerivation` the transported
factorizations of the two agree on the universal differential `d_{X/Y}`, so they agree, by the
uniqueness in the universal property of `Ω_{X/Y}`.  The transport is injective — it is an
adjunction bijection followed by precomposition with the isomorphism of Stacks 04BX — so the
factorizations through `Ω_{T/Y}` agree, and those recover the localizations. -/
public theorem objZariskiRestriction_congr
    (D₁ D₂ : PresheafOfModules.Derivation'
      (R := (commRingStructureSheaf B X hX).obj) F.val ψ)
    (hD₁ : ∀ (W : Y.Opens) (b : Γ(Y, W)), D₁.d (pullbackSection B hX f W b) = 0)
    (hD₂ : ∀ (W : Y.Opens) (b : Γ(Y, W)), D₂.d (pullbackSection B hX f W b) = 0)
    (hz : zariskiRestrictionData B hX D₁ = zariskiRestrictionData B hX D₂) :
    objZariskiRestriction B hX D₁ V f hD₁ = objZariskiRestriction B hX D₂ V f hD₂ := by
  have htr : objTransport B hX D₁ V f hD₁ = objTransport B hX D₂ V f hD₂ := by
    refine (SheafOfModules.universalDerivation_isUniversal
      (inverseImageStructureMap f)).hom_ext ?_
    refine PresheafOfModules.Derivation.ext (funext fun W => AddMonoidHom.ext fun a => ?_)
    refine Eq.trans (PresheafOfModules.Derivation.postcomp_d_apply
      (f.universalRelativeDerivation) (objTransport B hX D₁ V f hD₁).val a) ?_
    refine Eq.trans ?_ (PresheafOfModules.Derivation.postcomp_d_apply
      (f.universalRelativeDerivation) (objTransport B hX D₂ V f hD₂).val a).symm
    refine Eq.trans
      (objTransport_universalRelativeDerivation B hX D₁ V f hD₁ W.unop a) ?_
    refine Eq.trans ?_
      (objTransport_universalRelativeDerivation B hX D₂ V f hD₂ W.unop a).symm
    exact congrArg (F.val.map (objOpenHom B hX V W.unop).op)
      (PresheafOfModules.Derivation.congr_d hz a)
  have hcomp : (objDifferentialsIso B hX V f).hom ≫ objDesc B hX D₁ V f hD₁ =
      (objDifferentialsIso B hX V f).hom ≫ objDesc B hX D₂ V f hD₂ :=
    ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B X hX V)).homEquiv
      (Scheme.Hom.relativeDifferentials f) (objZariskiModule B hX F V)).injective htr
  have hdesc : objDesc B hX D₁ V f hD₁ = objDesc B hX D₂ V f hD₂ :=
    (Iso.cancel_iso_hom_left (objDifferentialsIso B hX V f) _ _).mp hcomp
  rw [← postcomp_universalDerivation_objDesc B hX D₁ V f hD₁,
    ← postcomp_universalDerivation_objDesc B hX D₂ V f hD₂, hdesc]

/-- **Two derivations of `𝒪_{X_étale}` with the same small Zariski restriction take the same
value over every object of the form `A ↪ T ⟶ X`.**  This is
`AlgebraicGeometry.SmallEtale.objZariskiRestriction_congr` read on sections. -/
public theorem d_congr_objOpen
    (D₁ D₂ : PresheafOfModules.Derivation'
      (R := (commRingStructureSheaf B X hX).obj) F.val ψ)
    (hD₁ : ∀ (W : Y.Opens) (b : Γ(Y, W)), D₁.d (pullbackSection B hX f W b) = 0)
    (hD₂ : ∀ (W : Y.Opens) (b : Γ(Y, W)), D₂.d (pullbackSection B hX f W b) = 0)
    (hz : zariskiRestrictionData B hX D₁ = zariskiRestrictionData B hX D₂)
    (A : (objScheme B X hX V).Opens) (x : Γ(objScheme B X hX V, A)) :
    D₁.d (X := op (((objToSmallEtaleOver B X hX V).obj A).left))
        (((commRingStructureMap B (objScheme B X hX V)
          (contains_objScheme B X hX V)).hom.app (op A)).hom x) =
      D₂.d (X := op (((objToSmallEtaleOver B X hX V).obj A).left))
        (((commRingStructureMap B (objScheme B X hX V)
          (contains_objScheme B X hX V)).hom.app (op A)).hom x) :=
  PresheafOfModules.Derivation.congr_d
    (objZariskiRestriction_congr B hX V f D₁ D₂ hD₁ hD₂ hz) x

/-- **The object `⊤ ↪ T ⟶ X` is terminal in the slice of the small étale site of `X` at `V`.**
Under `AlgebraicGeometry.SmallEtale.localizationEquivalence` it is the open `⊤` of the small étale
site of `T`, which is terminal there by
`AlgebraicGeometry.SmallEtale.isTerminalOpensObjTop`; the morphism from an arbitrary object is
transported across the equivalence, and there is at most one by
`AlgebraicGeometry.SmallEtale.subsingleton_hom_objToSmallEtaleOver`. -/
public noncomputable def isTerminalObjToSmallEtaleOverTop :
    Limits.IsTerminal ((objToSmallEtaleOver B X hX V).obj ⊤) :=
  Limits.IsTerminal.ofUniqueHom
    (fun Z => ((localizationEquivalence B X hX V).symm.toAdjunction.homEquiv Z
        ((opensToSmallEtale B (objScheme B X hX V)
          (contains_objScheme B X hX V)).obj ⊤))
      ((isTerminalOpensObjTop B (objScheme B X hX V)
        (contains_objScheme B X hX V)).from
          ((localizationEquivalence B X hX V).inverse.obj Z)))
    (fun Z _ => (subsingleton_hom_objToSmallEtaleOver B X hX V Z ⊤).allEq _ _)

/-- **An object of the small étale site of `X` is isomorphic to the object `⊤ ↪ T ⟶ X`.**  Both
are terminal in the slice at `V`, the first as `𝟙 V` and the second by
`AlgebraicGeometry.SmallEtale.isTerminalObjToSmallEtaleOverTop`.

This is the only gap between "the localization of `D` along every object is determined" and "`D`
is determined": the localization at `V` reaches the object `⊤ ↪ T ⟶ X`, whose scheme is the open
subscheme `⊤` of `T` and not `T`, so it is isomorphic to `V` rather than equal to it. -/
public noncomputable def objTopIso :
    V ≅ ((objToSmallEtaleOver B X hX V).obj ⊤).left :=
  (Over.forget V).mapIso
    (Limits.IsTerminal.uniqueUpToIso Over.mkIdTerminal
      (isTerminalObjToSmallEtaleOverTop B hX V))

end Transport

section Determined

variable {Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The existence half of the universal property of `d^a`, and so the other composite of the
invertibility clause of Stacks 04CS.**  The comparison map `c''` of a derivation `D` of
`𝒪_{X_étale}` annihilating the functions pulled back from `Y` carries `d^a` back to `D`.

With `AlgebraicGeometry.SmallEtale.postcomp_associatedDerivation_injective` this says that
`(Ω_{X/Y})^a` together with `d^a` corepresents those derivations.  At
`𝓕 = Ω_{X_étale/Y_étale}` carrying its universal derivation it is the composite `c ≫ c'' = 𝟙` of
the source's proof, the one the source leaves unverified.

Both sides have the same small Zariski restriction: the adjunct of `c''` carries `d_{X/Y}` to the
restriction of `D` by `AlgebraicGeometry.SmallEtale.differentialsComparison_adjunct`, and it
carries `d_{X/Y}` to the restriction of `d^a` postcomposed with `c''` because the comparison map
of `d^a` is the identity.  So `AlgebraicGeometry.SmallEtale.eq_of_zariskiRestrictionData_eq`
applies: a derivation of `𝒪_{X_étale}` is determined by its small Zariski restriction, with no
hypothesis on the functions pulled back from `Y`.

The base of the derivation is the constant presheaf of rings `ℤ`, i.e. only the Leibniz rule,
which is the weakest hypothesis available: a derivation over any base presheaf of rings is in
particular one over `ℤ` with the same values, and `hD` is unchanged by the passage, so this is
the general statement rather than a special case of it. -/
public theorem associatedDerivation_postcomp_differentialsComparison
    (D : PresheafOfModules.Derivation'
      (R := (commRingStructureSheaf B X hX).obj) F.val (siteConstIntMap B hX _))
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0) :
    (associatedDerivation B hX f).postcomp
        (differentialsComparison B hX f D hD).val = D := by
  -- the adjunct of the identity carries `d_{X/Y}` to the small Zariski restriction of `d^a`
  have hunit : (f.universalRelativeDerivation).postcomp
        (((associatedModuleAdjunction B X hX).homEquiv
          (Scheme.Hom.relativeDifferentials f)
          (associatedRelativeDifferentials B hX f))
            (𝟙 (associatedRelativeDifferentials B hX f))).val =
      zariskiRestriction B hX f (associatedDerivation B hX f)
        (associatedDerivation_pullbackSection_eq_zero B hX f) := by
    refine Eq.trans ?_ (differentialsComparison_adjunct B hX f
      (associatedDerivation B hX f)
      (associatedDerivation_pullbackSection_eq_zero B hX f))
    exact congrArg (fun m : associatedRelativeDifferentials B hX f ⟶
        associatedRelativeDifferentials B hX f =>
      (f.universalRelativeDerivation).postcomp
        (((associatedModuleAdjunction B X hX).homEquiv
          (Scheme.Hom.relativeDifferentials f)
          (associatedRelativeDifferentials B hX f)) m).val)
      (differentialsComparison_associatedDerivation B hX f).symm
  -- hence `d^a` followed by `c''` has the small Zariski restriction of `D`
  have hzar : zariskiRestriction B hX f
        ((associatedDerivation B hX f).postcomp
          (differentialsComparison B hX f D hD).val)
        (postcomp_pullbackSection_eq_zero B hX f (associatedDerivation B hX f)
          (associatedDerivation_pullbackSection_eq_zero B hX f)
          (differentialsComparison B hX f D hD)) =
      zariskiRestriction B hX f D hD := by
    refine Eq.trans (zariskiRestriction_postcomp B hX f (associatedDerivation B hX f)
      (associatedDerivation_pullbackSection_eq_zero B hX f)
      (differentialsComparison B hX f D hD)).symm ?_
    refine Eq.trans (congrArg
      (fun E => E.postcomp ((restrictModule B X hX).map
        (differentialsComparison B hX f D hD)).val) hunit.symm) ?_
    refine Eq.trans (SheafOfModules.postcomp_comp_val _ _ _) ?_
    refine Eq.trans ?_ (differentialsComparison_adjunct B hX f D hD)
    exact congrArg (fun m : Scheme.Hom.relativeDifferentials f ⟶
        (restrictModule B X hX).obj F =>
      (f.universalRelativeDerivation).postcomp m.val)
      (Eq.trans ((associatedModuleAdjunction B X hX).homEquiv_naturality_right
        (𝟙 (associatedRelativeDifferentials B hX f))
        (differentialsComparison B hX f D hD)).symm
        (congrArg ((associatedModuleAdjunction B X hX).homEquiv
          (Scheme.Hom.relativeDifferentials f) F) (Category.id_comp _)))
  refine eq_of_zariskiRestrictionData_eq B hX _ D ?_
  exact PresheafOfModules.Derivation.ext (funext fun W => AddMonoidHom.ext fun a =>
    PresheafOfModules.Derivation.congr_d hzar a)

/-- **`(Ω_{X/Y})^a` with `d^a` corepresents the derivations of `𝒪_{X_étale}` which annihilate the
functions pulled back from `Y`.**  This is the universal property the invertibility clause of
Stacks 04CS asserts: existence is
`AlgebraicGeometry.SmallEtale.associatedDerivation_postcomp_differentialsComparison` and
uniqueness is
`AlgebraicGeometry.SmallEtale.postcomp_associatedDerivation_injective`. -/
public theorem existsUnique_postcomp_associatedDerivation
    (D : PresheafOfModules.Derivation'
      (R := (commRingStructureSheaf B X hX).obj) F.val (siteConstIntMap B hX _))
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0) :
    ∃! g : associatedRelativeDifferentials B hX f ⟶ F,
      (associatedDerivation B hX f).postcomp g.val = D :=
  ⟨differentialsComparison B hX f D hD,
    associatedDerivation_postcomp_differentialsComparison B hX f D hD,
    fun g hg => postcomp_associatedDerivation_injective B hX f g
      (differentialsComparison B hX f D hD)
      (Eq.trans hg
        (associatedDerivation_postcomp_differentialsComparison B hX f D hD).symm)⟩

end Determined

end AlgebraicGeometry.SmallEtale

end
