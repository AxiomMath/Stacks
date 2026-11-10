module

public import
  StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.GlobalSectionsCompleteDevissage
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange

/-!
# Shrinking an affine elementary étale square to a basic open of the base

Let `f : X ⟶ S`, let `V` be an étale neighbourhood of `(S, s)` and `U` one of `(X, x)`, and let
`h : U.scheme ⟶ V.scheme` be a morphism over `f` matching the distinguished points. For a global
function `a` on `V.scheme` which does not vanish at the distinguished point, restricting `V` to
`D(a)` and `U` to `D(h^♯ a)` yields a square of the same kind: both restricted neighbourhoods are
étale neighbourhoods of the same points, they are elementary if the original ones were, they are
affine if the original ones were, and the restricted vertical morphism is again a morphism over
`f` matching the distinguished points.

For a quasi-coherent module `F` on `X` the global sections of the pullback of `F` to `D(h^♯ a)`
are the localization of the global sections of the pullback to `U.scheme` away from `h^♯ a`, and
over the base ring `Γ(V.scheme, ⊤)` this is the localization away from `a` itself.

## Main definitions

* `AlgebraicGeometry.EtaleNeighborhood.restrictOpen` restricts an étale neighbourhood to an open
  subscheme through its distinguished point.
* `AlgebraicGeometry.restrictBasicOpenHom` is the vertical morphism of the shrunk square.
* `AlgebraicGeometry.pullbackBasicOpenSectionsMap` is the restriction map from the global sections
  of a pullback to the global sections of its pullback to a basic open.

## Main results

* `AlgebraicGeometry.EtaleNeighborhood.IsElementary.restrictOpen`: restriction to an open through
  the distinguished point preserves elementariness.
* `AlgebraicGeometry.restrictBasicOpen_isAffineElementaryEtaleSquare`: the affine elementary étale
  square survives the shrinking, with all of its data.
* `AlgebraicGeometry.isLocalizedModule_pullbackBasicOpenSectionsMap` and
  `AlgebraicGeometry.isLocalizedModule_pullbackBasicOpenSectionsMap_base`: the sections of the
  pullback to a basic open are the localization of the sections, over the ring of functions on
  the upper scheme and over the ring of functions on the base respectively.

## Implementation notes

The ring of global functions on an open subscheme `W` of `Y` is definitionally `Γ(Y, W.ι ''ᵁ ⊤)`
and the restriction of an `𝒪_Y`-module along `W.ι` has definitionally the same sections, with the
same scalar multiplication, because `Scheme.Opens.ι_appIso` is the identity. The opens
`W.ι ''ᵁ ⊤` is therefore used in place of `W` throughout, which avoids transporting sections
along `Scheme.Opens.ι_image_top`.

## References

* [Stacks Project, Tag 05ID](https://stacks.math.columbia.edu/tag/05ID)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace AlgebraicGeometry

namespace EtaleNeighborhood

variable {S : Scheme.{u}} {s : S}

/-- An open subscheme of an étale neighbourhood containing the distinguished point is again an
étale neighbourhood of the same point of the base, via the composite structure morphism. -/
def restrictOpen (U : EtaleNeighborhood S s) (W : U.scheme.Opens) (hW : U.point ∈ W) :
    EtaleNeighborhood S s where
  scheme := W.toScheme
  point := ⟨U.point, hW⟩
  toBase := W.ι ≫ U.toBase
  map_point := U.map_point

/-- The underlying scheme of `U.restrictOpen W hW` is the open subscheme `W`. -/
@[simp]
lemma restrictOpen_scheme (U : EtaleNeighborhood S s) (W : U.scheme.Opens) (hW : U.point ∈ W) :
    (U.restrictOpen W hW).scheme = W.toScheme := rfl

/-- The distinguished point of `U.restrictOpen W hW` is `U.point`, viewed as a point of `W`. -/
@[simp]
lemma restrictOpen_point (U : EtaleNeighborhood S s) (W : U.scheme.Opens) (hW : U.point ∈ W) :
    (U.restrictOpen W hW).point = ⟨U.point, hW⟩ := rfl

/-- The structure morphism of `U.restrictOpen W hW` is the inclusion of `W` followed by
`U.toBase`. -/
@[simp]
lemma restrictOpen_toBase (U : EtaleNeighborhood S s) (W : U.scheme.Opens) (hW : U.point ∈ W) :
    (U.restrictOpen W hW).toBase = W.ι ≫ U.toBase := rfl

/-- Restricting an elementary étale neighbourhood to an open subscheme through its distinguished
point leaves it elementary. -/
theorem IsElementary.restrictOpen {U : EtaleNeighborhood S s} (hU : U.IsElementary)
    (W : U.scheme.Opens) (hW : U.point ∈ W) : (U.restrictOpen W hW).IsElementary := by
  rw [isElementary_iff]
  exact isIso_residueFieldMap_opens_comp U hU W ⟨U.point, hW⟩ rfl

/-- A basic open of an affine étale neighbourhood is an affine étale neighbourhood. -/
theorem isAffine_restrictOpen_basicOpen (U : EtaleNeighborhood S s) [IsAffine U.scheme]
    (a : Γ(U.scheme, ⊤)) (hW : U.point ∈ U.scheme.basicOpen a) :
    IsAffine (U.restrictOpen (U.scheme.basicOpen a) hW).scheme :=
  (isAffineOpen_top U.scheme).basicOpen a

/-- The global functions on a basic open of an affine étale neighbourhood are the localization of
its global functions away from the defining function. -/
theorem isLocalization_away_restrictOpen_basicOpen (U : EtaleNeighborhood S s) [IsAffine U.scheme]
    (a : Γ(U.scheme, ⊤)) (hW : U.point ∈ U.scheme.basicOpen a) :
    letI : Algebra Γ(U.scheme, ⊤) Γ((U.restrictOpen (U.scheme.basicOpen a) hW).scheme, ⊤) :=
      (U.scheme.basicOpen a).ι.appTop.hom.toAlgebra
    IsLocalization.Away a Γ((U.restrictOpen (U.scheme.basicOpen a) hW).scheme, ⊤) :=
  Γ_restrict_isLocalization U.scheme a

end EtaleNeighborhood

section Square

/-- If `h y = z` and the global function `a` on `Z` does not vanish at `z`, then `y` lies in the
basic open of `Y` cut out by the pullback `h^♯ a`. -/
theorem mem_basicOpen_appTop {Y Z : Scheme.{u}} (h : Y ⟶ Z) {y : Y} {z : Z} (hyz : h y = z)
    (a : Γ(Z, ⊤)) (ha : z ∈ Z.basicOpen a) : y ∈ Y.basicOpen (h.appTop.hom a) := by
  rw [← Scheme.preimage_basicOpen_top]
  change h y ∈ Z.basicOpen a
  rw [hyz]
  exact ha

/-- The vertical morphism of an étale square, restricted to the basic open of a function on the
base and to its preimage. -/
def restrictBasicOpenHom {Y Z : Scheme.{u}} (h : Y ⟶ Z) (a : Γ(Z, ⊤)) :
    (Y.basicOpen (h.appTop.hom a)).toScheme ⟶ (Z.basicOpen a).toScheme :=
  h.resLE _ _ (Scheme.preimage_basicOpen_top h a).ge

/-- The restricted morphism followed by the inclusion of `D(a)` is the inclusion of `D(h^♯ a)`
followed by `h`. -/
lemma restrictBasicOpenHom_comp_ι {Y Z : Scheme.{u}} (h : Y ⟶ Z) (a : Γ(Z, ⊤)) :
    restrictBasicOpenHom h a ≫ (Z.basicOpen a).ι =
      (Y.basicOpen (h.appTop.hom a)).ι ≫ h :=
  Scheme.Hom.resLE_comp_ι h _

/-- The restricted morphism acts on points as `h`. -/
@[simp]
lemma restrictBasicOpenHom_apply {Y Z : Scheme.{u}} (h : Y ⟶ Z) (a : Γ(Z, ⊤))
    (y : (Y.basicOpen (h.appTop.hom a)).toScheme) :
    (restrictBasicOpenHom h a y).1 = h y.1 :=
  Scheme.Hom.coe_resLE_apply h _ y

/-- Restricting a global function on `Z` to `D(a)` and pulling it back along the restricted
morphism is pulling it back along `h` and restricting to `D(h^♯ a)`. -/
lemma appTop_comp_restrictBasicOpenHom_appTop {Y Z : Scheme.{u}} (h : Y ⟶ Z) (a : Γ(Z, ⊤)) :
    (Z.basicOpen a).ι.appTop ≫ (restrictBasicOpenHom h a).appTop =
      h.appTop ≫ (Y.basicOpen (h.appTop.hom a)).ι.appTop := by
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, restrictBasicOpenHom_comp_ι]

variable {X S : Scheme.{u}} (f : X ⟶ S) {x : X} {V : EtaleNeighborhood S (f x)}

/-- **The affine elementary étale square survives shrinking the base to a basic open.** Let `V`
and `U` be affine elementary étale neighbourhoods of `(S, f x)` and `(X, x)` joined by a morphism
`h` over `f` matching the distinguished points, and let `a` be a global function on `V.scheme`
not vanishing at `V.point`. Then `V` restricted to `D(a)` and `U` restricted to `D(h^♯ a)` are
again affine elementary étale neighbourhoods of the same two points, and the restriction of `h`
is again a morphism over `f` matching the distinguished points. -/
theorem restrictBasicOpen_isAffineElementaryEtaleSquare {U : EtaleNeighborhood X x}
    [IsAffine V.scheme] [IsAffine U.scheme] (hV : V.IsElementary) (hU : U.IsElementary)
    (h : U.scheme ⟶ V.scheme) (hsq : h ≫ V.toBase = U.toBase ≫ f) (hpt : h U.point = V.point)
    (a : Γ(V.scheme, ⊤)) (ha : V.point ∈ V.scheme.basicOpen a) :
    letI V' := V.restrictOpen (V.scheme.basicOpen a) ha
    letI U' := U.restrictOpen (U.scheme.basicOpen (h.appTop.hom a))
      (mem_basicOpen_appTop h hpt a ha)
    V'.IsElementary ∧ U'.IsElementary ∧ IsAffine V'.scheme ∧ IsAffine U'.scheme ∧
      restrictBasicOpenHom h a ≫ V'.toBase = U'.toBase ≫ f ∧
      restrictBasicOpenHom h a U'.point = V'.point := by
  refine ⟨hV.restrictOpen _ ha, hU.restrictOpen _ _,
    V.isAffine_restrictOpen_basicOpen a ha, U.isAffine_restrictOpen_basicOpen _ _, ?_, ?_⟩
  · change restrictBasicOpenHom h a ≫ (V.scheme.basicOpen a).ι ≫ V.toBase =
      ((U.scheme.basicOpen (h.appTop.hom a)).ι ≫ U.toBase) ≫ f
    rw [← Category.assoc, restrictBasicOpenHom_comp_ι, Category.assoc, Category.assoc, ← hsq]
  · exact Subtype.ext ((restrictBasicOpenHom_apply h a _).trans hpt)

/-- The restriction of the vertical morphism of a square of finite type is of finite type. -/
instance locallyOfFiniteType_restrictBasicOpenHom {Y Z : Scheme.{u}} (h : Y ⟶ Z)
    [LocallyOfFiniteType h] (a : Γ(Z, ⊤)) :
    LocallyOfFiniteType (restrictBasicOpenHom h a) :=
  inferInstanceAs (LocallyOfFiniteType (h.resLE _ _ _))

end Square

section Sections

variable {Y Z : Scheme.{u}} (g : Y ⟶ Z) (F : Z.Modules) (b : Γ(Y, ⊤))

/-- Scalar multiplication on the global sections of the restriction of a module to an open
subscheme is scalar multiplication on its sections over that open. -/
lemma smul_restrictOpens_apply {Y : Scheme.{u}} (W : Y.Opens) (M : Y.Modules)
    (r : Γ(W.toScheme, ⊤)) (t : Γ(M.restrict W.ι, ⊤)) :
    (Scheme.Modules.smul (M := M.restrict W.ι) (U := ⊤) r).asHom.hom t =
      (Scheme.Modules.smul (M := M) (U := W.ι ''ᵁ ⊤) r).asHom.hom t := by
  rw [show Scheme.Modules.smul (M := M.restrict W.ι) (U := ⊤) r =
      Scheme.Modules.smul (M := M) (U := W.ι ''ᵁ ⊤) ((W.ι.appIso ⊤).inv r) from rfl,
    Scheme.Opens.ι_appIso]
  rfl

/-- The pullback of a module to an open subscheme of `Y` along a morphism `g : Y ⟶ Z` is the
restriction to that open of the pullback along `g`. -/
def pullbackRestrictIso (W : Y.Opens) :
    ((Scheme.Modules.pullback g).obj F).restrict W.ι ≅
      (Scheme.Modules.pullback (W.ι ≫ g)).obj F :=
  (Scheme.Modules.restrictFunctorIsoPullback W.ι).app _ ≪≫
    (Scheme.Modules.pullbackComp W.ι g).app F

/-- The `Γ(Y, ⊤)`-module structure on the global sections of the pullback of `F` to a basic open
of `Y`, obtained by restricting functions from `Y`. -/
@[instance_reducible]
def modulePullbackBasicOpenSections :
    Module Γ(Y, ⊤) Γ((Scheme.Modules.pullback ((Y.basicOpen b).ι ≫ g)).obj F, ⊤) :=
  Module.compHom _ (Y.basicOpen b).ι.appTop.hom

/-- Sections of the pullback of `F` to a basic open `D(b)` of `Y` are the sections over `D(b)` of
the pullback of `F` to `Y`. -/
def pullbackBasicOpenSectionsEquiv :
    letI := moduleOfLE ((Scheme.Modules.pullback g).obj F)
      (le_top (a := (Y.basicOpen b).ι ''ᵁ ⊤))
    letI := modulePullbackBasicOpenSections g F b
    Γ((Scheme.Modules.pullback g).obj F, (Y.basicOpen b).ι ''ᵁ ⊤) ≃ₗ[Γ(Y, ⊤)]
      Γ((Scheme.Modules.pullback ((Y.basicOpen b).ι ≫ g)).obj F, ⊤) :=
  letI := moduleOfLE ((Scheme.Modules.pullback g).obj F)
    (le_top (a := (Y.basicOpen b).ι ''ᵁ ⊤))
  letI := modulePullbackBasicOpenSections g F b
  { toFun := (pullbackRestrictIso g F (Y.basicOpen b)).hom.app ⊤
    invFun := (pullbackRestrictIso g F (Y.basicOpen b)).inv.app ⊤
    map_add' := map_add _
    map_smul' := fun r t ↦ by
      refine Eq.trans (congrArg ((pullbackRestrictIso g F (Y.basicOpen b)).hom.app ⊤) ?_)
        (Scheme.Modules.Hom.app_smul (pullbackRestrictIso g F (Y.basicOpen b)).hom
          ((Y.basicOpen b).ι.appTop.hom r) t)
      exact (smul_restrictOpens_apply (Y.basicOpen b) _
        ((Y.basicOpen b).ι.appTop.hom r) t).symm
    left_inv := fun t ↦ by
      have h : ((pullbackRestrictIso g F (Y.basicOpen b)).hom ≫
          (pullbackRestrictIso g F (Y.basicOpen b)).inv).app ⊤ = 𝟙 _ := by
        rw [Iso.hom_inv_id, Scheme.Modules.Hom.id_app]
      exact congr($h t)
    right_inv := fun t ↦ by
      have h : ((pullbackRestrictIso g F (Y.basicOpen b)).inv ≫
          (pullbackRestrictIso g F (Y.basicOpen b)).hom).app ⊤ = 𝟙 _ := by
        rw [Iso.inv_hom_id, Scheme.Modules.Hom.id_app]
      exact congr($h t) }

/-- Restriction of global sections of the pullback of `F` to `Y` to global sections of the
pullback of `F` to the basic open `D(b)`, as a `Γ(Y, ⊤)`-linear map. -/
def pullbackBasicOpenSectionsMap :
    letI := modulePullbackBasicOpenSections g F b
    Γ((Scheme.Modules.pullback g).obj F, ⊤) →ₗ[Γ(Y, ⊤)]
      Γ((Scheme.Modules.pullback ((Y.basicOpen b).ι ≫ g)).obj F, ⊤) :=
  letI := modulePullbackBasicOpenSections g F b
  ↑(pullbackBasicOpenSectionsEquiv g F b) ∘ₗ
    restrictₗ ((Scheme.Modules.pullback g).obj F) (le_top (a := (Y.basicOpen b).ι ''ᵁ ⊤))

/-- **Sections localize.** For `Y` affine and `F` with quasi-coherent pullback to `Y`, the global
sections of the pullback of `F` to the basic open `D(b)` are the localization away from `b` of the
global sections of the pullback of `F` to `Y`. -/
theorem isLocalizedModule_pullbackBasicOpenSectionsMap [IsAffine Y]
    [((Scheme.Modules.pullback g).obj F).IsQuasicoherent] :
    letI := modulePullbackBasicOpenSections g F b
    IsLocalizedModule.Away b (pullbackBasicOpenSectionsMap g F b) := by
  let := moduleOfLE ((Scheme.Modules.pullback g).obj F)
    (le_top (a := (Y.basicOpen b).ι ''ᵁ ⊤))
  let := modulePullbackBasicOpenSections g F b
  have : IsLocalizedModule.Away b
      (restrictₗ ((Scheme.Modules.pullback g).obj F)
        (le_top (a := (Y.basicOpen b).ι ''ᵁ ⊤))) :=
    isLocalizedModule_restrictₗ _ (isAffineOpen_top Y) b (Scheme.Opens.ι_image_top _) le_top
  exact IsLocalizedModule.of_linearEquiv (Submonoid.powers b)
    (restrictₗ ((Scheme.Modules.pullback g).obj F) (le_top (a := (Y.basicOpen b).ι ''ᵁ ⊤)))
    (pullbackBasicOpenSectionsEquiv g F b)

end Sections

section SectionsBase

variable {X S : Scheme.{u}} {x : X}

/-- **Sections localize over the base.** Read over the ring of global functions on the base
neighbourhood `V`, the global sections of the pullback of `F` to `D(h^♯ a)` are the localization
away from `a` of the global sections of the pullback of `F` to `U.scheme`. Together with
`AlgebraicGeometry.Γ_restrict_isLocalization`, which identifies `Γ(D(a), ⊤)` with the
localization of `Γ(V.scheme, ⊤)` away from `a`, this is what lets a projectivity statement over
the localized base ring be read as one over `Γ(D(a), ⊤)`. -/
theorem isLocalizedModule_pullbackBasicOpenSectionsMap_base (f : X ⟶ S)
    {V : EtaleNeighborhood S (f x)}
    {U : EtaleNeighborhood X x} [IsAffine U.scheme] (h : U.scheme ⟶ V.scheme) (F : X.Modules)
    [((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent] (a : Γ(V.scheme, ⊤)) :
    letI : Algebra Γ(V.scheme, ⊤) Γ(U.scheme, ⊤) := h.appTop.hom.toAlgebra
    letI : Module Γ(V.scheme, ⊤) Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) :=
      Module.compHom _ h.appTop.hom
    letI := modulePullbackBasicOpenSections U.toBase F (h.appTop.hom a)
    letI : Module Γ(V.scheme, ⊤)
        Γ((Scheme.Modules.pullback
          ((U.scheme.basicOpen (h.appTop.hom a)).ι ≫ U.toBase)).obj F, ⊤) :=
      Module.compHom _ ((U.scheme.basicOpen (h.appTop.hom a)).ι.appTop.hom.comp h.appTop.hom)
    have : IsScalarTower Γ(V.scheme, ⊤) Γ(U.scheme, ⊤)
        Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) :=
      .of_algebraMap_smul fun _ _ ↦ rfl
    have : IsScalarTower Γ(V.scheme, ⊤) Γ(U.scheme, ⊤)
        Γ((Scheme.Modules.pullback
          ((U.scheme.basicOpen (h.appTop.hom a)).ι ≫ U.toBase)).obj F, ⊤) :=
      .of_algebraMap_smul fun _ _ ↦ rfl
    IsLocalizedModule.Away a
      ((pullbackBasicOpenSectionsMap U.toBase F (h.appTop.hom a)).restrictScalars
        Γ(V.scheme, ⊤)) := by
  let : Algebra Γ(V.scheme, ⊤) Γ(U.scheme, ⊤) := h.appTop.hom.toAlgebra
  let : Module Γ(V.scheme, ⊤) Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) :=
    Module.compHom _ h.appTop.hom
  let := modulePullbackBasicOpenSections U.toBase F (h.appTop.hom a)
  let : Module Γ(V.scheme, ⊤)
      Γ((Scheme.Modules.pullback
        ((U.scheme.basicOpen (h.appTop.hom a)).ι ≫ U.toBase)).obj F, ⊤) :=
    Module.compHom _ ((U.scheme.basicOpen (h.appTop.hom a)).ι.appTop.hom.comp h.appTop.hom)
  have : IsScalarTower Γ(V.scheme, ⊤) Γ(U.scheme, ⊤)
      Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower Γ(V.scheme, ⊤) Γ(U.scheme, ⊤)
      Γ((Scheme.Modules.pullback
        ((U.scheme.basicOpen (h.appTop.hom a)).ι ≫ U.toBase)).obj F, ⊤) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsLocalizedModule (.powers (algebraMap Γ(V.scheme, ⊤) Γ(U.scheme, ⊤) a))
      (pullbackBasicOpenSectionsMap U.toBase F (h.appTop.hom a)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact isLocalizedModule_pullbackBasicOpenSectionsMap U.toBase F (h.appTop.hom a)
  exact IsLocalizedModule.restrictScalars_powers a _

end SectionsBase

end AlgebraicGeometry

end
