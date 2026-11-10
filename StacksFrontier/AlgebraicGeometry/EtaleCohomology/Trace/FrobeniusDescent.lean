module

public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.TopologicalProperties.RelativeFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.Frobenius
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Iterated

/-!
# Frobenius descent for sheaves on the small étale site

Let `k` be a finite field with `q = p ^ f` elements and let `X` be a scheme over `k`. The
geometric Frobenius `π_X` of `X` is the `f`-fold absolute Frobenius, a morphism over `k`. For a
sheaf `ℱ` on the small étale site of `X` there are canonical isomorphisms `π_X^{-1} ℱ ≅ ℱ` and
`ℱ ≅ (π_X)_* ℱ`.

## Main definitions

* `Stacks.EtaleCohomology.absoluteFrobeniusPowEtaleSiteIso` — base change along the `n`-fold
  absolute Frobenius of a scheme of characteristic `p` is isomorphic to the identity functor of
  its small étale site, for `n ≠ 0`.
* `Stacks.EtaleCohomology.geometricFrobeniusEtaleSiteIso` — the same identification for the
  geometric Frobenius of a scheme over a finite field.
* `Stacks.EtaleCohomology.etaleSheafPushforwardComparison` and
  `Stacks.EtaleCohomology.etaleSheafInverseImageComparison` — the identifications of direct and
  inverse image with the identity functor on sheaves, for a self-map of a scheme whose base
  change is isomorphic to the identity functor of the small étale site.
* `Stacks.EtaleCohomology.geometricFrobeniusPushforwardIso` and
  `Stacks.EtaleCohomology.geometricFrobeniusInverseImageIso` — the two canonical isomorphisms
  of the geometric Frobenius.

## Main results

* `AlgebraicGeometry.nFoldRelativeFrobenius_naturality` — the `n`-fold relative Frobenius is
  natural in the `S`-scheme.
* `AlgebraicGeometry.isIso_nFoldRelativeFrobenius_of_etale` — the `n`-fold relative Frobenius of
  an étale scheme is an isomorphism for `n ≠ 0`.
* `Stacks.EtaleCohomology.absoluteFrobeniusPowEtaleSiteIso_hom_app_left_fst` and
  `Stacks.EtaleCohomology.geometricFrobeniusEtaleSiteIso_hom_app_left_fst` — the component of
  the site identification at `U` has first projection the iterated absolute Frobenius of `U`.
* `Stacks.EtaleCohomology.geometricFrobeniusPushforwardIso_hom_app_hom_app` — the direct-image
  isomorphism is restriction of sections along the inverse of the relative Frobenius.
* `Stacks.EtaleCohomology.sheafAdjunction_unit_comp_etaleSheafInverseImageComparison` — the
  inverse-image isomorphism is the left-adjoint mate of the direct-image isomorphism.

## References

* [Stacks Project, Tag 03SR](https://stacks.math.columbia.edu/tag/03SR)
* [Stacks Project, Tag 03SQ](https://stacks.math.columbia.edu/tag/03SQ)
* [Stacks Project, Tag 0CCG](https://stacks.math.columbia.edu/tag/0CCG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u v w

namespace AlgebraicGeometry

/-- The `n`-fold relative Frobenius is natural in the `S`-scheme: it commutes with base change
of a morphism of `S`-schemes along the `n`-fold absolute Frobenius of `S`. -/
@[sga "3 VIIA 4.1" "special case",
  sga "3 VIIA 4.1.3" "partial",
  sga "4½ Rapport 1.3" "more general",
  sga "5 XV 1.Proposition1" "At n = 1"]
public theorem nFoldRelativeFrobenius_naturality (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (n : ℕ) {X Y : CategoryTheory.Over S} (f : X ⟶ Y) :
    nFoldRelativeFrobenius S p hS n X ≫
        (CategoryTheory.Over.pullback (absoluteFrobeniusPow S p hS n)).map f =
      f ≫ nFoldRelativeFrobenius S p hS n Y := by
  have hnat : ∀ (m : ℕ) {A B : Scheme.{u}} (g : A ⟶ B) (hA : IsInCharacteristic A p)
      (hB : IsInCharacteristic B p),
      absoluteFrobeniusPow A p hA m ≫ g = g ≫ absoluteFrobeniusPow B p hB m := by
    intro m A B g hA hB
    induction m with
    | zero => simp [absoluteFrobeniusPow]
    | succ m ih =>
        simp only [absoluteFrobeniusPow, pow_succ, End.mul_asHom]
        change (absoluteFrobenius A p hA ≫ absoluteFrobeniusPow A p hA m) ≫ g =
          g ≫ (absoluteFrobenius B p hB ≫ absoluteFrobeniusPow B p hB m)
        rw [Category.assoc, ih, ← Category.assoc,
          absoluteFrobenius_naturality g p hA hB, Category.assoc]
  ext
  apply pullback.hom_ext
  · have hlift : ((CategoryTheory.Over.pullback (absoluteFrobeniusPow S p hS n)).map f).left ≫
        pullback.fst Y.hom (absoluteFrobeniusPow S p hS n) =
          pullback.fst X.hom (absoluteFrobeniusPow S p hS n) ≫ f.left :=
      pullback.lift_fst _ _ _
    rw [CategoryTheory.Over.comp_left, Category.assoc, hlift, ← Category.assoc,
      nFoldRelativeFrobenius_fst, CategoryTheory.Over.comp_left, Category.assoc,
      nFoldRelativeFrobenius_fst]
    exact hnat n f.left _ _
  · have hlift : ((CategoryTheory.Over.pullback (absoluteFrobeniusPow S p hS n)).map f).left ≫
        pullback.snd Y.hom (absoluteFrobeniusPow S p hS n) =
          pullback.snd X.hom (absoluteFrobeniusPow S p hS n) :=
      pullback.lift_snd _ _ _
    rw [CategoryTheory.Over.comp_left, Category.assoc, hlift, CategoryTheory.Over.comp_left,
      Category.assoc, nFoldRelativeFrobenius_snd, nFoldRelativeFrobenius_snd,
      CategoryTheory.Over.w]

/-- For an étale `S`-scheme and `n ≠ 0` the `n`-fold relative Frobenius is an isomorphism. -/
@[sga "4½ Fonctions_L 3.4" "more general",
  sga "4½ Rapport 1.2" "special case",
  sga "5 XV 1.Proposition2" "more general"]
public theorem isIso_nFoldRelativeFrobenius_of_etale (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : CategoryTheory.Over S) [Etale X.hom] {n : ℕ} (hn : n ≠ 0) :
    IsIso (nFoldRelativeFrobenius S p hS n X) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [nFoldRelativeFrobenius_eq_successiveRelativeFrobenius]
  induction m with
  | zero =>
      dsimp [successiveRelativeFrobenius]
      infer_instance
  | succ m ih =>
      have : Etale (nFoldFrobeniusTwist S p hS (m + 1) X).hom := by
        dsimp [nFoldFrobeniusTwist]
        infer_instance
      dsimp [successiveRelativeFrobenius]
      exact IsIso.comp_isIso' (ih (Nat.succ_ne_zero m)) inferInstance

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

section SitePow

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p) {n : ℕ}
  (hn : n ≠ 0)

/-- For `n ≠ 0`, the canonical isomorphism between an étale scheme `U` over a scheme `X` of
characteristic `p` and its base change along the `n`-fold absolute Frobenius of `X`. Its
underlying morphism of schemes is the `n`-fold relative Frobenius of `U`, the arrow
`U ⟶ U ×_{X, F_X^n} X` determined by the `n`-fold absolute Frobenius of `U` and the structure
morphism of `U`. -/
@[sga "3 VIIA 4.1.1.1" "more general",
  sga "4½ Fonctions_L 3.4" "more general",
  sga "4½ Rapport 1.2" "special case"]
public def absoluteFrobeniusPowEtaleSiteIsoApp (U : X.Etale) :
    U ≅ (smallEtaleBaseChange (absoluteFrobeniusPow X p hX n)).obj U :=
  have : AlgebraicGeometry.Etale (CategoryTheory.Over.mk U.hom).hom := U.prop
  have := isIso_nFoldRelativeFrobenius_of_etale X p hX (CategoryTheory.Over.mk U.hom) hn
  MorphismProperty.Over.isoMk
    ((CategoryTheory.Over.forget X).mapIso
      (asIso (nFoldRelativeFrobenius X p hX n (CategoryTheory.Over.mk U.hom))))
    (nFoldRelativeFrobenius_snd X p hX n (CategoryTheory.Over.mk U.hom))

/-- The underlying morphism of schemes of the iterated Frobenius comparison at `U` is the
`n`-fold relative Frobenius of `U` over `X`. -/
@[simp]
public lemma absoluteFrobeniusPowEtaleSiteIsoApp_hom_left (U : X.Etale) :
    (absoluteFrobeniusPowEtaleSiteIsoApp X p hX hn U).hom.left =
      (nFoldRelativeFrobenius X p hX n (CategoryTheory.Over.mk U.hom)).left := rfl

/-- For a scheme `X` of characteristic `p` and `n ≠ 0`, base change along the `n`-fold absolute
Frobenius of `X` is isomorphic to the identity functor of the small étale site of `X`. The
isomorphism at an étale `X`-scheme `U` is the `n`-fold relative Frobenius of `U`. -/
@[sga "3 VIIA 4.1.1.1" "more general",
  sga "4½ Fonctions_L 3.4" "more general",
  sga "4½ Rapport 1.2" "special case"]
public def absoluteFrobeniusPowEtaleSiteIso :
    𝟭 X.Etale ≅ smallEtaleBaseChange (absoluteFrobeniusPow X p hX n) :=
  NatIso.ofComponents (absoluteFrobeniusPowEtaleSiteIsoApp X p hX hn) fun {U V} f ↦
    MorphismProperty.Over.Hom.ext (congrArg CommaMorphism.left (nFoldRelativeFrobenius_naturality
      X p hX n (CategoryTheory.Over.homMk f.left (MorphismProperty.Over.w f) :
        CategoryTheory.Over.mk U.hom ⟶ CategoryTheory.Over.mk V.hom))).symm

/-- The component of the iterated Frobenius site isomorphism at `U` followed by the first
projection is the `n`-fold absolute Frobenius of `U`. -/
@[reassoc (attr := simp)]
public lemma absoluteFrobeniusPowEtaleSiteIso_hom_app_left_fst (U : X.Etale) :
    ((absoluteFrobeniusPowEtaleSiteIso X p hX hn).hom.app U).left ≫
        pullback.fst U.hom (absoluteFrobeniusPow X p hX n) =
      absoluteFrobeniusPow U.left p (isInCharacteristic_of_hom U.hom p hX) n :=
  nFoldRelativeFrobenius_fst X p hX n (CategoryTheory.Over.mk U.hom)

/-- The component of the iterated Frobenius site isomorphism at `U` followed by the second
projection is the structure morphism of `U`. -/
@[reassoc (attr := simp)]
public lemma absoluteFrobeniusPowEtaleSiteIso_hom_app_left_snd (U : X.Etale) :
    ((absoluteFrobeniusPowEtaleSiteIso X p hX hn).hom.app U).left ≫
        pullback.snd U.hom (absoluteFrobeniusPow X p hX n) = U.hom :=
  nFoldRelativeFrobenius_snd X p hX n (CategoryTheory.Over.mk U.hom)

end SitePow

section GeometricFrobeniusSite

variable {k : Type u} [Field k] [Fintype k] (X : CategoryTheory.Over (Spec (.of k))) (p f : ℕ)
  [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ f)

/-- The underlying morphism of schemes of the geometric Frobenius is the `f`-fold absolute
Frobenius. -/
public lemma geometricFrobenius_left_eq_absoluteFrobeniusPow :
    (Stacks.Frobenius.geometricFrobenius X p f hcard).left =
      absoluteFrobeniusPow X.left p (Stacks.Frobenius.isInCharacteristic_of_over X) f := rfl

/-- For a scheme `X` over a finite field with `p ^ f` elements, base change along the geometric
Frobenius `π_X` is isomorphic to the identity functor of the small étale site of `X`. The
isomorphism at an étale `X`-scheme `φ : U ⟶ X` is the morphism
`γ_U = (F_U^f, φ) : U ⟶ U ×_{φ, X, π_X} X`. -/
@[sga "4½ Rapport 1.2" "special case"]
public def geometricFrobeniusEtaleSiteIso :
    𝟭 X.left.Etale ≅
      smallEtaleBaseChange (Stacks.Frobenius.geometricFrobenius X p f hcard).left :=
  have hf : f ≠ 0 := by
    rintro rfl
    exact Fintype.one_lt_card.ne' hcard
  absoluteFrobeniusPowEtaleSiteIso X.left p
    (Stacks.Frobenius.isInCharacteristic_of_over X) hf

/-- The component `γ_U` of the geometric Frobenius site isomorphism followed by the first
projection is the `f`-fold absolute Frobenius of `U`. -/
@[reassoc (attr := simp)]
public lemma geometricFrobeniusEtaleSiteIso_hom_app_left_fst (U : X.left.Etale) :
    ((geometricFrobeniusEtaleSiteIso X p f hcard).hom.app U).left ≫
        pullback.fst U.hom (Stacks.Frobenius.geometricFrobenius X p f hcard).left =
      absoluteFrobeniusPow U.left p
        (isInCharacteristic_of_hom U.hom p (Stacks.Frobenius.isInCharacteristic_of_over X)) f :=
  nFoldRelativeFrobenius_fst X.left p (Stacks.Frobenius.isInCharacteristic_of_over X) f
    (CategoryTheory.Over.mk U.hom)

/-- The component `γ_U` of the geometric Frobenius site isomorphism followed by the second
projection is the structure morphism of `U`. -/
@[reassoc (attr := simp)]
public lemma geometricFrobeniusEtaleSiteIso_hom_app_left_snd (U : X.left.Etale) :
    ((geometricFrobeniusEtaleSiteIso X p f hcard).hom.app U).left ≫
        pullback.snd U.hom (Stacks.Frobenius.geometricFrobenius X p f hcard).left = U.hom :=
  nFoldRelativeFrobenius_snd X.left p (Stacks.Frobenius.isInCharacteristic_of_over X) f
    (CategoryTheory.Over.mk U.hom)

end GeometricFrobeniusSite

section SheafComparison

variable (X : Scheme.{u}) (g : X ⟶ X) (e : 𝟭 X.Etale ≅ smallEtaleBaseChange g)
  (A : Type w) [Category.{v} A]

/-- The canonical identification of the direct image of sheaves along base change by
`g : X ⟶ X` with the identity functor, available whenever base change by `g` is isomorphic to
the identity functor of the small étale site. On sections over `U` it is restriction along the
inverse of the component of that isomorphism at `U`. -/
public def etaleSheafPushforwardComparison :
    𝟭 (Sheaf (smallEtaleTopology X) A) ≅
      (smallEtaleBaseChange g).sheafPushforwardContinuous A
        (smallEtaleTopology X) (smallEtaleTopology X) :=
  (Functor.sheafPushforwardContinuousId' e.symm A (smallEtaleTopology X)).symm

/-- The direct-image identification is, on sections over an étale `X`-scheme `U`, the restriction
map of the sheaf along the inverse of the site isomorphism at `U`. -/
@[simp]
public lemma etaleSheafPushforwardComparison_hom_app_hom_app
    (F : Sheaf (smallEtaleTopology X) A) (U : X.Etale) :
    ((etaleSheafPushforwardComparison X g e A).hom.app F).hom.app (op U) =
      F.obj.map (e.inv.app U).op :=
  Category.id_comp _

/-- The canonical identification of the inverse image of sheaves along base change by
`g : X ⟶ X` with the identity functor, available whenever base change by `g` is isomorphic to
the identity functor of the small étale site. It is the left-adjoint mate of
`etaleSheafPushforwardComparison`. -/
public def etaleSheafInverseImageComparison
    [HasWeakSheafify (smallEtaleTopology X) A]
    [∀ F : X.Etaleᵒᵖ ⥤ A, (smallEtaleBaseChange g).op.HasLeftKanExtension F] :
    Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange g) A
        (smallEtaleTopology X) (smallEtaleTopology X) ≅
      𝟭 (Sheaf (smallEtaleTopology X) A) :=
  Adjunction.leftAdjointUniq
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange g) A
      (smallEtaleTopology X) (smallEtaleTopology X))
    (Adjunction.id.ofNatIsoRight (etaleSheafPushforwardComparison X g e A))

/-- The inverse-image identification is the left-adjoint mate of the direct-image
identification: its adjunct under the pullback-pushforward adjunction is the direct-image
isomorphism. -/
public lemma sheafAdjunction_unit_comp_etaleSheafInverseImageComparison
    [HasWeakSheafify (smallEtaleTopology X) A]
    [∀ F : X.Etaleᵒᵖ ⥤ A, (smallEtaleBaseChange g).op.HasLeftKanExtension F]
    (F : Sheaf (smallEtaleTopology X) A) :
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange g) A
          (smallEtaleTopology X) (smallEtaleTopology X)).unit.app F ≫
        ((smallEtaleBaseChange g).sheafPushforwardContinuous A
          (smallEtaleTopology X) (smallEtaleTopology X)).map
            ((etaleSheafInverseImageComparison X g e A).hom.app F) =
      (etaleSheafPushforwardComparison X g e A).hom.app F := by
  simp [etaleSheafInverseImageComparison]

end SheafComparison

section GeometricFrobeniusDescent

variable {k : Type u} [Field k] [Fintype k] (X : CategoryTheory.Over (Spec (.of k))) (p f : ℕ)
  [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ f) (A : Type w) [Category.{v} A]

/-- Let `k` be a finite field with `p ^ f` elements, let `X` be a scheme over `k` and let `π_X` be
the geometric Frobenius of `X`. Then a sheaf `ℱ` on the small étale site of `X` is canonically
isomorphic to its direct image `(π_X)_* ℱ`, naturally in `ℱ`.
On sections over an étale `φ : U ⟶ X` the isomorphism
`ℱ(U) ⟶ (π_X)_* ℱ(U) = ℱ(U ×_{φ, X, π_X} X)` is restriction along the inverse of
`γ_U = (F_U^f, φ)`. -/
@[stacks 03SR "direct image", sga "5 XII 7.3" "more general"]
public def geometricFrobeniusPushforwardIso :
    𝟭 (Sheaf (smallEtaleTopology X.left) A) ≅
      (smallEtaleBaseChange
          (Stacks.Frobenius.geometricFrobenius X p f hcard).left).sheafPushforwardContinuous A
        (smallEtaleTopology X.left) (smallEtaleTopology X.left) :=
  etaleSheafPushforwardComparison X.left
    (Stacks.Frobenius.geometricFrobenius X p f hcard).left
    (geometricFrobeniusEtaleSiteIso X p f hcard) A

/-- On sections over an étale `X`-scheme `U` the direct-image isomorphism of the geometric
Frobenius is the restriction map of the sheaf along `γ_U^{-1}`. -/
@[simp, sga "5 XII 7.3" "Section formula"]
public lemma geometricFrobeniusPushforwardIso_hom_app_hom_app
    (F : Sheaf (smallEtaleTopology X.left) A) (U : X.left.Etale) :
    ((geometricFrobeniusPushforwardIso X p f hcard A).hom.app F).hom.app (op U) =
      F.obj.map ((geometricFrobeniusEtaleSiteIso X p f hcard).inv.app U).op :=
  etaleSheafPushforwardComparison_hom_app_hom_app X.left
    (Stacks.Frobenius.geometricFrobenius X p f hcard).left
    (geometricFrobeniusEtaleSiteIso X p f hcard) A F U

/-- Let `k` be a finite field with `p ^ f` elements, let `X` be a scheme over `k` and let `π_X` be
the geometric Frobenius of `X`. Then the inverse image `π_X^{-1} ℱ` of a sheaf `ℱ` on the small
étale site of `X` is canonically isomorphic to `ℱ`, naturally in `ℱ`. The isomorphism is the
left-adjoint mate of `geometricFrobeniusPushforwardIso`. -/
@[stacks 03SR "inverse image, for coefficients admitting sheafification and left Kan extensions"]
public def geometricFrobeniusInverseImageIso
    [HasWeakSheafify (smallEtaleTopology X.left) A]
    [∀ F : X.left.Etaleᵒᵖ ⥤ A,
      (smallEtaleBaseChange
        (Stacks.Frobenius.geometricFrobenius X p f hcard).left).op.HasLeftKanExtension F] :
    Functor.sheafPullbackConstruction.sheafPullback
        (smallEtaleBaseChange (Stacks.Frobenius.geometricFrobenius X p f hcard).left) A
        (smallEtaleTopology X.left) (smallEtaleTopology X.left) ≅
      𝟭 (Sheaf (smallEtaleTopology X.left) A) :=
  etaleSheafInverseImageComparison X.left
    (Stacks.Frobenius.geometricFrobenius X p f hcard).left
    (geometricFrobeniusEtaleSiteIso X p f hcard) A

end GeometricFrobeniusDescent

end Stacks.EtaleCohomology

end
