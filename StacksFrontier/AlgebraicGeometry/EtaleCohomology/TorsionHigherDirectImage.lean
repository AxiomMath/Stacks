module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.Algebra.Homology.DerivedCategory.WeakSerreClassRightDerivedFunctorPlus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionEtaleCohomologyOverAnObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.AbelianHigherDirectImageSheafification
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
import StacksCore.Tactic.StacksAttribute

/-!
# Torsion higher direct images on the small étale site

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes. [Stacks, Tag 0DDD]
says that

1. if `F` is a torsion abelian sheaf on `X_étale`, then `R^n f_* F` is a torsion abelian sheaf on
   `Y_étale` for every `n`; and
2. if `K` lies in `D^+(X_étale)` and has torsion cohomology sheaves, then `Rf_* K` is an object of
   `D^+(Y_étale)` whose cohomology sheaves are torsion abelian sheaves.

Part (1) is the source's proof. The higher direct image `R^n f_* F` is the sheafification of the
cohomology presheaf `V ↦ H^n(V ×_Y X, F)` ([Stacks, Tag 072W]), and on an *affine* `V` the scheme
`V ×_Y X` is quasi-compact and quasi-separated, so [Stacks, Tag 0DDC] (1) makes that group
torsion. Affine objects generate the small étale topology, so the cohomology presheaf is locally
torsion, and the sheafification of a locally torsion presheaf is a torsion abelian sheaf.

Part (2) is deduced from part (1) by dévissage rather than by repeating the source's argument
with [Stacks, Tag 0D6I] in place of Tag 072W. The spectral sequence of a Cartan--Eilenberg
resolution has `E_2^{p,q} = R^p f_* H^q(K)`, which part (1) places in the torsion abelian
sheaves; those form a Serre subcategory ([Stacks, Tag 0DD7]), hence a weak Serre class, and a
weak Serre class containing a page of a convergent bounded spectral sequence contains the
abutment, which is `H^{p+q}(Rf_* K)`. That dévissage is
`CategoryTheory.Functor.derivedCategoryBPlus_rightDerivedFunctorPlus_obj`, proved for an
arbitrary additive functor.

The first half of this file isolates the sheafification argument of part (1), for an arbitrary
site. Torsion of an abelian sheaf is the local condition of
`Stacks.Torsion.torsionSheafProperty` ([Stacks, Tag 0DD7]);
`Stacks.Torsion.IsLocallyTorsion` is the same condition read on a presheaf, and a sheaf is
torsion exactly when its underlying presheaf is locally torsion.

## Main definitions

* `Stacks.Torsion.IsLocallyTorsion`: a presheaf of abelian groups is locally torsion when every
  section is, on a covering sieve, annihilated by a positive integer.
* `Stacks.Torsion.torsionSieve`: the largest sieve on which a given section is pointwise
  annihilated by a positive integer.
* `Stacks.EtaleCohomology.smallEtaleDirectImageAb`: the direct image `f_*` on abelian sheaves for
  the small étale sites, along base change.
* `Stacks.EtaleCohomology.smallEtaleCohomologyPresheaf`: the cohomology presheaf
  `V ↦ H^•(V ×_Y X, -)` on the small étale site of `Y`.
* `Stacks.EtaleCohomology.smallEtaleDerivedDirectImage`: `Rf_*` on bounded-below derived
  categories of abelian étale sheaves.

## Main results

* `Stacks.Torsion.isLocallyTorsion_of_isLocallySurjective`: local torsion passes along a locally
  surjective map of presheaves.
* `Stacks.Torsion.isLocallyTorsion_of_isCoverDense`: local torsion is tested on a cover-dense
  family of objects.
* `Stacks.Torsion.torsionSheafProperty_sheafify`: the sheafification of a locally torsion
  presheaf is a torsion abelian sheaf.
* `Stacks.EtaleCohomology.torsionSheafProperty_rightDerived_smallEtaleDirectImageAb`: part (1) of
  Tag 0DDD.
* `Stacks.EtaleCohomology.torsionSheafProperty_smallEtaleDirectImageAb`: part (1) of Tag 0DDD in
  degree zero, read on `f_*` itself.
* `Stacks.EtaleCohomology.torsionCohomologyProperty_smallEtaleDerivedDirectImage`: the torsion
  half of part (2) of Tag 0DDD.

## Implementation notes

**The inputs.** Tag 072W for abelian sheaves is
`Stacks.Cohomology.SheafifiedHigherDirectImage.rightDerivedPushforwardIso`, together with the
identification of the values of the cohomology presheaf. Tag 0DDC (1) is applied to the objects
`V ×_Y X` of the small étale site of `X` for affine `V`, in the form
`Stacks.EtaleCohomology.exists_nsmul_eq_zero_rightDerived_sectionsOverObject`: cohomology over an
object of the small étale site of `X` is the étale cohomology of its underlying *scheme*, which
for `V` affine is quasi-compact and quasi-separated by
`compactSpace_smallEtaleBaseChange_obj` and `quasiSeparatedSpace_smallEtaleBaseChange_obj`. These
last two are the "restrict to affine `V`" step of the source's proof, and they are what the
quasi-compactness and quasi-separatedness of `f` are used for.

**The bounded-below half of part (2).** `Rf_*` on bounded-below derived categories is Mathlib's
`CategoryTheory.Functor.rightDerivedFunctorPlus`, whose codomain is `DerivedCategory.Plus` of the
target. So "`Rf_* K` is an object of `D^+(Y_étale)`" is the type of
`smallEtaleDerivedDirectImage`, and it is that definition, rather than a theorem, which states
that clause of the tag.

**Universes.** The coefficients are `AddCommGrpCat.{max (u + 1) v}` for a scheme universe `u` and
arbitrary `v`, as elsewhere in the étale abelian development: the small étale site of
`X : Scheme.{u}` has its objects in `Type (u + 1)` and its morphisms in `Type u`, so this is the
first universe in which sheafification, enough injectives and local bijectivity are all
available, and at it they are all instances.

## References

* [Stacks Project, Tag 0DDD](https://stacks.math.columbia.edu/tag/0DDD)
* [Stacks Project, Tag 0DDC](https://stacks.math.columbia.edu/tag/0DDC)
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Stacks.Torsion

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section LocallyTorsion

/-- A positive integer killing `a` kills any image `b = φ a` of it under a morphism `φ`. -/
private theorem nsmul_eq_zero_of_apply_eq {A B : AddCommGrpCat.{w}} (φ : A ⟶ B) {a : A} {b : B}
    (h : φ a = b) {n : ℕ} (ha : n • a = 0) : n • b = 0 := by
  rw [← h, ← _root_.map_nsmul, ha, map_zero]

/-- The sieve of those arrows `g : V ⟶ U` along which the restriction of a section `y` of a
presheaf of abelian groups is annihilated by a positive integer. It is a sieve because the
integer that kills a restriction kills every further restriction of it. -/
public def torsionSieve (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) {U : C} (y : P.obj (op U)) : Sieve U where
  arrows V g := ∃ n : ℕ, 0 < n ∧ n • P.map g.op y = 0
  downward_closed := by
    intro V W g hg h
    obtain ⟨n, hn, hg⟩ := hg
    refine ⟨n, hn, ?_⟩
    have hres : P.map (h ≫ g).op y = P.map h.op (P.map g.op y) := by
      rw [op_comp, P.map_comp, CategoryTheory.comp_apply]
    rw [hres, ← _root_.map_nsmul, hg, map_zero]

/-- A presheaf of abelian groups on a site is **locally torsion** when every section over every
object is, on some covering sieve, annihilated by a positive integer — the integer being allowed
to vary over the members of the sieve.

This is the presheaf-level form of `Stacks.Torsion.torsionSheafProperty`: an abelian sheaf is a
torsion abelian sheaf exactly when its underlying presheaf is locally torsion, which is
`torsionSheafProperty_iff_isLocallyTorsion`. -/
@[sga "4 IX 1.1"]
public def IsLocallyTorsion (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) : Prop :=
  ∀ (U : C) (x : P.obj (op U)), ∃ R : Sieve U, R ∈ J U ∧
    ∀ (V : C) (f : V ⟶ U), R f → ∃ n : ℕ, 0 < n ∧ n • P.map f.op x = 0

/-- An abelian sheaf is torsion exactly when its underlying presheaf is locally torsion. -/
public theorem torsionSheafProperty_iff_isLocallyTorsion (F : Sheaf J AddCommGrpCat.{w}) :
    torsionSheafProperty J F ↔ IsLocallyTorsion J F.obj :=
  Iff.rfl

/-- Being locally torsion says that the torsion sieve of every section is a covering sieve: the
torsion sieve is the largest sieve on which the section is pointwise annihilated. -/
public theorem isLocallyTorsion_iff_torsionSieve_mem (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    IsLocallyTorsion J P ↔ ∀ (U : C) (y : P.obj (op U)), torsionSieve P y ∈ J U := by
  constructor
  · intro h U y
    obtain ⟨R, hR, hkill⟩ := h U y
    exact J.superset_covering (fun V g hg => hkill V g hg) hR
  · exact fun h U y => ⟨_, h U y, fun _ _ hg => hg⟩

/-- **Local torsion passes along a locally surjective map.** If `η : P ⟶ Q` is locally surjective
for the topology and `P` is locally torsion, then so is `Q`: a section of `Q` is locally the image
of a section of `P`, that section is in turn locally annihilated, and the two coverings compose by
transitivity of the topology. -/
public theorem isLocallyTorsion_of_isLocallySurjective
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective J η] (hP : IsLocallyTorsion J P) :
    IsLocallyTorsion J Q := by
  rw [isLocallyTorsion_iff_torsionSieve_mem] at hP ⊢
  intro U y
  refine J.transitive (Presheaf.imageSieve_mem J η y) _ ?_
  intro V g hg
  obtain ⟨t, ht⟩ := hg
  refine J.superset_covering ?_ (hP V t)
  intro W h hh
  obtain ⟨n, hn, hkill⟩ := hh
  refine ⟨n, hn, nsmul_eq_zero_of_apply_eq (η.app (op W)) ?_ hkill⟩
  rw [op_comp, Q.map_comp, CategoryTheory.comp_apply, ← ht, NatTrans.naturality_apply η h.op]

/-- Local torsion transports along an isomorphism of presheaves, an isomorphism being locally
surjective. -/
public theorem isLocallyTorsion_of_iso {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (e : P ≅ Q)
    (hP : IsLocallyTorsion J P) : IsLocallyTorsion J Q :=
  isLocallyTorsion_of_isLocallySurjective J e.hom hP

/-- Being a torsion abelian sheaf transports along an isomorphism of sheaves. -/
public theorem torsionSheafProperty_of_iso {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G)
    (hF : torsionSheafProperty J F) : torsionSheafProperty J G :=
  isLocallyTorsion_of_iso J ((sheafToPresheaf J AddCommGrpCat.{w}).mapIso e) hF

/-- **Local torsion is tested on a cover-dense family.** If `G : C' ⥤ C` is cover dense for the
topology and every section of `P` over an object in the image of `G` is annihilated by a positive
integer, then `P` is locally torsion: the sieve of arrows factoring through the image of `G`
covers, and along each of its members the section restricts through an object of that image. -/
public theorem isLocallyTorsion_of_isCoverDense {C' : Type*} [Category* C'] (G : C' ⥤ C)
    [G.IsCoverDense J] (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (hG : ∀ (Z : C') (y : P.obj (op (G.obj Z))), ∃ n : ℕ, 0 < n ∧ n • y = 0) :
    IsLocallyTorsion J P := by
  intro U x
  refine ⟨Sieve.coverByImage G U, G.is_cover_of_isCoverDense J U, ?_⟩
  intro V g hg
  obtain ⟨⟨Z, lift, map, fac⟩⟩ := hg
  obtain ⟨n, hn, hkill⟩ := hG Z (P.map map.op x)
  refine ⟨n, hn, nsmul_eq_zero_of_apply_eq (P.map lift.op) ?_ hkill⟩
  rw [← fac, op_comp, P.map_comp, CategoryTheory.comp_apply]

/-- Being a torsion abelian group transports along an isomorphism of abelian groups. -/
public theorem exists_nsmul_eq_zero_of_iso {A B : AddCommGrpCat.{w}} (e : A ≅ B)
    (h : ∀ x : A, ∃ n : ℕ, 0 < n ∧ n • x = 0) (y : B) : ∃ n : ℕ, 0 < n ∧ n • y = 0 := by
  obtain ⟨n, hn, hkill⟩ := h (e.inv y)
  refine ⟨n, hn, nsmul_eq_zero_of_apply_eq e.hom ?_ hkill⟩
  rw [← CategoryTheory.comp_apply, e.inv_hom_id]
  rfl

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The sheafification of a locally torsion presheaf is a torsion abelian sheaf.** The canonical
map to the sheafification is locally surjective, so this is
`isLocallyTorsion_of_isLocallySurjective`. -/
public theorem torsionSheafProperty_sheafify (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (hP : IsLocallyTorsion J P) :
    torsionSheafProperty J ((presheafToSheaf J AddCommGrpCat.{w}).obj P) :=
  isLocallyTorsion_of_isLocallySurjective J (CategoryTheory.toSheafify J P) hP

end LocallyTorsion

end Stacks.Torsion

namespace Stacks.EtaleCohomology

open Stacks.Torsion Stacks.Cohomology.SheafifiedHigherDirectImage

universe w v u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section Functors

/-- **The direct image of abelian sheaves for the small étale sites.** It is restriction along
base change `smallEtaleBaseChange f : Y.Etale ⥤ X.Etale`, which is the site functor underlying
the geometric morphism `X_étale ⟶ Y_étale` and is continuous.

At the coefficient universe `max (u + 1) v` of the étale abelian development this is
`Stacks.EtaleCohomology.etaleAbelianDirectImage`, which is where its additivity and its
adjunctions are recorded. -/
public abbrev smallEtaleDirectImageAb :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{w} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{w} :=
  (smallEtaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{w}
    Y.smallEtaleTopology X.smallEtaleTopology

/-- **The étale cohomology presheaf of the direct image.** It sends an abelian sheaf `F` on
`X_étale` to the presheaf `V ↦ F(V ×_Y X)` on `Y.Etale`; its `n`-th right derived functor is the
presheaf `V ↦ H^n(V ×_Y X, F)` of [Stacks, Tag 072W], whose sheafification is `R^n f_* F`. -/
public abbrev smallEtaleCohomologyPresheaf :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      ((Y.Etale)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) :=
  pushforwardCohomologyPresheaf (K := X.smallEtaleTopology) AddCommGrpCat.{max (u + 1) v}
    (smallEtaleBaseChange f)

/-- **The derived direct image on bounded-below derived categories of abelian étale sheaves**:
`Rf_* : D^+(X_étale) ⥤ D^+(Y_étale)`, the right derived functor of `f_*` on bounded-below derived
categories.

This definition states the first clause of part (2) of [Stacks, Tag 0DDD] — that `Rf_* K` is
again an object of `D^+(Y_étale)` — which is the codomain of this functor. The remaining clause,
that its cohomology sheaves are torsion when those of `K` are, is
`torsionCohomologyProperty_smallEtaleDerivedDirectImage`. -/
@[stacks 0DDD "part (2), the bounded-below clause: the derived direct image of an object of
`D^+(X_étale)` is an object of `D^+(Y_étale)`, this being the codomain of the right derived
functor of `f_*` on bounded-below derived categories"]
public abbrev smallEtaleDerivedDirectImage :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  (smallEtaleDirectImageAb.{max (u + 1) v} f).rightDerivedFunctorPlus

end Functors

section Qcqs

/-- **Base change of a quasi-compact morphism along an object of the small étale site.** If `f` is
quasi-compact and the étale `Y`-scheme `V` is quasi-compact, then `V ×_Y X` is quasi-compact: the
projection to `V` is a base change of `f`.

This is the "restrict to affine `V`" step of the proof of [Stacks, Tag 0DDD]. -/
public theorem compactSpace_smallEtaleBaseChange_obj [QuasiCompact f] (V : Y.Etale)
    (hV : CompactSpace V.left) :
    CompactSpace ((smallEtaleBaseChange f).obj V).left := by
  have hV' : CompactSpace ((𝟭 Scheme.{u}).obj V.left) := hV
  show CompactSpace (Limits.pullback V.hom f : Scheme.{u})
  exact QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.fst V.hom f)

/-- **Base change of a quasi-separated morphism along an object of the small étale site.** If `f`
is quasi-separated and the étale `Y`-scheme `V` is quasi-separated, then `V ×_Y X` is
quasi-separated: the projection to `V` is a base change of `f`, and quasi-separatedness of
morphisms is stable under base change.

This is the "restrict to affine `V`" step of the proof of [Stacks, Tag 0DDD]. -/
public theorem quasiSeparatedSpace_smallEtaleBaseChange_obj [QuasiSeparated f] (V : Y.Etale)
    (hV : QuasiSeparatedSpace V.left) :
    QuasiSeparatedSpace ((smallEtaleBaseChange f).obj V).left := by
  have hV' : QuasiSeparatedSpace ((𝟭 Scheme.{u}).obj V.left) := hV
  have hfst : QuasiSeparated (Limits.pullback.fst V.hom f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated)
      (IsPullback.of_hasPullback V.hom f).flip ‹QuasiSeparated f›
  show QuasiSeparatedSpace (Limits.pullback V.hom f : Scheme.{u})
  exact quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.fst V.hom f)

/-- An affine object of the small étale site of `Y` is quasi-compact. -/
public theorem compactSpace_affineEtale_left (Z : Y.AffineEtale) :
    CompactSpace ((AffineEtale.Spec Y).obj Z).left := by
  show CompactSpace (Scheme.Spec.obj Z.left : Scheme.{u})
  infer_instance

/-- An affine object of the small étale site of `Y` is quasi-separated. -/
public theorem quasiSeparatedSpace_affineEtale_left (Z : Y.AffineEtale) :
    QuasiSeparatedSpace ((AffineEtale.Spec Y).obj Z).left := by
  show QuasiSeparatedSpace (Scheme.Spec.obj Z.left : Scheme.{u})
  infer_instance

end Qcqs

section Main

/-- **Part (1) of [Stacks, Tag 0DDD].** For a quasi-compact and quasi-separated morphism of
schemes `f : X ⟶ Y` and a torsion abelian sheaf `F` on `X_étale`, the higher direct image
`R^n f_* F` is a torsion abelian sheaf on `Y_étale`, for every `n`.

Tag 072W for abelian sheaves identifies `R^n f_* F` with the sheafification of the cohomology
presheaf and identifies that presheaf's values with étale cohomology over `V ×_Y X`; affine
objects are cover dense in the small étale site of `Y`, and for `V` affine the scheme `V ×_Y X`
is quasi-compact and quasi-separated, which is where the quasi-compactness and
quasi-separatedness of `f` enter, through `compactSpace_smallEtaleBaseChange_obj` and
`quasiSeparatedSpace_smallEtaleBaseChange_obj`; Tag 0DDC (1) over that object then makes
`H^n(V ×_Y X, F)` torsion, which is where the torsion hypothesis on `F` is consumed. So the
cohomology presheaf is locally torsion, and the sheafification of a locally torsion presheaf is a
torsion abelian sheaf. -/
@[stacks 0DDD "part (1): for `f` quasi-compact and quasi-separated and `F` a torsion abelian
sheaf on `X_étale`, every higher direct image `R^n f_* F` is a torsion abelian sheaf on
`Y_étale`"]
public theorem torsionSheafProperty_rightDerived_smallEtaleDirectImageAb
    [QuasiCompact f] [QuasiSeparated f] (n : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : torsionSheafProperty X.smallEtaleTopology F) :
    torsionSheafProperty Y.smallEtaleTopology
      (((smallEtaleDirectImageAb.{max (u + 1) v} f).rightDerived n).obj F) := by
  have hloc : IsLocallyTorsion Y.smallEtaleTopology
      (((smallEtaleCohomologyPresheaf.{v} f).rightDerived n).obj F) := by
    refine isLocallyTorsion_of_isCoverDense Y.smallEtaleTopology (AffineEtale.Spec Y) _ ?_
    intro Z
    refine exists_nsmul_eq_zero_of_iso
      ((pushforwardCohomologyPresheafEvaluationIso AddCommGrpCat.{max (u + 1) v}
        (smallEtaleBaseChange f) n ((AffineEtale.Spec Y).obj Z)).app F) (fun x => ?_)
    exact exists_nsmul_eq_zero_rightDerived_sectionsOverObject.{v} _
      (compactSpace_smallEtaleBaseChange_obj f _ (compactSpace_affineEtale_left Z))
      (quasiSeparatedSpace_smallEtaleBaseChange_obj f _ (quasiSeparatedSpace_affineEtale_left Z))
      F hF n x
  have hsheafify : torsionSheafProperty Y.smallEtaleTopology
      ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (((smallEtaleCohomologyPresheaf.{v} f).rightDerived n).obj F)) :=
    torsionSheafProperty_sheafify Y.smallEtaleTopology
      (((smallEtaleCohomologyPresheaf.{v} f).rightDerived n).obj F) hloc
  exact torsionSheafProperty_of_iso Y.smallEtaleTopology
    (((rightDerivedPushforwardIso AddCommGrpCat.{max (u + 1) v}
      (smallEtaleBaseChange f) n).app F).symm) hsheafify

/-- **Part (1) of [Stacks, Tag 0DDD] in degree zero.** For a quasi-compact and quasi-separated
morphism of schemes `f : X ⟶ Y` and a torsion abelian sheaf `F` on `X_étale`, the direct image
`f_* F` is a torsion abelian sheaf on `Y_étale`.

This is the degree-zero case of `torsionSheafProperty_rightDerived_smallEtaleDirectImageAb` read
on `f_*` itself: the direct image is a right adjoint, hence left exact, so its degree-zero right
derived functor is itself (`CategoryTheory.Functor.rightDerivedZeroIsoSelf`). -/
public theorem torsionSheafProperty_smallEtaleDirectImageAb
    [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : torsionSheafProperty X.smallEtaleTopology F) :
    torsionSheafProperty Y.smallEtaleTopology
      ((smallEtaleDirectImageAb.{max (u + 1) v} f).obj F) :=
  torsionSheafProperty_of_iso Y.smallEtaleTopology
    ((smallEtaleDirectImageAb.{max (u + 1) v} f).rightDerivedZeroIsoSelf.app F)
    (torsionSheafProperty_rightDerived_smallEtaleDirectImageAb.{v} f 0 F hF)

/-- **Part (2) of [Stacks, Tag 0DDD], the torsion clause.** For a quasi-compact and
quasi-separated morphism of schemes `f : X ⟶ Y` and an object `K` of `D^+(X_étale)` whose
cohomology sheaves are torsion, all cohomology sheaves of `Rf_* K` are torsion abelian sheaves on
`Y_étale`. That `Rf_* K` is again an object of `D^+(Y_étale)` is the codomain of
`smallEtaleDerivedDirectImage`, which states that clause of the tag.

This is dévissage from part (1). The torsion abelian sheaves on `Y_étale` form a Serre
subcategory ([Stacks, Tag 0DD7]), hence a weak Serre class; part (1) says that `R^p f_*` carries
torsion abelian sheaves on `X_étale` into it; and
`CategoryTheory.Functor.derivedCategoryBPlus_rightDerivedFunctorPlus_obj` propagates that from
the second page `E_2^{p,q} = R^p f_* H^q(K)` of the spectral sequence of a Cartan--Eilenberg
resolution to its abutment `H^{p+q}(Rf_* K)`. -/
@[stacks 0DDD "part (2), the torsion clause: for `f` quasi-compact and quasi-separated and `K` in
`D^+(X_étale)` with torsion cohomology sheaves, every cohomology sheaf of `Rf_* K` is a torsion
abelian sheaf on `Y_étale`. The bounded-below clause is the codomain of
`smallEtaleDerivedDirectImage`"]
public theorem torsionCohomologyProperty_smallEtaleDerivedDirectImage
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))
    (hK : torsionCohomologyProperty.{max (u + 1) v} X.smallEtaleTopology
      (DerivedCategory.Plus.ι.obj K)) :
    torsionCohomologyProperty.{max (u + 1) v} Y.smallEtaleTopology
      (DerivedCategory.Plus.ι.obj ((smallEtaleDerivedDirectImage.{v} f).obj K)) :=
  (Functor.derivedCategoryBPlus_rightDerivedFunctorPlus_obj
    (smallEtaleDirectImageAb.{max (u + 1) v} f)
    (torsionSheafProperty X.smallEtaleTopology) (torsionSheafProperty Y.smallEtaleTopology)
    (fun M hM p => torsionSheafProperty_rightDerived_smallEtaleDirectImageAb.{v} f p M hM) K
    hK).2

end Main

end Stacks.EtaleCohomology

end
