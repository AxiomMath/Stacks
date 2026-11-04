module

public import StacksFrontier.AlgebraicGeometry.DerivedIso.Leray
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.AffinePushforwardProjection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison of flat base change through the Čech resolution

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `X` and `S` of affine diagonal, let `T` be a finite affine
open cover of `X`, let `F` be a quasi-coherent `𝒪_X`-module and let `G` be a quasi-coherent
`𝒪_{S'}`-module flat over `S`. This file proves that the degreewise comparison of
`DegreewiseComparison.lean`,

`Φ(R ⁱ f_* F) ⟶ R ⁱ f'_*(Ψ F)`,

is invertible in every degree `i`. No hypothesis is placed on `f` beyond the existence of the
finite affine open cover, which is quasi-compactness of `X`.

The complex computing both sides is the absolute Čech resolution `𝔠 ⁼(𝒰, F)` of
[Stacks, Tag 01XL], whose degree `p` term is the product, over the `(p + 1)`-tuples of members of
the cover, of the direct image `a_* a^* F` along the structure morphism `a` of their
intersection. The criterion
`Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_degreewiseComparison_app_of_degreewise` asks for
four things, and the Čech resolution has all four:

* its image in `D⁺(X)` is `F[0]`, which is [Stacks, Tag 02FU] in the form
  `Stacks.AlgebraicGeometry.Tag01XLDerivedIso.absoluteCechResolutionIso`;
* its direct image computes `Rf_* F`, which is Leray's acyclicity lemma ([Stacks, Tag 015E]) in
  the form `isIso_rightDerivedFunctorPlusUnit_absoluteCechComplexPlus`;
* the underived comparison is invertible at every term, and
* `Ψ` of every term is right acyclic for `f'_*`.

The last two are the content of `AffinePushforwardProjection.lean` at a single factor: affineness
of the diagonal of `X` makes each `a` an affine morphism and affineness of the diagonal of `S`
makes each `a ≫ f` one, because the intersections have affine source
(`Stacks.AlgebraicGeometry.RelativeCechComplex.isAffine_left_pi` and
`isAffineHom_of_isAffine_source`). Passing from one factor to the product is additivity of all
the functors in sight, and in a negative degree the term is a zero object.

This is the route the proof of [Stacks, Tag 0GN5] takes when, in its own words, a Čech covering
suffices in place of a hypercovering — that is, when `X` has affine diagonal. It does not cover
the tag, whose hypothesis on `f` is only that it be quasi-compact and quasi-separated: for a
scheme without affine diagonal the inclusion of an affine open is not an affine morphism, and
base change genuinely fails at its direct image.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_underivedComparison_app_absoluteCechComplex`:
  the underived comparison is invertible at every term of the Čech resolution.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.rightAcyclic_totalCoefficients_absoluteCechComplex`:
  `Ψ` of every term of the Čech resolution is right acyclic for `f'_*`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_degreewiseComparison_app_of_affineOpenCover`:
  **the comparison of [Stacks, Tag 0GN5] is invertible for a scheme of affine diagonal with a
  finite affine open cover, over a base of affine diagonal**, in every degree.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_degreewiseComparison_app_of_affineDiagonal`:
  the same with the cover produced from quasi-compactness of `X`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_degreewiseComparison_app_of_isSeparated`:
  **the comparison of [Stacks, Tag 0GN5] for a quasi-compact separated morphism to an affine
  base**, in every degree.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeCech
open Stacks.AlgebraicGeometry.RelativeCechComplex
open Stacks.AlgebraicGeometry.Tag01XLDerivedIso
open Stacks.CategoryTheory.CechComplex (inter isLimitFan)

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Finite products -/

/-- **A natural transformation between additive functors is invertible at a finite product as
soon as it is invertible at every factor.**  Both functors preserve the product, and the
transformation is compatible with the projections, so it is the product of its components read
through the two comparison isomorphisms. -/
private theorem isIso_app_pi {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] {P Q : C ⥤ D} [P.Additive] [Q.Additive] (τ : P ⟶ Q) {ι : Type*}
    (A : ι → C) [Finite ι] [HasProductsOfShape ι C] [HasProductsOfShape ι D]
    (h : ∀ k, IsIso (τ.app (A k))) : IsIso (τ.app (∏ᶜ A)) := by
  have := h
  have key : τ.app (∏ᶜ A) ≫ piComparison Q A =
      piComparison P A ≫ Limits.Pi.map fun k => τ.app (A k) := by
    refine Pi.hom_ext _ _ fun k => ?_
    simp only [Category.assoc, piComparison_comp_π, Pi.map_π, piComparison_comp_π_assoc]
    exact (τ.naturality _).symm
  have hcomp : IsIso (τ.app (∏ᶜ A) ≫ piComparison Q A) := by rw [key]; infer_instance
  exact IsIso.of_isIso_comp_right (τ.app (∏ᶜ A)) (piComparison Q A)

/-- `isIso_app_pi` for a product presented by an arbitrary limit fan.  This is the form a Čech
term takes: it is a product of the values of the coefficient presheaf, but it is not
syntactically `∏ᶜ`. -/
private theorem isIso_app_of_isLimitFan {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] {P Q : C ⥤ D} [P.Additive] [Q.Additive] (τ : P ⟶ Q)
    {ι : Type*} (A : ι → C) {c : Fan A} (hc : IsLimit c) [Finite ι] [HasProductsOfShape ι C]
    [HasProductsOfShape ι D] (h : ∀ k, IsIso (τ.app (A k))) : IsIso (τ.app c.pt) :=
  (CategoryTheory.NatTrans.isIso_app_iff_of_iso τ
    (hc.conePointUniqueUpToIso (productIsProduct A))).mpr (isIso_app_pi τ A h)

/-- **The image of a finite product under an additive functor is right acyclic as soon as the
images of the factors are.**  The functor preserves the product, so its value at the product is
the product of its values. -/
private theorem rightAcyclic_obj_pi {C C' D : Type*} [Category* C] [Category* C'] [Category* D]
    [Preadditive C] [Abelian C'] [Abelian D] [HasDerivedCategory C'] [HasDerivedCategory D]
    (Ψ : C ⥤ C') [Ψ.Additive] (F' : C' ⥤ D) [F'.Additive] [EnoughInjectives C']
    [PreservesFiniteLimits F'] {ι : Type*} (A : ι → C) [Finite ι] [HasProductsOfShape ι C]
    [HasProductsOfShape ι C'] (h : ∀ k, F'.rightAcyclic (Ψ.obj (A k))) :
    F'.rightAcyclic (Ψ.obj (∏ᶜ A)) :=
  Stacks.RightAcyclicProduct.rightAcyclic_of_iso F'
    (@asIso _ _ _ _ (piComparison Ψ A) inferInstance).symm
    (Stacks.RightAcyclicProduct.rightAcyclic_pi F' _ h)

/-- `rightAcyclic_obj_pi` for a product presented by an arbitrary limit fan. -/
private theorem rightAcyclic_obj_of_isLimitFan {C C' D : Type*} [Category* C] [Category* C']
    [Category* D] [Preadditive C] [Abelian C'] [Abelian D] [HasDerivedCategory C']
    [HasDerivedCategory D] (Ψ : C ⥤ C') [Ψ.Additive] (F' : C' ⥤ D) [F'.Additive]
    [EnoughInjectives C'] [PreservesFiniteLimits F'] {ι : Type*} (A : ι → C) {c : Fan A}
    (hc : IsLimit c) [Finite ι] [HasProductsOfShape ι C] [HasProductsOfShape ι C']
    (h : ∀ k, F'.rightAcyclic (Ψ.obj (A k))) : F'.rightAcyclic (Ψ.obj c.pt) :=
  Stacks.RightAcyclicProduct.rightAcyclic_of_iso F'
    (Ψ.mapIso (hc.conePointUniqueUpToIso (productIsProduct A))).symm
    (rightAcyclic_obj_pi Ψ F' A h)

/-! ### The terms of the Čech resolution -/

variable {S S' X X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- Additivity of the source of the underived comparison. -/
private instance additive_pushforward_comp_baseCoefficients (f : X ⟶ S) (g : S' ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    (modulePushforward f.toLRSHom.toShHom ⋙ baseCoefficients g G).Additive :=
  inferInstance

/-- Additivity of the target of the underived comparison. -/
private instance additive_totalCoefficients_comp_pushforward (g' : X' ⟶ X) (f' : X' ⟶ S')
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    (totalCoefficients g' f' G ⋙ modulePushforward f'.toLRSHom.toShHom).Additive :=
  inferInstance

/-- The Čech family of a finite affine open cover: its members, as objects over `X`. -/
private abbrev cechFamily (T : X.AffineOpenCover.{u, u}) : T.I₀ → Over X :=
  fun i => (Over.mk (T.f i) : Over X)

/-- A finite intersection of members of an affine open cover has affine source, `X` having
affine diagonal. -/
private theorem isAffine_cechInter_left
    [AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from X))]
    (T : X.AffineOpenCover.{u, u}) {m : ℕ} (x : Fin (m + 1) → T.I₀) :
    IsAffine (inter (cechFamily T) x).left := by
  have hoi : ∀ a : Fin (m + 1), IsOpenImmersion (cechFamily T (x a)).hom :=
    fun a => inferInstanceAs (IsOpenImmersion (T.f (x a)))
  have hfa : ∀ a : Fin (m + 1), IsAffine (cechFamily T (x a)).left :=
    fun a => inferInstanceAs (IsAffine (Spec (T.X (x a))))
  exact isAffine_left_pi fun a => cechFamily T (x a)

/-- **For a morphism with affine source, the underived comparison is invertible at the direct
image of the inverse image, and `Ψ` of it is right acyclic for `f'_*`.**  Such an `A.hom` is an
affine morphism, and so is `A.hom ≫ f`, because `X` and `S` have affine diagonal; so
`isIso_underivedComparison_app_pushforward` and `rightAcyclic_totalCoefficients_pushforward`
apply, with the cartesian square obtained by pulling `A.hom` back along `g'`. -/
private theorem isIso_and_rightAcyclic_overAffine (H : IsPullback g' f' f g)
    [AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from X))]
    [AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from S))] (A : Over X)
    [IsAffine A.left] (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (hG : G.IsQuasicoherent) (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hF : F.IsQuasicoherent) :
    IsIso ((underivedComparison H.w G).app
      ((modulePushforward A.hom.toLRSHom.toShHom).obj
        ((modulePullback A.hom.toLRSHom.toShHom).obj F))) ∧
    (modulePushforward f'.toLRSHom.toShHom).rightAcyclic
      ((totalCoefficients g' f' G).obj
        ((modulePushforward A.hom.toLRSHom.toShHom).obj
          ((modulePullback A.hom.toLRSHom.toShHom).obj F))) := by
  have := hF
  have : AlgebraicGeometry.IsAffineHom A.hom := isAffineHom_of_isAffine_source _
  have : AlgebraicGeometry.IsAffineHom (A.hom ≫ f) := isAffineHom_of_isAffine_source _
  have hFA := AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent
    A.hom.toLRSHom.toShHom F
  have hP := IsPullback.of_hasPullback A.hom g'
  exact ⟨isIso_underivedComparison_app_pushforward H hP G hG _ hFA,
    rightAcyclic_totalCoefficients_pushforward H hP G hG _ hFA⟩

/-- The term of the absolute Čech resolution in a negative degree is a zero object. -/
private theorem isZero_absoluteCechComplexPlus_X_of_neg (T : X.AffineOpenCover.{u, u})
    [Fintype T.I₀] (Fq : (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    {n : ℤ} (hn : n < 0) : IsZero (((absoluteCechComplexPlus T).obj Fq).obj.X n) := by
  refine HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat n fun m hm => ?_
  have h : (m : ℤ) = n := hm
  omega

/-- **The underived comparison is invertible at every term of the absolute Čech resolution.**
The term in degree `m ≥ 0` is a finite product of direct images `a_* a^* F` along the structure
morphisms of the intersections of members of the cover, where
`isIso_and_rightAcyclic_overAffine` applies; the comparison is a transformation of
additive functors, so the conclusion crosses the product. In a negative degree the term is a
zero object. -/
theorem isIso_underivedComparison_app_absoluteCechComplex (H : IsPullback g' f' f g)
    [AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from X))]
    [AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from S))]
    (T : X.AffineOpenCover.{u, u}) [Fintype T.I₀]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) (hG : G.IsQuasicoherent)
    (Fq : (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (n : ℤ) :
    IsIso ((underivedComparison H.w G).app (((absoluteCechComplexPlus T).obj Fq).obj.X n)) := by
  rcases Int.lt_or_le n 0 with hn | hn
  · have hz := isZero_absoluteCechComplexPlus_X_of_neg T Fq hn
    have hzP : IsZero ((baseCoefficients g G).obj
        ((modulePushforward f.toLRSHom.toShHom).obj
          (((absoluteCechComplexPlus T).obj Fq).obj.X n))) :=
      Functor.map_isZero (baseCoefficients g G)
        (Functor.map_isZero (modulePushforward f.toLRSHom.toShHom) hz)
    have hzQ : IsZero ((modulePushforward f'.toLRSHom.toShHom).obj
        ((totalCoefficients g' f' G).obj (((absoluteCechComplexPlus T).obj Fq).obj.X n))) :=
      Functor.map_isZero (modulePushforward f'.toLRSHom.toShHom)
        (Functor.map_isZero (totalCoefficients g' f' G) hz)
    exact isIso_of_isZero hzP hzQ _
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    refine (CategoryTheory.NatTrans.isIso_app_iff_of_iso (underivedComparison H.w G)
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat (i := m) rfl)).mpr ?_
    refine isIso_app_of_isLimitFan (underivedComparison H.w G)
      (fun x : Fin (m + 1) → T.I₀ =>
        ((relativeMonad X).flip.obj Fq.obj).obj (op (inter (cechFamily T) x)))
      (isLimitFan (cechFamily T) ((relativeMonad X).flip.obj Fq.obj) m) fun x => ?_
    have := isAffine_cechInter_left T x
    exact (isIso_and_rightAcyclic_overAffine H (inter (cechFamily T) x) G hG Fq.obj Fq.property).1

/-- **`Ψ` of every term of the absolute Čech resolution is right acyclic for `f'_*`.**  Factorwise
this is `isIso_and_rightAcyclic_overAffine`, and `Ψ` and `f'_*` are additive, so the
conclusion crosses the finite product. In a negative degree the term is a zero object. -/
theorem rightAcyclic_totalCoefficients_absoluteCechComplex (H : IsPullback g' f' f g)
    [AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from X))]
    [AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from S))]
    (T : X.AffineOpenCover.{u, u}) [Fintype T.I₀]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) (hG : G.IsQuasicoherent)
    (Fq : (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) (n : ℤ) :
    (modulePushforward f'.toLRSHom.toShHom).rightAcyclic
      ((totalCoefficients g' f' G).obj (((absoluteCechComplexPlus T).obj Fq).obj.X n)) := by
  rcases Int.lt_or_le n 0 with hn | hn
  · exact Stacks.RightAcyclicProduct.rightAcyclic_of_isZero _
      (Functor.map_isZero (totalCoefficients g' f' G)
        (isZero_absoluteCechComplexPlus_X_of_neg T Fq hn))
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    refine Stacks.RightAcyclicProduct.rightAcyclic_of_iso _
      ((totalCoefficients g' f' G).mapIso
        (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat (i := m) rfl)).symm ?_
    refine rightAcyclic_obj_of_isLimitFan (totalCoefficients g' f' G)
      (modulePushforward f'.toLRSHom.toShHom)
      (fun x : Fin (m + 1) → T.I₀ =>
        ((relativeMonad X).flip.obj Fq.obj).obj (op (inter (cechFamily T) x)))
      (isLimitFan (cechFamily T) ((relativeMonad X).flip.obj Fq.obj) m) fun x => ?_
    have := isAffine_cechInter_left T x
    exact (isIso_and_rightAcyclic_overAffine H (inter (cechFamily T) x) G hG Fq.obj Fq.property).2

/-! ### The comparison for a scheme of affine diagonal -/

/-- **The comparison of [Stacks, Tag 0GN5] through the Čech resolution.**  For a cartesian square
with `X` and `S` of affine diagonal, a finite affine open cover `T` of `X`, a quasi-coherent
`𝒪_X`-module `F` and a quasi-coherent `𝒪_{S'}`-module `G` flat over `S`, the degreewise
comparison

`Φ(R ⁱ f_* F) ⟶ R ⁱ f'_*(Ψ F)`

is invertible in every degree `i`.  Nothing is assumed about `f`.

The complex computing both sides is the absolute Čech resolution of `T`: its image in `D⁺(X)` is
`F[0]` ([Stacks, Tag 02FU]), its direct image computes `Rf_* F` (Leray's acyclicity lemma,
[Stacks, Tag 015E]), the underived comparison is invertible at every one of its terms and `Ψ` of
every one of its terms is right acyclic for `f'_*`. -/
@[ega "III 7.7.2" "special case"]
theorem isIso_degreewiseComparison_app_of_affineOpenCover (H : IsPullback g' f' f g)
    [AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from X))]
    [AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from S))]
    (T : X.AffineOpenCover.{u, u}) [Fintype T.I₀]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [hF : F.IsQuasicoherent]
    (i : ℕ) :
    IsIso ((degreewiseComparison H G hG i).app F) := by
  let Fq : (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := ⟨F, hF⟩
  exact isIso_degreewiseComparison_app_of_degreewise H G hG F
    ((HomotopyCategory.Plus.quotient X.Modules).obj ((absoluteCechComplexPlus T).obj Fq))
    ((absoluteCechResolutionIso T).app Fq).symm
    (isIso_rightDerivedFunctorPlusUnit_absoluteCechComplexPlus f T Fq)
    (isIso_underivedComparison_app_absoluteCechComplex H T G inferInstance Fq)
    (rightAcyclic_totalCoefficients_absoluteCechComplex H T G inferInstance Fq) i

/-- A finite affine open cover of a quasi-compact scheme: a finite subcover of the canonical
affine open cover. -/
def finiteAffineOpenCover (Y : Scheme.{u}) [CompactSpace Y] : Y.AffineOpenCover.{u, u} :=
  let C := Y.affineOpenCover
  let V := C.openCover.finiteSubcover
  { I₀ := V.I₀
    X i := C.X (C.openCover.idx i.1)
    f i := C.f (C.openCover.idx i.1)
    idx := V.idx
    covers := V.covers
    map_prop i := C.map_prop (C.openCover.idx i.1) }

/-- The index set of `finiteAffineOpenCover Y` is finite. -/
instance fintype_finiteAffineOpenCover_I₀ (Y : Scheme.{u}) [CompactSpace Y] :
    Fintype (finiteAffineOpenCover Y).I₀ :=
  inferInstanceAs (Fintype Y.affineOpenCover.openCover.finiteSubcover.I₀)

/-- **The comparison of [Stacks, Tag 0GN5] for a quasi-compact scheme of affine diagonal over a
base of affine diagonal**, in every degree: the Čech resolution of a finite subcover of the
canonical affine open cover computes both sides. -/
@[ega "III 7.7.2" "special case"]
theorem isIso_degreewiseComparison_app_of_affineDiagonal (H : IsPullback g' f' f g)
    [CompactSpace X]
    [AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from X))]
    [AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from S))]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    (i : ℕ) :
    IsIso ((degreewiseComparison H G hG i).app F) :=
  isIso_degreewiseComparison_app_of_affineOpenCover H (finiteAffineOpenCover X) G hG F i

/-- **The comparison of [Stacks, Tag 0GN5] for a quasi-compact separated morphism to an affine
base**, in every degree.  An affine base is of affine diagonal and compact, so `X` is compact and
separated, hence of affine diagonal, and
`isIso_degreewiseComparison_app_of_affineDiagonal` applies.  This is the case in which, in the
words of [Stacks, Tag 0GN5], a Čech covering suffices in place of a hypercovering. -/
theorem isIso_degreewiseComparison_app_of_isSeparated (H : IsPullback g' f' f g)
    [QuasiCompact f] [IsSeparated f] [IsAffine S]
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) [G.IsQuasicoherent]
    (hG : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom G)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) [F.IsQuasicoherent]
    (i : ℕ) :
    IsIso ((degreewiseComparison H G hG i).app F) := by
  have : CompactSpace ↥X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have hsepS : IsSeparated (terminal.from S) := inferInstance
  have hsepX : IsSeparated (terminal.from X) := by
    have h : IsSeparated (f ≫ terminal.from S) := inferInstance
    simpa using h
  have : AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from X)) := inferInstance
  have : AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from S)) := inferInstance
  exact isIso_degreewiseComparison_app_of_affineDiagonal H G hG F i

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
