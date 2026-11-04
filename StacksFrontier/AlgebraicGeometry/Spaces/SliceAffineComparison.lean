module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurj
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyBijective

/-!
# A comparison morphism bijective over affine charts suffices for essential surjectivity

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `X` be
an étale chart of `F`.  Two kinds of sheaves of modules live on the slice of the small étale
site of `F` at `X`: the restriction `G|_X` of an `𝒪_F`-module
(`AlgebraicGeometry.Space.SmallEtale.sliceModule`) and the module `Mᵃ` of Tag 03DU of a
quasi-coherent module `M` on the scheme underlying `X`
(`AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule`).  The essential-surjectivity
hypothesis `hEss` of
`AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj` asks for an
*isomorphism* `G|_Y ≅ Mᵃ` on the slice at every affine chart `Y`.

This file replaces that demand by a strictly more tractable one: **a morphism `Mᵃ ⟶ G|_Y` whose
map on sections is bijective over the affine charts over `Y` only.**  Nothing has to be checked
over a non-affine chart, and no inverse has to be produced.  The two demands are *equivalent*
— `AlgebraicGeometry.Space.SmallEtale.exists_bijective_comparison_of_exists_iso` derives the
second from the first — so this is a change of the work owed and not a weakening of the
hypothesis.

The mechanism is that the affine étale charts are a dense subsite of the small étale site
(Stacks 04JS, `AlgebraicGeometry.Space.AffineEtale.inclusion_isSpecialCocontinuous`): every
chart is covered by affine charts, so bijectivity over affine charts is local bijectivity, and a
locally bijective morphism of sheaves of modules is an isomorphism
(`Stacks.SheafOfModules.isIso_of_isLocallyBijective`).

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isCoverDense_affineEtaleInclusion` and
  `AlgebraicGeometry.Space.SmallEtale.coverByImage_affineEtale_mem_over`: the sieve of chart
  morphisms factoring through an affine chart is a covering sieve, also after localizing at a
  chart.
* `AlgebraicGeometry.Space.SmallEtale.isLocallySurjective_of_surjective_app_of_isAffine` and
  `AlgebraicGeometry.Space.SmallEtale.isLocallyInjective_of_injective_app_of_isAffine`: a
  morphism of sheaves of modules on the slice at a chart which is surjective (respectively
  injective) on the sections over every affine chart over it is locally surjective (respectively
  locally injective).
* `AlgebraicGeometry.Space.SmallEtale.isIso_of_bijective_app_of_isAffine`: **a morphism of
  sheaves of modules on the slice at a chart which is bijective on the sections over the affine
  charts is an isomorphism.**
* `AlgebraicGeometry.Space.SmallEtale.exists_sliceAssociatedModule_iso_of_bijective_app`: a
  comparison morphism `Mᵃ ⟶ G|_X` bijective over the affine charts gives the isomorphism that
  `hEss` asks for at `X`.
* `AlgebraicGeometry.Space.SmallEtale.exists_bijective_comparison_of_exists_iso`: the converse,
  which is what makes the exchange faithful — `hEss` at `X` already provides such a comparison
  morphism, bijective over *every* chart.
* `AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_exists_comparison`:
  **`AlgebraicGeometry.Space.IsCartesianOnAffineCharts` follows from a comparison morphism
  bijective over affine charts at every affine chart.**  This is the forward implication of
  Descent, Proposition 03DX(2) reduced to the construction of a comparison morphism.

## Implementation notes

The covering sieve used throughout is `CategoryTheory.Sieve.coverByImage` of the inclusion of
the affine étale charts, transported to the slice by
`CategoryTheory.GrothendieckTopology.overEquiv_symm_mem_over`; membership in the transported
sieve is membership of the underlying chart morphism by `CategoryTheory.Sieve.overEquiv_symm_iff`,
which holds by `rfl`.  Given a chart morphism `g` in that sieve, with factorisation
`lift ≫ map = g` through an affine chart `A`, the object `CategoryTheory.Over.mk (map ≫ Z.hom)`
of the slice has `A` as its underlying chart — so the hypothesis applies to it — and `g` factors
through it *in the slice*.  Since `CategoryTheory.Presheaf.imageSieve` and
`CategoryTheory.Presheaf.equalizerSieve` are sieves, it is enough to treat that one factor.

Two spellings of the same map have to be kept apart.  The hypotheses are stated with
`CategoryTheory.ModuleCat.Hom.hom` of `φ.val.app`, which is the spelling a consumer computing
with sections has, whereas `CategoryTheory.Presheaf.IsLocallySurjective` is about the morphism of
presheaves of abelian groups underlying `φ.val`.  The two are definitionally equal but not
syntactically equal, so the naturality step in
`AlgebraicGeometry.Space.SmallEtale.isLocallyInjective_of_injective_app_of_isAffine` is taken in
term mode: a `rw` with `CategoryTheory.NatTrans.naturality_apply` fails there with "the target
expression is not type-correct under the `implicit` transparency level" on a goal that displays
the pattern.

The module universe of the first five results is free; only the last three mention
`AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule`, whose sections are global sections of
a pullback of a module on a scheme and therefore lie in `Type u` by construction.

No `@[stacks]` attribute is claimed.  Descent, Proposition 03DX(2) is an equivalence of
categories and neither half of it is proved here: the comparison morphism is a hypothesis, and
Stacks constructs it from Tags 03DV and 0GN7, which this tree has for a **scheme** and not for
an algebraic space: 03DV is
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseOpenCoverQuasicoherence` together
with the two small-site modules next to it, and 0GN7 is tagged at the big and small étale sites,
all of them over `S : Scheme`.  The object here is a slice of the small étale site of an
algebraic space, so neither applies.  Stacks 04JS
is already tagged at its own statement.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory Opposite

universe m u

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (X : SmallEtale B S hS F)

/-! ### Affine charts cover, also in the slice -/

include hF in
/-- **The affine étale charts are cover dense in the small étale site.**  This is the dense
subsite half of Stacks 04JS, `AlgebraicGeometry.Space.AffineEtale.inclusion_isSpecialCocontinuous`,
extracted in the form `CategoryTheory.Functor.IsCoverDense` consumed below. -/
theorem isCoverDense_affineEtaleInclusion :
    (AffineEtale.inclusion B S hS F).IsCoverDense (topology B S hS F) :=
  (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2.isCoverDense'

include hF in
/-- **The chart morphisms factoring through an affine chart form a covering sieve of any object
of the slice at `X`.**  Cover density gives the covering sieve on the underlying chart, and
`CategoryTheory.GrothendieckTopology.overEquiv_symm_mem_over` transports it to the localized
topology. -/
theorem coverByImage_affineEtale_mem_over (Z : Over X) :
    (Sieve.overEquiv Z).symm (Sieve.coverByImage (AffineEtale.inclusion B S hS F) Z.left) ∈
      ((topology B S hS F).over X) Z :=
  GrothendieckTopology.overEquiv_symm_mem_over _ _ _
    ((isCoverDense_affineEtaleInclusion B S hS F hF).is_cover Z.left)

/-! ### Bijectivity over affine charts is local bijectivity -/

/-- A morphism of the slice in the sieve of chart morphisms factoring through an affine chart
factors in the slice through an object whose underlying chart is affine. -/
private theorem exists_factorization_through_affine (Z W : Over X) (g : W ⟶ Z)
    (hg : (Sieve.overEquiv Z).symm
      (Sieve.coverByImage (AffineEtale.inclusion B S hS F) Z.left) g) :
    ∃ (A : Over X) (_ : IsAffine (chartScheme A.left)) (l : W ⟶ A) (m : A ⟶ Z), g = l ≫ m := by
  obtain ⟨⟨A, lift, map, fac⟩⟩ := hg
  refine ⟨Over.mk (map ≫ Z.hom), A.property, Over.homMk lift (by
    change lift ≫ map ≫ Z.hom = W.hom
    rw [← Category.assoc, fac]
    exact Over.w g), Over.homMk map, Over.OverMorphism.ext (by simpa using fac.symm)⟩

include hF in
/-- **Surjectivity on sections over affine charts is local surjectivity.**  If the sections map
of `φ` is surjective over every object of the slice at `X` whose underlying scheme is affine,
then `φ` is locally surjective: every section is, on an affine covering, in the image. -/
theorem isLocallySurjective_of_surjective_app_of_isAffine
    {M N : SheafOfModules.{m} (sliceRingSheaf B S hS F hF X)} (φ : M ⟶ N)
    (h : ∀ Z : Over X, IsAffine (chartScheme Z.left) →
      Function.Surjective (φ.val.app (op Z)).hom) :
    PresheafOfModules.IsLocallySurjective ((topology B S hS F).over X) φ.val := by
  constructor
  intro Z s
  refine ((topology B S hS F).over X).superset_covering ?_
    (coverByImage_affineEtale_mem_over B S hS F hF X Z)
  intro W g hg
  obtain ⟨A, hA, l, m, rfl⟩ := exists_factorization_through_affine B S hS F X Z W g hg
  obtain ⟨t, ht⟩ := h A hA
    (((PresheafOfModules.toPresheaf (sliceRingSheaf B S hS F hF X).obj).obj N.val).map m.op s)
  exact (Presheaf.imageSieve
      ((PresheafOfModules.toPresheaf (sliceRingSheaf B S hS F hF X).obj).map φ.val)
      s).downward_closed ⟨t, ht⟩ l

include hF in
/-- **Injectivity on sections over affine charts is local injectivity.**  If the sections map of
`φ` is injective over every object of the slice at `X` whose underlying scheme is affine, then
two sections with the same image agree on an affine covering. -/
theorem isLocallyInjective_of_injective_app_of_isAffine
    {M N : SheafOfModules.{m} (sliceRingSheaf B S hS F hF X)} (φ : M ⟶ N)
    (h : ∀ Z : Over X, IsAffine (chartScheme Z.left) →
      Function.Injective (φ.val.app (op Z)).hom) :
    PresheafOfModules.IsLocallyInjective ((topology B S hS F).over X) φ.val := by
  constructor
  intro Z x y hxy
  refine ((topology B S hS F).over X).superset_covering ?_
    (coverByImage_affineEtale_mem_over B S hS F hF X Z.unop)
  intro W g hg
  obtain ⟨A, hA, l, m, rfl⟩ := exists_factorization_through_affine B S hS F X Z.unop W g hg
  have hm : Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (sliceRingSheaf B S hS F hF X).obj).obj M.val) x y m := by
    refine h A hA ?_
    have hx := NatTrans.naturality_apply
      ((PresheafOfModules.toPresheaf (sliceRingSheaf B S hS F hF X).obj).map φ.val) m.op x
    have hy := NatTrans.naturality_apply
      ((PresheafOfModules.toPresheaf (sliceRingSheaf B S hS F hF X).obj).map φ.val) m.op y
    exact hx.trans ((congrArg
      (fun z : ToType (((PresheafOfModules.toPresheaf
          (sliceRingSheaf B S hS F hF X).obj).obj N.val).obj Z) =>
        ((PresheafOfModules.toPresheaf (sliceRingSheaf B S hS F hF X).obj).obj N.val).map m.op z)
      hxy).trans hy.symm)
  exact (Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (sliceRingSheaf B S hS F hF X).obj).obj M.val)
      x y).downward_closed hm l

include hF in
/-- **A morphism of sheaves of modules on the slice at a chart which is bijective on the sections
over the affine charts is an isomorphism.**  Nothing is assumed over a non-affine chart: the
affine charts cover, so the morphism is locally bijective, and a locally bijective morphism of
sheaves of modules is invertible. -/
theorem isIso_of_bijective_app_of_isAffine
    {M N : SheafOfModules.{m} (sliceRingSheaf B S hS F hF X)} (φ : M ⟶ N)
    (h : ∀ Z : Over X, IsAffine (chartScheme Z.left) →
      Function.Bijective (φ.val.app (op Z)).hom) :
    IsIso φ :=
  have := isLocallyInjective_of_injective_app_of_isAffine B S hS F hF X φ
    fun Z hZ => (h Z hZ).1
  have := isLocallySurjective_of_surjective_app_of_isAffine B S hS F hF X φ
    fun Z hZ => (h Z hZ).2
  Stacks.SheafOfModules.isIso_of_isLocallyBijective φ

/-! ### The exchange at the essential-surjectivity hypothesis -/

include hF in
/-- **A comparison morphism bijective over the affine charts gives the isomorphism `hEss` asks
for.**  For a quasi-coherent module `M` on the scheme underlying the chart `X`, a morphism
`Mᵃ ⟶ G|_X` of sheaves of modules on the slice at `X` which is bijective on the sections over
the affine charts over `X` is invertible, so `G|_X` is in the essential image of `M ↦ Mᵃ`. -/
theorem exists_sliceAssociatedModule_iso_of_bijective_app
    (G : Modules.{u, u} B S hS F hF) (M : (chartScheme X).Modules) [M.IsQuasicoherent]
    (hM : Presheaf.IsSheaf ((topology B S hS F).over X)
      (Stacks.Sites.associatedPresheaf (chartScheme X) M (sliceToOver B S hS F X)))
    (φ : sliceAssociatedModule B S hS F hF X M hM ⟶ sliceModule B S hS F hF X G)
    (h : ∀ Z : Over X, IsAffine (chartScheme Z.left) →
      Function.Bijective (φ.val.app (op Z)).hom) :
    Nonempty (sliceModule B S hS F hF X G ≅ sliceAssociatedModule B S hS F hF X M hM) :=
  have := isIso_of_bijective_app_of_isAffine B S hS F hF X φ h
  ⟨(asIso φ).symm⟩

include hF in
/-- **The converse: the isomorphism `hEss` asks for provides such a comparison morphism.**  Its
inverse is bijective on the sections over *every* chart, affine or not, by
`Stacks.SheafOfModules.bijective_app`.  So demanding a comparison morphism bijective over the
affine charts is exactly as strong as demanding the isomorphism, and
`AlgebraicGeometry.Space.SmallEtale.exists_sliceAssociatedModule_iso_of_bijective_app` changes
the work owed rather than the hypothesis. -/
theorem exists_bijective_comparison_of_exists_iso
    (G : Modules.{u, u} B S hS F hF) (M : (chartScheme X).Modules) [M.IsQuasicoherent]
    (hM : Presheaf.IsSheaf ((topology B S hS F).over X)
      (Stacks.Sites.associatedPresheaf (chartScheme X) M (sliceToOver B S hS F X)))
    (e : sliceModule B S hS F hF X G ≅ sliceAssociatedModule B S hS F hF X M hM) :
    ∃ φ : sliceAssociatedModule B S hS F hF X M hM ⟶ sliceModule B S hS F hF X G,
      ∀ Z : Over X, Function.Bijective (φ.val.app (op Z)).hom :=
  ⟨e.inv, fun Z => Stacks.SheafOfModules.bijective_app e.inv e.hom e.inv_hom_id e.hom_inv_id
    (op Z)⟩

end AlgebraicGeometry.Space.SmallEtale

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

include hF in
/-- **The forward implication of Descent, Proposition 03DX(2) from a comparison morphism.**  If
for every affine chart `Y` of `F` there are a quasi-coherent module `M` on the scheme underlying
`Y`, the sheaf condition of Tag 03DT for its presheaf of pullback sections, and a morphism
`Mᵃ ⟶ G|_Y` of sheaves of modules on the slice at `Y` whose sections map is bijective over the
affine charts over `Y`, then `G` is cartesian on affine charts.

This is `AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj` with its
essential-surjectivity hypothesis replaced by the equivalent demand of
`AlgebraicGeometry.Space.SmallEtale.exists_sliceAssociatedModule_iso_of_bijective_app`: an
isomorphism of sheaves of modules has to be inverted and checked over every chart, whereas this
morphism has to be checked only over the affine ones.  What is still owed is the morphism
itself, which Stacks obtains from Tags 03DV and 0GN7; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurj`.  No `@[stacks]` attribute
is claimed. -/
theorem isCartesianOnAffineCharts_of_exists_comparison (G : Modules.{u, u} B S hS F hF)
    (hcomp : ∀ Y : SmallEtale B S hS F, IsAffine (chartScheme Y) →
      ∃ (M : (chartScheme Y).Modules) (_ : M.IsQuasicoherent)
        (hM : Presheaf.IsSheaf ((topology B S hS F).over Y)
          (Stacks.Sites.associatedPresheaf (chartScheme Y) M
            (sliceToOver B S hS F Y)))
        (φ : sliceAssociatedModule B S hS F hF Y M hM ⟶ sliceModule B S hS F hF Y G),
        ∀ Z : Over Y, IsAffine (chartScheme Z.left) →
          Function.Bijective (φ.val.app (op Z)).hom) :
    IsCartesianOnAffineCharts G :=
  isCartesianOnAffineCharts_of_essSurj B S hS F hF G fun Y hY => by
    obtain ⟨M, hMq, hM, φ, hφ⟩ := hcomp Y hY
    have _ := hMq
    exact ⟨M, hMq, hM,
      exists_sliceAssociatedModule_iso_of_bijective_app B S hS F hF Y G M hM φ hφ⟩

end AlgebraicGeometry.Space.SmallEtale

end
