module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.PresentingDescentData
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackTrivialActionRigidification
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.Deformation.Artin.FormalObject.TriangleCechObject

/-!
# The glued objects of the classifying stack over the thickened triangles

Let `A` be a group scheme over a field `k` lying in a big fppf site, let `K/k` be a field
extension and let `η` be a `K`-point of `A`. Over the `n`-th thickening
`X_n = Spec K[x, y] ⧸ (xy(x + y - 1)) ^ (n + 1)` of the triangle, covered by the two opens
`U = D(1 - x)` and `W = D(1 - y)`, the glueing cocycle `c` (`Deformation.Artin.triangleCocycle`)
is a morphism `U ∩ W ⟶ A`. This file glues the trivial object of the classifying stack
`[Spec(k)/A]` over `U` and over `W` along `c`, which is the object `ξ_n` of the source.

The glueing is descent in the quotient stack: the trivial points over `U` and `W` with the arrow
`c` between them form a descent datum for the presentation of `[Spec(k)/A]` relative to the
covering `{U, W}` (Stacks 044X), and every such datum comes from an object (Stacks 044X part (4),
`AlgebraicGeometry.Stack.effective_presentingDescentDatum`).

## Main definitions

* `Deformation.Artin.triangleSite`, `Deformation.Artin.triangleOpenSite` and
  `Deformation.Artin.triangleCover`: `X_n`, `U` and `W` as objects of the big fppf site of
  `Spec k`, and the covering `{U, W}` of `X_n`.
* `Deformation.Artin.siteGroupSpace`: the group algebraic space over `Spec k` of a group scheme
  of the site (Stacks 043I).
* `Deformation.Artin.pointOfScheme`: a morphism over `Spec k` from an object of the site to `A`,
  as a point of that group algebraic space.
* `Deformation.Artin.triangleSiteCocycle`: the Čech cocycle of the covering `{U, W}` with values
  in the points of `A` given by `c`.
* `Deformation.Artin.triangleDescentDatum` and `Deformation.Artin.triangleObject`: the descent
  datum of `ξ_n` for the presentation of `[Spec(k)/A]`, and the object `ξ_n` over `X_n` it
  glues to (Stacks 044X part (4)), with `Deformation.Artin.triangleObjectIso` identifying the
  descent datum of `ξ_n` with the projection of `triangleDescentDatum`.
* `Deformation.Artin.triangleObjectTransitionIso`: the isomorphism `ξ_n ≅ ξ_{n+1}|_{X_n}`.
* `Deformation.Artin.triangleObjectMap` and `Deformation.Artin.triangleSystem`: the morphisms
  `ξ_n ⟶ ξ_{n+1}` over `X_n ⟶ X_{n+1}` and the system `ℕ ⥤ [Spec(k)/A]` they form, which lies
  over the system of thickenings `Deformation.Artin.triangleSiteSystem`
  (`Deformation.Artin.triangleSystemProjectionIso`).

## Main results

* `Deformation.Artin.triangleCover_mem`: `{U, W}` is an fppf covering of `X_n`.
* `Deformation.Artin.isRepresentedBy_triangleDescentDatum`: the descent datum of `ξ_n` is
  represented by the glueing cocycle.
* `Deformation.Artin.triangleSiteCocycle_pull_val`: the glueing cocycle of `X_{n+1}` restricts
  to that of `X_n`; this is
  `Deformation.Artin.specOverFieldMap_triangleOverlapTransition_comp_triangleCocycle`.

## Implementation notes

The transition isomorphism is obtained by descent: the descent data of `ξ_n` and of the
pullback of `ξ_{n+1}` relative to `{U_n, W_n}` are compared through Stacks 044X parts (5) and (6)
(`AlgebraicGeometry.Stack.presentingDescentFunctor_refinementIsoOver`) and the comparison of
cocycles of `CategoryTheory.Functor.Rigidification`, and the stack `[Spec(k)/A]` turns the
isomorphism of descent data into an isomorphism of objects. The site objects `X_n` are
`Spec R_n` itself, so the size of `Spec R_n` is a hypothesis `hR`; `U` and `W` are opens of it,
in the site by `AlgebraicGeometry.BigFppfOver.contains_opens`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Space
open scoped CategoryTheory.MonObj

universe u

namespace Deformation.Artin

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
  (𝒞 : BigFppfSite.{u}) (hk : 𝒞.Contains (Spec (.of k)))
  (hR : ∀ n : ℕ, 𝒞.Contains (Spec (.of (triangleLevel K n))))

/-! ### The thickened triangle and its covering as objects of the big fppf site -/

section Site

variable (k) in
/-- The structure morphism `X_n ⟶ Spec k`. -/
abbrev triangleStructure (n : ℕ) : Spec (.of (triangleLevel K n)) ⟶ Spec (.of k) :=
  (specOverField k K (triangleLevel K n)).hom

/-- The thickening `X_n` as an object of the big fppf site of `Spec k`. -/
def triangleSite (n : ℕ) : BigFppfOver 𝒞 (Spec (.of k)) hk :=
  BigFppfOver.mk 𝒞 _ hk (hR n) (triangleStructure k K n)

/-- The two opens `U = D(1 - x)` (at `false`) and `W = D(1 - y)` (at `true`) of `X_n`. -/
def triangleOpen (n : ℕ) : Bool → (Spec (.of (triangleLevel K n))).Opens
  | false => PrimeSpectrum.basicOpen (1 - triangleX K n)
  | true => PrimeSpectrum.basicOpen (1 - triangleY K n)

/-- The opens `U` and `W` of `X_n` as objects of the big fppf site of `Spec k`. -/
def triangleOpenSite (n : ℕ) (i : Bool) : BigFppfOver 𝒞 (Spec (.of k)) hk :=
  BigFppfOver.mk 𝒞 _ hk (BigFppfOver.contains_opens 𝒞 (hR n) (triangleOpen K n i))
    ((triangleOpen K n i).ι ≫ triangleStructure k K n)

/-- The inclusions of `U` and `W` into `X_n`. -/
def triangleOpenSiteι (n : ℕ) (i : Bool) :
    triangleOpenSite K 𝒞 hk hR n i ⟶ triangleSite K 𝒞 hk hR n :=
  BigFppfOver.homMk 𝒞 _ hk (hR n) (triangleStructure k K n) (triangleOpen K n i).ι rfl

@[simp]
lemma toScheme_map_triangleOpenSiteι (n : ℕ) (i : Bool) :
    (BigFppfOver.toScheme 𝒞 _ hk).map (triangleOpenSiteι K 𝒞 hk hR n i) =
      (triangleOpen K n i).ι :=
  rfl

instance (n : ℕ) (i : Bool) : Mono (triangleOpenSiteι K 𝒞 hk hR n i) :=
  (BigFppfOver.toScheme 𝒞 _ hk).mono_of_mono_map
    (inferInstance : Mono (triangleOpen K n i).ι)

/-- The covering `{U, W}` of `X_n`. -/
abbrev triangleCover (n : ℕ) : PreZeroHypercover.{0} (triangleSite K 𝒞 hk hR n) where
  I₀ := Bool
  X := triangleOpenSite K 𝒞 hk hR n
  f := triangleOpenSiteι K 𝒞 hk hR n

instance (n : ℕ) (i : (triangleCover K 𝒞 hk hR n).I₀) :
    Mono ((triangleCover K 𝒞 hk hR n).f i) :=
  (inferInstance : ∀ j : Bool, Mono (triangleOpenSiteι K 𝒞 hk hR n j)) i

/-- **`{U, W}` is a covering of `X_n`** in the big fppf site: `U` and `W` are opens whose union
is `X_n`, since `1 - x` and `1 - y` are coprime. -/
theorem triangleCover_mem (n : ℕ) :
    (triangleCover K 𝒞 hk hR n).sieve₀ ∈
      BigFppfOver.topology 𝒞 _ hk (triangleSite K 𝒞 hk hR n) := by
  refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion 𝒞 _ hk
    (triangleOpenSiteι K 𝒞 hk hR n) (fun i => ?_) (fun x => ?_)
  · exact (inferInstance : IsOpenImmersion (triangleOpen K n i).ι)
  · obtain ⟨a, b, hab⟩ := isCoprime_one_sub_triangleX_one_sub_triangleY K n
    by_cases hx : 1 - triangleX K n ∈ x.asIdeal
    · have hy : (1 - triangleY K n) ∉ x.asIdeal := fun hy =>
        x.2.ne_top ((Ideal.eq_top_iff_one _).mpr
          (hab ▸ x.asIdeal.add_mem (x.asIdeal.mul_mem_left a hx) (x.asIdeal.mul_mem_left b hy)))
      exact ⟨true, ⟨x, hy⟩, rfl⟩
    · exact ⟨false, ⟨x, hx⟩, rfl⟩

end Site

/-! ### The group algebraic space of a group scheme of the site and its points -/

section Points

variable {𝒞 hk} (A : Over (Spec (.of k))) [GrpObj A] (hA : 𝒞.Contains A.left)

/-- A group scheme over `Spec k` lying in the site, as an object of the site. -/
abbrev siteGroupScheme : BigFppfOver 𝒞 (Spec (.of k)) hk :=
  BigFppfOver.mk 𝒞 _ hk hA A.hom

instance : GrpObj ((toSchemeOver 𝒞 _ hk).obj (siteGroupScheme A hA)) :=
  inferInstanceAs (GrpObj A)

/-- **Stacks 043I** for a group scheme over `Spec k` lying in the site: the group algebraic space
over `Spec k` whose points over an object `T` of the site are the morphisms `T ⟶ A` over
`Spec k`. Its classifying stack is the quotient stack of its trivial action on `Spec k`. -/
abbrev siteGroupSpace :
    GroupAlgebraicSpace 𝒞 (Spec (.of k)) hk (baseS 𝒞 _ hk) (isAlgebraicSpace_baseS 𝒞 _ hk) :=
  GroupAlgebraicSpace.ofGroupSchemeInSite 𝒞 _ hk (baseS 𝒞 _ hk) (isAlgebraicSpace_baseS 𝒞 _ hk)
    (siteGroupScheme A hA) inferInstance

/-- A morphism over `Spec k` from an object `Y` of the site to `A`, as a point of the group
algebraic space of `A` over `Y`. -/
def pointOfScheme {Y : BigFppfOver 𝒞 (Spec (.of k)) hk} :
    ((toSchemeOver 𝒞 _ hk).obj Y ⟶ A) ≃*
      (GroupAlgebraicSpace.pointsGrpPresheaf (siteGroupSpace A hA)).obj (op Y) :=
  (GroupAlgebraicSpace.pointsMulEquiv 𝒞 _ hk (baseS 𝒞 _ hk)
    (pointsOnSite 𝒞 _ hk (siteGroupScheme A hA) inferInstance) Y (toBaseS _)).symm

/-- `pointOfScheme` is natural in the object of the site. -/
lemma pointOfScheme_naturality {Y Y' : BigFppfOver 𝒞 (Spec (.of k)) hk} (g : Y' ⟶ Y)
    (t : (toSchemeOver 𝒞 _ hk).obj Y ⟶ A) :
    pointOfScheme A hA ((toSchemeOver 𝒞 _ hk).map g ≫ t) =
      (GroupAlgebraicSpace.pointsGrpPresheaf (siteGroupSpace A hA)).map g.op
        (pointOfScheme A hA t) := by
  have key : ∀ z : (yonedaOverBaseS 𝒞 _ hk).obj Y ⟶ (siteGroupSpace A hA).obj.X,
      (pointOfScheme A hA).symm ((yonedaOverBaseS 𝒞 _ hk).map g ≫ z) =
        (toSchemeOver 𝒞 _ hk).map g ≫ (pointOfScheme A hA).symm z := fun z =>
    (yonedaEquiv_naturality (F := pointsOnSite 𝒞 _ hk (siteGroupScheme A hA) inferInstance ⋙
      forget GrpCat) (z.left ≫ prod.snd) g).symm
  apply (pointOfScheme A hA).symm.injective
  rw [MulEquiv.symm_apply_apply]
  exact ((key _).trans (by rw [MulEquiv.symm_apply_apply])).symm

end Points

/-! ### The glueing cocycle as a Čech cocycle of the covering `{U, W}` -/

section Cocycle

variable {𝒞 hk} {A : Over (Spec (.of k))} [GrpObj A] (hA : 𝒞.Contains A.left)
  (pt : specOverField k K K ⟶ A)

/-- The open immersion `U ∩ W = Spec R_n[1/((1 - x)(1 - y))] ⟶ X_n`. -/
abbrev triangleOverlapι (n : ℕ) :
    Spec (.of (triangleOverlap K n)) ⟶ Spec (.of (triangleLevel K n)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (triangleLevel K n) (triangleOverlap K n)))

/-- The morphism of schemes `Y ⟶ U` (or `Y ⟶ W`) underlying a morphism of the site. -/
abbrev triangleOpenSchemeMap {n : ℕ} {Y : BigFppfOver 𝒞 (Spec (.of k)) hk} {i : Bool}
    (a : Y ⟶ triangleOpenSite K 𝒞 hk hR n i) :
    (BigFppfOver.toScheme 𝒞 _ hk).obj Y ⟶ (triangleOpen K n i).toScheme :=
  (BigFppfOver.toScheme 𝒞 _ hk).map a

/-- The morphism of schemes `Y ⟶ X_n` underlying a morphism `Y ⟶ U` or `Y ⟶ W` of the site. -/
def triangleOpenMap {n : ℕ} {Y : BigFppfOver 𝒞 (Spec (.of k)) hk} {i : Bool}
    (a : Y ⟶ triangleOpenSite K 𝒞 hk hR n i) :
    (BigFppfOver.toScheme 𝒞 _ hk).obj Y ⟶ Spec (.of (triangleLevel K n)) :=
  triangleOpenSchemeMap K hR a ≫ (triangleOpen K n i).ι

/-- Two morphisms to `U` and `W` agreeing on `X_n` have the same underlying morphism of
schemes to `X_n`. -/
lemma triangleOpenMap_eq_of_eq {n : ℕ} {Y : BigFppfOver 𝒞 (Spec (.of k)) hk}
    {a : Y ⟶ triangleOpenSite K 𝒞 hk hR n false} {b : Y ⟶ triangleOpenSite K 𝒞 hk hR n true}
    (h : a ≫ triangleOpenSiteι K 𝒞 hk hR n false = b ≫ triangleOpenSiteι K 𝒞 hk hR n true) :
    triangleOpenMap K hR a = triangleOpenMap K hR b := by
  have e := congrArg (BigFppfOver.toScheme 𝒞 _ hk).map h
  rw [Functor.map_comp, Functor.map_comp] at e
  exact e

/-- `triangleOpenMap` is natural in `Y`. -/
lemma triangleOpenMap_comp {n : ℕ} {Y Y' : BigFppfOver 𝒞 (Spec (.of k)) hk} {i : Bool}
    (g : Y' ⟶ Y) (a : Y ⟶ triangleOpenSite K 𝒞 hk hR n i) :
    triangleOpenMap K hR (g ≫ a) =
      (BigFppfOver.toScheme 𝒞 _ hk).map g ≫ triangleOpenMap K hR a := by
  have e : triangleOpenSchemeMap K hR (g ≫ a) =
      (BigFppfOver.toScheme 𝒞 _ hk).map g ≫ triangleOpenSchemeMap K hR a :=
    (BigFppfOver.toScheme 𝒞 _ hk).map_comp g a
  rw [triangleOpenMap, triangleOpenMap, e, Category.assoc]

/-- `triangleOpenMap` lies over `Spec k`. -/
lemma triangleOpenMap_comp_triangleStructure {n : ℕ} {Y : BigFppfOver 𝒞 (Spec (.of k)) hk}
    {i : Bool} (a : Y ⟶ triangleOpenSite K 𝒞 hk hR n i) :
    triangleOpenMap K hR a ≫ triangleStructure k K n = ((toSchemeOver 𝒞 _ hk).obj Y).hom := by
  have e := congrArg 𝒞.inclusion.map (Over.w (a ≫ triangleOpenSiteι K 𝒞 hk hR n i))
  rw [Functor.map_comp, Over.comp_left, Functor.map_comp, Category.assoc] at e
  exact e

/-- A morphism to `X_n` factoring through `U` and through `W` lands in `U ∩ W`. -/
lemma range_subset_range_triangleOverlapι {n : ℕ} {Y : BigFppfOver 𝒞 (Spec (.of k)) hk}
    (a : Y ⟶ triangleOpenSite K 𝒞 hk hR n false) (b : Y ⟶ triangleOpenSite K 𝒞 hk hR n true)
    (h : a ≫ triangleOpenSiteι K 𝒞 hk hR n false = b ≫ triangleOpenSiteι K 𝒞 hk hR n true) :
    Set.range (triangleOpenMap K hR a) ⊆ Set.range (triangleOverlapι K n) := by
  have hj : Set.range (triangleOverlapι K n) =
      (PrimeSpectrum.basicOpen ((1 - triangleX K n) * (1 - triangleY K n)) :
        Set (PrimeSpectrum (triangleLevel K n))) :=
    PrimeSpectrum.localization_away_comap_range _ _
  rintro _ ⟨y, rfl⟩
  rw [hj, PrimeSpectrum.basicOpen_mul]
  refine ⟨((BigFppfOver.toScheme 𝒞 _ hk).map a y).2, ?_⟩
  rw [triangleOpenMap_eq_of_eq K hR h]
  exact ((BigFppfOver.toScheme 𝒞 _ hk).map b y).2

/-- The morphism `Y ⟶ U ∩ W` induced by two morphisms `Y ⟶ U`, `Y ⟶ W` agreeing on `X_n`. -/
def triangleOverlapLift {n : ℕ} {Y : BigFppfOver 𝒞 (Spec (.of k)) hk}
    (a : Y ⟶ triangleOpenSite K 𝒞 hk hR n false) (b : Y ⟶ triangleOpenSite K 𝒞 hk hR n true)
    (h : a ≫ triangleOpenSiteι K 𝒞 hk hR n false = b ≫ triangleOpenSiteι K 𝒞 hk hR n true) :
    (BigFppfOver.toScheme 𝒞 _ hk).obj Y ⟶ Spec (.of (triangleOverlap K n)) :=
  IsOpenImmersion.lift (triangleOverlapι K n) (triangleOpenMap K hR a)
    (range_subset_range_triangleOverlapι K hR a b h)

@[reassoc (attr := simp)]
lemma triangleOverlapLift_ι {n : ℕ} {Y : BigFppfOver 𝒞 (Spec (.of k)) hk}
    (a : Y ⟶ triangleOpenSite K 𝒞 hk hR n false) (b : Y ⟶ triangleOpenSite K 𝒞 hk hR n true)
    (h : a ≫ triangleOpenSiteι K 𝒞 hk hR n false = b ≫ triangleOpenSiteι K 𝒞 hk hR n true) :
    triangleOverlapLift K hR a b h ≫ triangleOverlapι K n = triangleOpenMap K hR a :=
  IsOpenImmersion.lift_fac _ _ _

/-- The structure morphism of `U ∩ W` to `Spec k` factors through `X_n`. -/
lemma triangleOverlapι_comp_triangleStructure (n : ℕ) :
    triangleOverlapι K n ≫ triangleStructure k K n =
      (specOverField k K (triangleOverlap K n)).hom := by
  simp only [Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

/-- `triangleOverlapLift` as a morphism of schemes over `Spec k`. -/
def triangleOverlapLiftOver {n : ℕ} {Y : BigFppfOver 𝒞 (Spec (.of k)) hk}
    (a : Y ⟶ triangleOpenSite K 𝒞 hk hR n false) (b : Y ⟶ triangleOpenSite K 𝒞 hk hR n true)
    (h : a ≫ triangleOpenSiteι K 𝒞 hk hR n false = b ≫ triangleOpenSiteι K 𝒞 hk hR n true) :
    (toSchemeOver 𝒞 _ hk).obj Y ⟶ specOverField k K (triangleOverlap K n) :=
  Over.homMk (triangleOverlapLift K hR a b h) (by
    refine Eq.trans (?_ : _ = triangleOpenMap K hR a ≫ triangleStructure k K n)
      (triangleOpenMap_comp_triangleStructure K hR a)
    have e : triangleOverlapLift K hR a b h ≫ (specOverField k K (triangleOverlap K n)).hom =
        triangleOpenMap K hR a ≫ triangleStructure k K n := by
      rw [← triangleOverlapι_comp_triangleStructure, triangleOverlapLift_ι_assoc]
    exact e)

/-- `triangleOverlapLift` is natural in `Y`. -/
lemma triangleOverlapLift_comp {n : ℕ} {Y Y' : BigFppfOver 𝒞 (Spec (.of k)) hk}
    (g : Y' ⟶ Y) (a : Y ⟶ triangleOpenSite K 𝒞 hk hR n false)
    (b : Y ⟶ triangleOpenSite K 𝒞 hk hR n true)
    (h : a ≫ triangleOpenSiteι K 𝒞 hk hR n false = b ≫ triangleOpenSiteι K 𝒞 hk hR n true)
    (h' : (g ≫ a) ≫ triangleOpenSiteι K 𝒞 hk hR n false =
      (g ≫ b) ≫ triangleOpenSiteι K 𝒞 hk hR n true) :
    triangleOverlapLift K hR (g ≫ a) (g ≫ b) h' =
      (BigFppfOver.toScheme 𝒞 _ hk).map g ≫ triangleOverlapLift K hR a b h :=
  (IsOpenImmersion.lift_uniq (f := triangleOverlapι K n) (g := triangleOpenMap K hR (g ≫ a))
    (range_subset_range_triangleOverlapι K hR _ _ h') _
    (by rw [Category.assoc, triangleOverlapLift_ι, triangleOpenMap_comp])).symm

/-- `triangleOverlapLiftOver` is natural in `Y`. -/
lemma triangleOverlapLiftOver_comp {n : ℕ} {Y Y' : BigFppfOver 𝒞 (Spec (.of k)) hk}
    (g : Y' ⟶ Y) (a : Y ⟶ triangleOpenSite K 𝒞 hk hR n false)
    (b : Y ⟶ triangleOpenSite K 𝒞 hk hR n true)
    (h : a ≫ triangleOpenSiteι K 𝒞 hk hR n false = b ≫ triangleOpenSiteι K 𝒞 hk hR n true)
    (h' : (g ≫ a) ≫ triangleOpenSiteι K 𝒞 hk hR n false =
      (g ≫ b) ≫ triangleOpenSiteι K 𝒞 hk hR n true) :
    triangleOverlapLiftOver K hR (g ≫ a) (g ≫ b) h' =
      (toSchemeOver 𝒞 _ hk).map g ≫ triangleOverlapLiftOver K hR a b h := by
  ext1
  exact triangleOverlapLift_comp K hR g a b h h'

open Classical in
/-- The value of the glueing cocycle on a pair `(Y ⟶ U, Y ⟶ W)` agreeing on `X_n`: the point of
`A` over `Y` obtained from `Y ⟶ U ∩ W` and the glueing cocycle `U ∩ W ⟶ A`. -/
def triangleGamma (n : ℕ) ⦃Y : BigFppfOver 𝒞 (Spec (.of k)) hk⦄
    (a : Y ⟶ triangleOpenSite K 𝒞 hk hR n false) (b : Y ⟶ triangleOpenSite K 𝒞 hk hR n true) :
    (GroupAlgebraicSpace.pointsGrpPresheaf (siteGroupSpace A hA)).obj (op Y) :=
  if h : a ≫ triangleOpenSiteι K 𝒞 hk hR n false = b ≫ triangleOpenSiteι K 𝒞 hk hR n true then
    pointOfScheme A hA (triangleOverlapLiftOver K hR a b h ≫ triangleCocycle K n A pt)
  else 1

lemma triangleGamma_of_eq (n : ℕ) {Y : BigFppfOver 𝒞 (Spec (.of k)) hk}
    (a : Y ⟶ triangleOpenSite K 𝒞 hk hR n false) (b : Y ⟶ triangleOpenSite K 𝒞 hk hR n true)
    (h : a ≫ triangleOpenSiteι K 𝒞 hk hR n false = b ≫ triangleOpenSiteι K 𝒞 hk hR n true) :
    triangleGamma K hR hA pt n a b =
      pointOfScheme A hA (triangleOverlapLiftOver K hR a b h ≫ triangleCocycle K n A pt) := by
  classical
  exact dite_eq_left_of_eq_true (eq_true h)

/-- **The glueing cocycle as a Čech cocycle** of the covering `{U, W}` of `X_n` with values in
the points of `A`: its value on a pair `(Y ⟶ U, Y ⟶ W)` is the glueing cocycle read on
`Y ⟶ U ∩ W`. -/
def triangleSiteCocycle (n : ℕ) :
    Functor.FamilyCocycle (GroupAlgebraicSpace.pointsGrpPresheaf (siteGroupSpace A hA))
      (triangleCover K 𝒞 hk hR n).f :=
  Functor.FamilyCocycle.ofPair (X := triangleOpenSite K 𝒞 hk hR n) (triangleOpenSiteι K 𝒞 hk hR n)
    (triangleGamma K hR hA pt n) (fun Y Y' g a b h => by
      have h' : (g ≫ a) ≫ triangleOpenSiteι K 𝒞 hk hR n false =
          (g ≫ b) ≫ triangleOpenSiteι K 𝒞 hk hR n true := by
        simp only [Category.assoc, h]
      rw [triangleGamma_of_eq K hR hA pt n _ _ h', triangleGamma_of_eq K hR hA pt n a b h,
        triangleOverlapLiftOver_comp K hR g a b h h', Category.assoc, pointOfScheme_naturality])

lemma triangleSiteCocycle_val_false_true (n : ℕ) {Y : BigFppfOver 𝒞 (Spec (.of k)) hk}
    (a : Y ⟶ triangleOpenSite K 𝒞 hk hR n false) (b : Y ⟶ triangleOpenSite K 𝒞 hk hR n true) :
    (triangleSiteCocycle K hR hA pt n).val (i₁ := false) (i₂ := true) a b =
      triangleGamma K hR hA pt n a b :=
  rfl

lemma triangleSiteCocycle_val_true_false (n : ℕ) {Y : BigFppfOver 𝒞 (Spec (.of k)) hk}
    (b : Y ⟶ triangleOpenSite K 𝒞 hk hR n true) (a : Y ⟶ triangleOpenSite K 𝒞 hk hR n false) :
    (triangleSiteCocycle K hR hA pt n).val (i₁ := true) (i₂ := false) b a =
      (triangleGamma K hR hA pt n a b)⁻¹ :=
  rfl

lemma triangleSiteCocycle_val_self (n : ℕ) {Y : BigFppfOver 𝒞 (Spec (.of k)) hk} {i : Bool}
    (a a' : Y ⟶ triangleOpenSite K 𝒞 hk hR n i) :
    (triangleSiteCocycle K hR hA pt n).val (i₁ := i) (i₂ := i) a a' = 1 := by
  cases i <;> rfl

end Cocycle

/-! ### The glued object `ξ_n` -/

section Object

variable {A : Over (Spec (.of k))} [GrpObj A] (hA : 𝒞.Contains A.left)
  (pt : specOverField k K K ⟶ A)

/-- **The descent datum of `ξ_n`** for the presentation of `[Spec(k)/A]` relative to the
covering `{U, W}` of `X_n`: the trivial point over `U` and over `W`, glued by the arrows given
by the glueing cocycle. -/
def triangleDescentDatum (n : ℕ) :
    Functor.FamilyDescentDatum
      (Stack.quotientPrestack (baseTrivialActionGroupoid (siteGroupSpace A hA))).p
      (triangleCover K 𝒞 hk hR n) :=
  (trivialActionRigidification (siteGroupSpace A hA)).descentDatumOfCocycle
    (fun i => trivialActionPoint (siteGroupSpace A hA) ((triangleCover K 𝒞 hk hR n).X i))
    (triangleSiteCocycle K hR hA pt n)

/-- The descent datum of `ξ_n` is represented by the glueing cocycle. -/
lemma isRepresentedBy_triangleDescentDatum (n : ℕ) :
    (trivialActionRigidification (siteGroupSpace A hA)).IsRepresentedBy
      (triangleDescentDatum K 𝒞 hk hR hA pt n) (triangleSiteCocycle K hR hA pt n) :=
  (trivialActionRigidification (siteGroupSpace A hA)).isRepresentedBy_descentDatumOfCocycle _ _

/-- The glueing of the descent datum of `ξ_n` exists (Stacks 044X part (4)). -/
lemma exists_triangleObject (n : ℕ) :
    ∃ x : (Stack.quotientStack (baseTrivialActionGroupoid (siteGroupSpace A hA))).p.Fiber
        (triangleSite K 𝒞 hk hR n),
      Nonempty ((Functor.toFamilyDescentDatum
        (Stack.quotientStack (baseTrivialActionGroupoid (siteGroupSpace A hA))).p
          (triangleCover K 𝒞 hk hR n)).obj x ≅
        (Stack.presentingDescentFunctor (baseTrivialActionGroupoid (siteGroupSpace A hA))
          (triangleCover K 𝒞 hk hR n)).obj (triangleDescentDatum K 𝒞 hk hR hA pt n)) :=
  Stack.effective_presentingDescentDatum _ _ (triangleCover_mem K 𝒞 hk hR n) _

/-- **The object `ξ_n` of `[Spec(k)/A]` over `X_n`**: the trivial object over `U` and over `W`,
glued along the glueing cocycle on `U ∩ W`. -/
def triangleObject (n : ℕ) :
    (Stack.quotientStack (baseTrivialActionGroupoid (siteGroupSpace A hA))).p.Fiber
      (triangleSite K 𝒞 hk hR n) :=
  (exists_triangleObject K 𝒞 hk hR hA pt n).choose

/-- The descent datum of `ξ_n` relative to `{U, W}` is the projection of
`triangleDescentDatum`. -/
def triangleObjectIso (n : ℕ) :
    (Functor.toFamilyDescentDatum
      (Stack.quotientStack (baseTrivialActionGroupoid (siteGroupSpace A hA))).p
        (triangleCover K 𝒞 hk hR n)).obj (triangleObject K 𝒞 hk hR hA pt n) ≅
      (Stack.presentingDescentFunctor (baseTrivialActionGroupoid (siteGroupSpace A hA))
        (triangleCover K 𝒞 hk hR n)).obj (triangleDescentDatum K 𝒞 hk hR hA pt n) :=
  (exists_triangleObject K 𝒞 hk hR hA pt n).choose_spec.some

end Object

/-! ### The transition maps `X_n ⟶ X_{n+1}` -/

section Transition

variable {𝒞 hk}

/-- The closed immersion `X_n ⟶ X_{n+1}` of schemes. -/
abbrev triangleSchemeTransition (n : ℕ) :
    Spec (.of (triangleLevel K n)) ⟶ Spec (.of (triangleLevel K (n + 1))) :=
  Spec.map (CommRingCat.ofHom (triangleTransition K n).toRingHom)

lemma triangleSchemeTransition_comp_triangleStructure (n : ℕ) :
    triangleSchemeTransition K n ≫ triangleStructure k K (n + 1) = triangleStructure k K n := by
  simp only [Over.mk_hom]
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    show (triangleTransition K n).toRingHom.comp (algebraMap K (triangleLevel K (n + 1))) =
      algebraMap K (triangleLevel K n) from RingHom.ext (triangleTransition K n).commutes]

variable (𝒞 hk) in
/-- The closed immersion `X_n ⟶ X_{n+1}` in the big fppf site. -/
def triangleSiteTransition (n : ℕ) :
    triangleSite K 𝒞 hk hR n ⟶ triangleSite K 𝒞 hk hR (n + 1) :=
  BigFppfOver.homMk 𝒞 _ hk (hR (n + 1)) (triangleStructure k K (n + 1))
    (triangleSchemeTransition K n) (triangleSchemeTransition_comp_triangleStructure K n)

/-- `X_n ⟶ X_{n+1}` sends `U` to `U` and `W` to `W`. -/
lemma triangleOpen_le_preimage (n : ℕ) (i : Bool) :
    triangleOpen K n i ≤ triangleSchemeTransition K n ⁻¹ᵁ triangleOpen K (n + 1) i := by
  intro y hy
  cases i
  · change (1 - triangleX K n) ∉ y.asIdeal at hy
    change (1 - triangleX K (n + 1)) ∉ Ideal.comap (triangleTransition K n).toRingHom y.asIdeal
    rw [Ideal.mem_comap]
    simpa using hy
  · change (1 - triangleY K n) ∉ y.asIdeal at hy
    change (1 - triangleY K (n + 1)) ∉ Ideal.comap (triangleTransition K n).toRingHom y.asIdeal
    rw [Ideal.mem_comap]
    simpa using hy

/-- The restriction `U_n ⟶ U_{n+1}` (resp. `W_n ⟶ W_{n+1}`) of `X_n ⟶ X_{n+1}`. -/
abbrev triangleOpenTransitionScheme (n : ℕ) (i : Bool) :
    (triangleOpen K n i).toScheme ⟶ (triangleOpen K (n + 1) i).toScheme :=
  (triangleSchemeTransition K n).resLE _ _ (triangleOpen_le_preimage K n i)

variable (𝒞 hk) in
/-- The restriction `U_n ⟶ U_{n+1}` (resp. `W_n ⟶ W_{n+1}`) in the big fppf site. -/
def triangleOpenSiteTransition (n : ℕ) (i : Bool) :
    triangleOpenSite K 𝒞 hk hR n i ⟶ triangleOpenSite K 𝒞 hk hR (n + 1) i :=
  BigFppfOver.homMk 𝒞 _ hk (BigFppfOver.contains_opens 𝒞 (hR (n + 1)) (triangleOpen K (n + 1) i))
    ((triangleOpen K (n + 1) i).ι ≫ triangleStructure k K (n + 1))
    (triangleOpenTransitionScheme K n i) (by
      have e : triangleOpenTransitionScheme K n i ≫ (triangleOpen K (n + 1) i).ι ≫
          triangleStructure k K (n + 1) = (triangleOpen K n i).ι ≫ triangleStructure k K n := by
        rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
          triangleSchemeTransition_comp_triangleStructure]
      exact e)

/-- The restrictions `U_n ⟶ U_{n+1}` and `W_n ⟶ W_{n+1}` lie over `X_n ⟶ X_{n+1}`. -/
@[reassoc]
lemma triangleOpenSiteTransition_comp_ι (n : ℕ) (i : Bool) :
    triangleOpenSiteTransition K 𝒞 hk hR n i ≫ triangleOpenSiteι K 𝒞 hk hR (n + 1) i =
      triangleOpenSiteι K 𝒞 hk hR n i ≫ triangleSiteTransition K 𝒞 hk hR n :=
  (BigFppfOver.toScheme 𝒞 _ hk).map_injective (by
    have e : triangleOpenTransitionScheme K n i ≫ (triangleOpen K (n + 1) i).ι =
        (triangleOpen K n i).ι ≫ triangleSchemeTransition K n :=
      Scheme.Hom.resLE_comp_ι _ _
    rw [Functor.map_comp, Functor.map_comp]
    exact e)

variable (𝒞 hk) in
/-- The covering `{U_n, W_n}` of `X_n` maps to the covering `{U_{n+1}, W_{n+1}}` of `X_{n+1}`
over `X_n ⟶ X_{n+1}`. -/
def triangleCoverTransition (n : ℕ) :
    (triangleCover K 𝒞 hk hR n).HomOver (triangleCover K 𝒞 hk hR (n + 1))
      (triangleSiteTransition K 𝒞 hk hR n) where
  s₀ i := i
  h₀ i := triangleOpenSiteTransition K 𝒞 hk hR n i
  w₀ i := triangleOpenSiteTransition_comp_ι K hR n i

/-- `triangleOpenMap` of a composite with the restriction `U_n ⟶ U_{n+1}`. -/
lemma triangleOpenMap_transition (n : ℕ) {Y : BigFppfOver 𝒞 (Spec (.of k)) hk} {i : Bool}
    (a : Y ⟶ triangleOpenSite K 𝒞 hk hR n i) :
    triangleOpenMap K hR (a ≫ triangleOpenSiteTransition K 𝒞 hk hR n i) =
      triangleOpenMap K hR a ≫ triangleSchemeTransition K n := by
  have e : triangleOpenSchemeMap K hR (a ≫ triangleOpenSiteTransition K 𝒞 hk hR n i) =
      triangleOpenSchemeMap K hR a ≫ triangleOpenTransitionScheme K n i :=
    (BigFppfOver.toScheme 𝒞 _ hk).map_comp _ _
  rw [triangleOpenMap, triangleOpenMap, e, Category.assoc, Scheme.Hom.resLE_comp_ι,
    Category.assoc]

/-- The transition of the overlaps is compatible with the open immersions into the
thickenings. -/
lemma triangleOverlapTransition_comp_ι (n : ℕ) :
    Spec.map (CommRingCat.ofHom (triangleOverlapTransition K n).toRingHom) ≫
        triangleOverlapι K (n + 1) =
      triangleOverlapι K n ≫ triangleSchemeTransition K n := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    show (triangleOverlapTransition K n).toRingHom.comp (algebraMap _ _) =
      (algebraMap _ _).comp (triangleTransition K n).toRingHom from
      RingHom.ext (triangleOverlapTransition_algebraMap K n)]

lemma triangleOverlapLift_transition (n : ℕ) {Y : BigFppfOver 𝒞 (Spec (.of k)) hk}
    (a : Y ⟶ triangleOpenSite K 𝒞 hk hR n false) (b : Y ⟶ triangleOpenSite K 𝒞 hk hR n true)
    (h : a ≫ triangleOpenSiteι K 𝒞 hk hR n false = b ≫ triangleOpenSiteι K 𝒞 hk hR n true)
    (h' : (a ≫ triangleOpenSiteTransition K 𝒞 hk hR n false) ≫
        triangleOpenSiteι K 𝒞 hk hR (n + 1) false =
      (b ≫ triangleOpenSiteTransition K 𝒞 hk hR n true) ≫
        triangleOpenSiteι K 𝒞 hk hR (n + 1) true) :
    triangleOverlapLift K hR (a ≫ triangleOpenSiteTransition K 𝒞 hk hR n false)
        (b ≫ triangleOpenSiteTransition K 𝒞 hk hR n true) h' =
      triangleOverlapLift K hR a b h ≫
        Spec.map (CommRingCat.ofHom (triangleOverlapTransition K n).toRingHom) :=
  (IsOpenImmersion.lift_uniq (f := triangleOverlapι K (n + 1))
    (g := triangleOpenMap K hR (a ≫ triangleOpenSiteTransition K 𝒞 hk hR n false))
    (range_subset_range_triangleOverlapι K hR _ _ h') _ (by
      rw [Category.assoc, triangleOverlapTransition_comp_ι, triangleOverlapLift_ι_assoc,
        triangleOpenMap_transition])).symm

variable {A : Over (Spec (.of k))} [GrpObj A] (hA : 𝒞.Contains A.left)
  (pt : specOverField k K K ⟶ A)

/-- **The value of the glueing cocycle is compatible with the transitions.** -/
lemma triangleGamma_transition (n : ℕ) {Y : BigFppfOver 𝒞 (Spec (.of k)) hk}
    (a : Y ⟶ triangleOpenSite K 𝒞 hk hR n false) (b : Y ⟶ triangleOpenSite K 𝒞 hk hR n true)
    (h : a ≫ triangleOpenSiteι K 𝒞 hk hR n false = b ≫ triangleOpenSiteι K 𝒞 hk hR n true) :
    triangleGamma K hR hA pt (n + 1) (a ≫ triangleOpenSiteTransition K 𝒞 hk hR n false)
        (b ≫ triangleOpenSiteTransition K 𝒞 hk hR n true) =
      triangleGamma K hR hA pt n a b := by
  have h' : (a ≫ triangleOpenSiteTransition K 𝒞 hk hR n false) ≫
        triangleOpenSiteι K 𝒞 hk hR (n + 1) false =
      (b ≫ triangleOpenSiteTransition K 𝒞 hk hR n true) ≫
        triangleOpenSiteι K 𝒞 hk hR (n + 1) true := by
    rw [Category.assoc, Category.assoc, triangleOpenSiteTransition_comp_ι,
      triangleOpenSiteTransition_comp_ι, reassoc_of% h]
  have e : triangleOverlapLiftOver K hR (a ≫ triangleOpenSiteTransition K 𝒞 hk hR n false)
      (b ≫ triangleOpenSiteTransition K 𝒞 hk hR n true) h' =
        triangleOverlapLiftOver K hR a b h ≫ specOverFieldMap (triangleOverlapTransition K n) :=
    Over.OverMorphism.ext (triangleOverlapLift_transition K hR n a b h h')
  rw [triangleGamma_of_eq K hR hA pt (n + 1) _ _ h', triangleGamma_of_eq K hR hA pt n a b h, e,
    Category.assoc, specOverFieldMap_triangleOverlapTransition_comp_triangleCocycle]

/-- **The glueing cocycle of `X_{n+1}`, pulled back to `X_n`, is the glueing cocycle of `X_n`.** -/
lemma triangleSiteCocycle_pull_val (n : ℕ) {Y : BigFppfOver 𝒞 (Spec (.of k)) hk} {i₁ i₂ : Bool}
    (f₁ : Y ⟶ triangleOpenSite K 𝒞 hk hR n i₁) (f₂ : Y ⟶ triangleOpenSite K 𝒞 hk hR n i₂)
    (h : f₁ ≫ triangleOpenSiteι K 𝒞 hk hR n i₁ = f₂ ≫ triangleOpenSiteι K 𝒞 hk hR n i₂) :
    ((triangleSiteCocycle K hR hA pt (n + 1)).pull (triangleCoverTransition K 𝒞 hk hR n)).val
        f₁ f₂ = (triangleSiteCocycle K hR hA pt n).val f₁ f₂ := by
  rw [Functor.FamilyCocycle.pull_val]
  cases i₁ <;> cases i₂
  · rw [triangleSiteCocycle_val_self]
    exact (triangleSiteCocycle_val_self K hR hA pt n _ _).symm
  · rw [triangleSiteCocycle_val_false_true]
    exact (triangleSiteCocycle_val_false_true K hR hA pt (n + 1)
      (f₁ ≫ triangleOpenSiteTransition K 𝒞 hk hR n false)
      (f₂ ≫ triangleOpenSiteTransition K 𝒞 hk hR n true)).trans
      (triangleGamma_transition K hR hA pt n f₁ f₂ h)
  · rw [triangleSiteCocycle_val_true_false]
    exact (triangleSiteCocycle_val_true_false K hR hA pt (n + 1)
      (f₁ ≫ triangleOpenSiteTransition K 𝒞 hk hR n true)
      (f₂ ≫ triangleOpenSiteTransition K 𝒞 hk hR n false)).trans
      (congrArg (·⁻¹) (triangleGamma_transition K hR hA pt n f₂ f₁ h.symm))
  · rw [triangleSiteCocycle_val_self]
    exact (triangleSiteCocycle_val_self K hR hA pt n _ _).symm

variable (𝒞 hk) in
/-- **The descent datum of `ξ_{n+1}`, pulled back to `X_n`, is isomorphic to that of `ξ_n`**:
both are represented by the glueing cocycle of `X_n`, up to the twist by the elements of the
chosen cartesian lifts along which the pullback is formed. -/
def triangleDescentDatumIso (n : ℕ) :
    triangleDescentDatum K 𝒞 hk hR hA pt n ≅
      Functor.FamilyDescentDatum.pull _ (triangleCoverTransition K 𝒞 hk hR n)
        (triangleDescentDatum K 𝒞 hk hR hA pt (n + 1)) :=
  (trivialActionRigidification (siteGroupSpace A hA)).isoOfIsRepresentedBy
    (isRepresentedBy_triangleDescentDatum K 𝒞 hk hR hA pt n)
    ((trivialActionRigidification (siteGroupSpace A hA)).isRepresentedBy_pull
      (triangleCoverTransition K 𝒞 hk hR n)
      (isRepresentedBy_triangleDescentDatum K 𝒞 hk hR hA pt (n + 1)))
    (fun i => ((trivialActionRigidification (siteGroupSpace A hA)).cartElt
      ((triangleDescentDatum K 𝒞 hk hR hA pt (n + 1)).obj
        ((triangleCoverTransition K 𝒞 hk hR n).s₀ i))
      ((triangleCoverTransition K 𝒞 hk hR n).h₀ i))⁻¹)
    (fun Y i₁ i₂ f₁ f₂ h => by
      rw [Functor.FamilyCocycle.twist_val, Functor.FamilyCocycle.twist_val,
        triangleSiteCocycle_pull_val K hR hA pt n f₁ f₂ h])

/-- The quotient stack `[Spec(k)/A]`, for short. -/
local notation3 "𝒬" =>
  (Stack.quotientStack (baseTrivialActionGroupoid (siteGroupSpace (hk := hk) A hA))).p

/-- The presentation of `[Spec(k)/A]`, for short. -/
local notation3 "𝒫" =>
  (Stack.quotientPrestack (baseTrivialActionGroupoid (siteGroupSpace (hk := hk) A hA))).p

variable (𝒞 hk) in
/-- Pulling back the descent datum of `ξ_{n+1}` to `{U_n, W_n}` commutes with the projection
to the quotient stack (Stacks 044X part (6)). -/
def triangleObjectPullIso (n : ℕ) :
    (Stack.presentingDescentFunctor (baseTrivialActionGroupoid (siteGroupSpace A hA))
      (triangleCover K 𝒞 hk hR n)).obj
        (Functor.FamilyDescentDatum.pull 𝒫 (triangleCoverTransition K 𝒞 hk hR n)
          (triangleDescentDatum K 𝒞 hk hR hA pt (n + 1))) ≅
      (Functor.FamilyDescentDatum.pullFunctor 𝒬 (triangleCoverTransition K 𝒞 hk hR n)).obj
        ((Stack.presentingDescentFunctor (baseTrivialActionGroupoid (siteGroupSpace A hA))
          (triangleCover K 𝒞 hk hR (n + 1))).obj (triangleDescentDatum K 𝒞 hk hR hA pt (n + 1))) :=
  ((Stack.presentingDescentFunctor_refinementIsoOver _
    (triangleCoverTransition K 𝒞 hk hR n)).app
      (triangleDescentDatum K 𝒞 hk hR hA pt (n + 1))).symm

variable (𝒞 hk) in
/-- The descent datum of the pullback of `ξ_{n+1}` to `X_n` is the pullback of the descent datum
of `ξ_{n+1}`. -/
def triangleObjectPullbackIso (n : ℕ) :
    (Functor.FamilyDescentDatum.pullFunctor 𝒬 (triangleCoverTransition K 𝒞 hk hR n)).obj
        ((Functor.toFamilyDescentDatum 𝒬 (triangleCover K 𝒞 hk hR (n + 1))).obj
          (triangleObject K 𝒞 hk hR hA pt (n + 1))) ≅
      (Functor.toFamilyDescentDatum 𝒬 (triangleCover K 𝒞 hk hR n)).obj
        (((Functor.IsFibered.pullbackPseudofunctor 𝒬).map
          (triangleSiteTransition K 𝒞 hk hR n).op.toLoc).toFunctor.obj
            (triangleObject K 𝒞 hk hR hA pt (n + 1))) :=
  (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
    (Functor.IsFibered.pullbackPseudofunctor 𝒬) (f := (triangleCover K 𝒞 hk hR (n + 1)).f)
    (f' := (triangleCover K 𝒞 hk hR n).f) (p := triangleSiteTransition K 𝒞 hk hR n)
    (α := (triangleCoverTransition K 𝒞 hk hR n).s₀)
    (p' := (triangleCoverTransition K 𝒞 hk hR n).h₀)
    (triangleCoverTransition K 𝒞 hk hR n).w₀).app (triangleObject K 𝒞 hk hR hA pt (n + 1))

variable (𝒞 hk) in
/-- The descent data relative to `{U_n, W_n}` of `ξ_n` and of the pullback of `ξ_{n+1}` to `X_n`
are isomorphic: Stacks 044X part (6) commutes the projection to `[Spec(k)/A]` with pulling back,
and `triangleDescentDatumIso` compares the presenting data. -/
def triangleObjectDescentIso (n : ℕ) :
    (Functor.toFamilyDescentDatum 𝒬 (triangleCover K 𝒞 hk hR n)).obj
        (triangleObject K 𝒞 hk hR hA pt n) ≅
      (Functor.toFamilyDescentDatum 𝒬 (triangleCover K 𝒞 hk hR n)).obj
        (((Functor.IsFibered.pullbackPseudofunctor 𝒬).map
          (triangleSiteTransition K 𝒞 hk hR n).op.toLoc).toFunctor.obj
            (triangleObject K 𝒞 hk hR hA pt (n + 1))) :=
  triangleObjectIso K 𝒞 hk hR hA pt n ≪≫
    (Stack.presentingDescentFunctor _ _).mapIso (triangleDescentDatumIso K 𝒞 hk hR hA pt n) ≪≫
    triangleObjectPullIso K 𝒞 hk hR hA pt n ≪≫
    (Functor.FamilyDescentDatum.pullFunctor 𝒬 (triangleCoverTransition K 𝒞 hk hR n)).mapIso
      (triangleObjectIso K 𝒞 hk hR hA pt (n + 1)).symm ≪≫
    triangleObjectPullbackIso K 𝒞 hk hR hA pt n

variable (𝒞 hk) in
/-- **The transition isomorphism `ξ_n ≅ ξ_{n+1}|_{X_n}`** in the fibre of `[Spec(k)/A]` over
`X_n`: descent in the stack `[Spec(k)/A]` along the covering `{U_n, W_n}` is fully faithful, and
the two descent data agree by `triangleObjectDescentIso`. -/
def triangleObjectTransitionIso (n : ℕ) :
    triangleObject K 𝒞 hk hR hA pt n ≅
      ((Functor.IsFibered.pullbackPseudofunctor 𝒬).map
        (triangleSiteTransition K 𝒞 hk hR n).op.toLoc).toFunctor.obj
          (triangleObject K 𝒞 hk hR hA pt (n + 1)) :=
  haveI : (Functor.toFamilyDescentDatum 𝒬 (triangleCover K 𝒞 hk hR n)).IsEquivalence :=
    Functor.isEquivalence_toDescentData_of_isStack _
      (Stack.isStack_quotientStack (baseTrivialActionGroupoid (siteGroupSpace A hA)))
      (triangleCover K 𝒞 hk hR n).f (triangleCover_mem K 𝒞 hk hR n)
  (Functor.toFamilyDescentDatum 𝒬 (triangleCover K 𝒞 hk hR n)).preimageIso
    (triangleObjectDescentIso K 𝒞 hk hR hA pt n)

variable (𝒞 hk) in
/-- **The morphism `ξ_n ⟶ ξ_{n+1}` of `[Spec(k)/A]` over `X_n ⟶ X_{n+1}`**: the transition
isomorphism followed by the chosen cartesian lift. -/
def triangleObjectMap (n : ℕ) :
    (triangleObject K 𝒞 hk hR hA pt n).1 ⟶ (triangleObject K 𝒞 hk hR hA pt (n + 1)).1 :=
  Functor.Fiber.fiberInclusion.map (triangleObjectTransitionIso K 𝒞 hk hR hA pt n).hom ≫
    Functor.IsPreFibered.pullbackMap (triangleObject K 𝒞 hk hR hA pt (n + 1)).2
      (triangleSiteTransition K 𝒞 hk hR n)

/-- The morphism `ξ_n ⟶ ξ_{n+1}` lies over `X_n ⟶ X_{n+1}`. -/
instance isHomLift_triangleObjectMap (n : ℕ) :
    Functor.IsHomLift 𝒬 (triangleSiteTransition K 𝒞 hk hR n)
      (triangleObjectMap K 𝒞 hk hR hA pt n) :=
  haveI h₂ : Functor.IsHomLift 𝒬 (triangleSiteTransition K 𝒞 hk hR n)
      (Functor.IsPreFibered.pullbackMap (triangleObject K 𝒞 hk hR hA pt (n + 1)).2
        (triangleSiteTransition K 𝒞 hk hR n)) := inferInstance
  have h := @IsHomLift.comp _ _ _ _ 𝒬 _ _ _ _ _ _ (𝟙 _) (triangleSiteTransition K 𝒞 hk hR n)
    (Functor.Fiber.fiberInclusion.map (triangleObjectTransitionIso K 𝒞 hk hR hA pt n).hom)
    (Functor.IsPreFibered.pullbackMap (triangleObject K 𝒞 hk hR hA pt (n + 1)).2
      (triangleSiteTransition K 𝒞 hk hR n))
    (triangleObjectTransitionIso K 𝒞 hk hR hA pt n).hom.2 h₂
  by rw [Category.id_comp] at h; exact h

variable (𝒞 hk) in
/-- The inverse system of thickenings `X_0 ⟶ X_1 ⟶ ⋯` in the big fppf site of `Spec k`. -/
def triangleSiteSystem : ℕ ⥤ BigFppfOver 𝒞 (Spec (.of k)) hk :=
  Functor.ofSequence (triangleSiteTransition K 𝒞 hk hR)

variable (𝒞 hk) in
/-- **The system `ξ_0 ⟶ ξ_1 ⟶ ⋯` of objects of `[Spec(k)/A]`** over the thickenings of the
triangle. -/
def triangleSystem :
    ℕ ⥤ (Stack.quotientStack (baseTrivialActionGroupoid (siteGroupSpace (hk := hk) A hA))).obj :=
  Functor.ofSequence (triangleObjectMap K 𝒞 hk hR hA pt)

lemma triangleSiteSystem_map_succ (n : ℕ) :
    (triangleSiteSystem K 𝒞 hk hR).map (homOfLE (Nat.le_succ n)) =
      triangleSiteTransition K 𝒞 hk hR n :=
  Functor.ofSequence_map_homOfLE_succ _ n

lemma triangleSystem_map_succ (n : ℕ) :
    (triangleSystem K 𝒞 hk hR hA pt).map (homOfLE (Nat.le_succ n)) =
      triangleObjectMap K 𝒞 hk hR hA pt n :=
  Functor.ofSequence_map_homOfLE_succ _ n

variable (𝒞 hk) in
/-- The system of objects lies over the system of thickenings, the identification over `X_n`
being the equality `p (ξ_n) = X_n` of the fibre. -/
def triangleSystemProjectionHom :
    triangleSystem K 𝒞 hk hR hA pt ⋙ 𝒬 ⟶ triangleSiteSystem K 𝒞 hk hR :=
  NatTrans.ofSequence (fun n => eqToHom (triangleObject K 𝒞 hk hR hA pt n).2) (fun n => by
    change (Stack.quotientStack (baseTrivialActionGroupoid (siteGroupSpace (hk := hk) A hA))).p.map
        ((triangleSystem K 𝒞 hk hR hA pt).map (homOfLE (Nat.le_succ n))) ≫ _ =
      _ ≫ (triangleSiteSystem K 𝒞 hk hR).map (homOfLE (Nat.le_succ n))
    rw [triangleSystem_map_succ, triangleSiteSystem_map_succ]
    refine (congrArg (· ≫ eqToHom (triangleObject K 𝒞 hk hR hA pt (n + 1)).2)
      (IsHomLift.fac' 𝒬 (triangleSiteTransition K 𝒞 hk hR n)
        (triangleObjectMap K 𝒞 hk hR hA pt n))).trans ?_
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rfl)

instance : IsIso (triangleSystemProjectionHom K 𝒞 hk hR hA pt) :=
  haveI : ∀ n, IsIso ((triangleSystemProjectionHom K 𝒞 hk hR hA pt).app n) := fun n => by
    rw [triangleSystemProjectionHom, NatTrans.ofSequence_app]
    exact (eqToIso (triangleObject K 𝒞 hk hR hA pt n).2).isIso_hom
  NatIso.isIso_of_isIso_app _

variable (𝒞 hk) in
/-- **The system of objects lies over the system of thickenings.** -/
def triangleSystemProjectionIso :
    triangleSystem K 𝒞 hk hR hA pt ⋙ 𝒬 ≅ triangleSiteSystem K 𝒞 hk hR :=
  asIso (triangleSystemProjectionHom K 𝒞 hk hR hA pt)

end Transition

end Deformation.Artin

end
