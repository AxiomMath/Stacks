module

public import StacksFrontier.Deformation.Artin.FormalObject.TriangleObjectNonTorsion
public import StacksFrontier.Deformation.Artin.FormalObject.TriangleQuotientStackObject

/-!
# The Čech class of the glued object `ξ_0` has infinite order

Let `A` be a nonzero abelian variety over an infinite field `k`, let `K = k(A)` be its function
field and let `ξ_n` be the object of `[Spec(k)/A]` over the thickened triangle `X_n` glued along
the generic point of `A` (`Deformation.Artin.triangleObject`). Its descent datum relative to the
covering `{U, W}` of `X_n` is represented by the Čech cocycle
`Deformation.Artin.triangleSiteCocycle` with values in the points of `A`. This file proves that
the Čech class of that cocycle at `n = 0` has infinite order: no nonzero power of it is a
coboundary (`Deformation.Artin.not_isTorsionClass_triangleSiteCocycle_genericPointOverField`).
This is the statement of the source about the glued torsor, read in Čech cohomology, and it
comes from the scheme-level computation
`Deformation.Artin.triangleCocycle_genericPointOverField_pow_ne`, evaluated on `U ∩ W`.

The comparison with the fppf cohomology class of the source is the interface
`Deformation.Artin.IsCechCompatible`: a class map on the objects of `[Spec(k)/A]` is
*Čech-compatible* when an object presented by a descent datum with a cocycle `c` on a covering
has a class of finite order only if the Čech class of `c` is torsion. That holds for the class
map of an object of a classifying stack whose value on presented objects is the image of the
Čech class under an injective group homomorphism, such as the map of Stacks 03AJ on torsors
trivial on a covering (`Stacks.Cohomology.Torsors.cechClass_injective`). For every
Čech-compatible class map the class of `ξ_0` has infinite order
(`Deformation.Artin.not_isOfFinAddOrder_triangleObject`).

## Main definitions

* `Deformation.Artin.triangleOverlapSite`: the overlap `U ∩ W` of `X_n` as an object of the
  site, with its morphisms to `U` and to `W`.
* `Deformation.Artin.IsCechCompatible`: the compatibility of a class map with Čech classes.

## Main results

* `Deformation.Artin.not_isTorsionClass_triangleSiteCocycle_genericPointOverField`: the Čech
  class of the cocycle of `ξ_0` has infinite order.
* `Deformation.Artin.not_isOfFinAddOrder_triangleObject`: the class of `ξ_0` under any
  Čech-compatible class map has infinite order.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Space
open scoped CategoryTheory.MonObj

universe u

namespace Deformation.Artin

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
  {𝒞 : BigFppfSite.{u}} {hk : 𝒞.Contains (Spec (.of k))}
  (hR : ∀ n : ℕ, 𝒞.Contains (Spec (.of (triangleLevel K n))))

/-! ### The overlap `U ∩ W` as an object of the site -/

section Overlap

variable (hk) in
/-- The overlap `U ∩ W = Spec R_n[1/((1 - x)(1 - y))]` of `X_n` as an object of the big fppf
site of `Spec k`. -/
def triangleOverlapSite (n : ℕ) : BigFppfOver 𝒞 (Spec (.of k)) hk :=
  BigFppfOver.mk 𝒞 _ hk (Scheme.size_lt_of_isOpenImmersion (triangleOverlapι K n) (hR n))
    (specOverField k K (triangleOverlap K n)).hom

/-- `U ∩ W` lies in `U` and in `W`. -/
lemma range_triangleOverlapι_subset (n : ℕ) (i : Bool) :
    Set.range (triangleOverlapι K n) ⊆ Set.range (triangleOpen K n i).ι := by
  have hj : Set.range (triangleOverlapι K n) =
      (PrimeSpectrum.basicOpen ((1 - triangleX K n) * (1 - triangleY K n)) :
        Set (PrimeSpectrum (triangleLevel K n))) :=
    PrimeSpectrum.localization_away_comap_range _ _
  rw [hj, Scheme.Opens.range_ι]
  cases i
  · exact PrimeSpectrum.basicOpen_mul_le_left _ _
  · exact PrimeSpectrum.basicOpen_mul_le_right _ _

/-- The inclusions `U ∩ W ⟶ U` (at `false`) and `U ∩ W ⟶ W` (at `true`) of schemes. -/
def triangleOverlapToOpen (n : ℕ) (i : Bool) :
    Spec (.of (triangleOverlap K n)) ⟶ (triangleOpen K n i).toScheme :=
  IsOpenImmersion.lift (triangleOpen K n i).ι (triangleOverlapι K n)
    (range_triangleOverlapι_subset K n i)

@[reassoc (attr := simp)]
lemma triangleOverlapToOpen_ι (n : ℕ) (i : Bool) :
    triangleOverlapToOpen K n i ≫ (triangleOpen K n i).ι = triangleOverlapι K n :=
  IsOpenImmersion.lift_fac _ _ _

variable (hk) in
/-- The inclusions `U ∩ W ⟶ U` and `U ∩ W ⟶ W` in the big fppf site. -/
def triangleOverlapSiteToOpen (n : ℕ) (i : Bool) :
    triangleOverlapSite K hk hR n ⟶ triangleOpenSite K 𝒞 hk hR n i :=
  BigFppfOver.homMk 𝒞 _ hk (BigFppfOver.contains_opens 𝒞 (hR n) (triangleOpen K n i))
    ((triangleOpen K n i).ι ≫ triangleStructure k K n) (triangleOverlapToOpen K n i) (by
      have e : triangleOverlapToOpen K n i ≫ (triangleOpen K n i).ι ≫ triangleStructure k K n =
          (specOverField k K (triangleOverlap K n)).hom := by
        rw [triangleOverlapToOpen_ι_assoc, triangleOverlapι_comp_triangleStructure]
      exact e)

lemma triangleOpenMap_triangleOverlapSiteToOpen (n : ℕ) (i : Bool) :
    triangleOpenMap K hR (triangleOverlapSiteToOpen K hk hR n i) = triangleOverlapι K n :=
  triangleOverlapToOpen_ι K n i

/-- The two inclusions of `U ∩ W` agree on `X_n`. -/
lemma triangleOverlapSiteToOpen_comp_ι (n : ℕ) :
    triangleOverlapSiteToOpen K hk hR n false ≫ triangleOpenSiteι K 𝒞 hk hR n false =
      triangleOverlapSiteToOpen K hk hR n true ≫ triangleOpenSiteι K 𝒞 hk hR n true :=
  (BigFppfOver.toScheme 𝒞 _ hk).map_injective (by
    rw [Functor.map_comp, Functor.map_comp]
    exact (triangleOpenMap_triangleOverlapSiteToOpen K hR n false).trans
      (triangleOpenMap_triangleOverlapSiteToOpen K hR n true).symm)

/-- The morphism `U ∩ W ⟶ U ∩ W` induced by the two inclusions is the identity. -/
lemma triangleOverlapLift_triangleOverlapSiteToOpen (n : ℕ) :
    triangleOverlapLift K hR (triangleOverlapSiteToOpen K hk hR n false)
      (triangleOverlapSiteToOpen K hk hR n true) (triangleOverlapSiteToOpen_comp_ι K hR n) =
        𝟙 _ :=
  (IsOpenImmersion.lift_uniq _ _ _ _
    ((Category.id_comp _).trans (triangleOpenMap_triangleOverlapSiteToOpen K hR n false).symm)).symm

/-- On `U`, the inclusion of `U ∩ W` is the localization `R_n[1/(1 - x)] ⟶ R_n[1/((1 - x)(1 - y))]`
followed by the identification of `Spec R_n[1/(1 - x)]` with the open `D(1 - x)`. -/
lemma triangleOverlapToOpen_false (n : ℕ) :
    triangleOverlapToOpen K n false =
      Spec.map (CommRingCat.ofHom (triangleLeftToOverlap K n).toRingHom) ≫
        (basicOpenIsoSpecAway (R := .of (triangleLevel K n)) (1 - triangleX K n)).inv := by
  refine (cancel_mono (triangleOpen K n false).ι).mp ?_
  have hι : (basicOpenIsoSpecAway (R := .of (triangleLevel K n)) (1 - triangleX K n)).inv ≫
      (triangleOpen K n false).ι =
      Spec.map (CommRingCat.ofHom (algebraMap (triangleLevel K n) (triangleLeft K n))) := by
    exact (Iso.inv_comp_eq _).mpr (basicOpenIsoSpecAway_hom_SpecMap _).symm
  rw [triangleOverlapToOpen_ι]
  calc triangleOverlapι K n
      = Spec.map (CommRingCat.ofHom (triangleLeftToOverlap K n).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (triangleLevel K n) (triangleLeft K n))) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
          show (triangleLeftToOverlap K n).toRingHom.comp (algebraMap _ _) = algebraMap _ _ from
            RingHom.ext (triangleLeftToOverlap_algebraMap K n)]
    _ = Spec.map (CommRingCat.ofHom (triangleLeftToOverlap K n).toRingHom) ≫
          (basicOpenIsoSpecAway (R := .of (triangleLevel K n)) (1 - triangleX K n)).inv ≫
            (triangleOpen K n false).ι := by rw [hι]
    _ = _ := (Category.assoc _ _ _).symm

/-- On `W`, the inclusion of `U ∩ W` is the localization `R_n[1/(1 - y)] ⟶ R_n[1/((1 - x)(1 - y))]`
followed by the identification of `Spec R_n[1/(1 - y)]` with the open `D(1 - y)`. -/
lemma triangleOverlapToOpen_true (n : ℕ) :
    triangleOverlapToOpen K n true =
      Spec.map (CommRingCat.ofHom (triangleRightToOverlap K n).toRingHom) ≫
        (basicOpenIsoSpecAway (R := .of (triangleLevel K n)) (1 - triangleY K n)).inv := by
  refine (cancel_mono (triangleOpen K n true).ι).mp ?_
  have hι : (basicOpenIsoSpecAway (R := .of (triangleLevel K n)) (1 - triangleY K n)).inv ≫
      (triangleOpen K n true).ι =
      Spec.map (CommRingCat.ofHom (algebraMap (triangleLevel K n) (triangleRight K n))) := by
    exact (Iso.inv_comp_eq _).mpr (basicOpenIsoSpecAway_hom_SpecMap _).symm
  rw [triangleOverlapToOpen_ι]
  calc triangleOverlapι K n
      = Spec.map (CommRingCat.ofHom (triangleRightToOverlap K n).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (triangleLevel K n) (triangleRight K n))) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
          show (triangleRightToOverlap K n).toRingHom.comp (algebraMap _ _) = algebraMap _ _ from
            RingHom.ext (triangleRightToOverlap_algebraMap K n)]
    _ = Spec.map (CommRingCat.ofHom (triangleRightToOverlap K n).toRingHom) ≫
          (basicOpenIsoSpecAway (R := .of (triangleLevel K n)) (1 - triangleY K n)).inv ≫
            (triangleOpen K n true).ι := by rw [hι]
    _ = _ := (Category.assoc _ _ _).symm

/-- The structure morphism to `Spec k` of a localization of `R_n`. -/
lemma Spec_algebraMap_comp_triangleStructure (n : ℕ) (S : Type u) [CommRing S]
    [Algebra (triangleLevel K n) S] [Algebra K S] [IsScalarTower K (triangleLevel K n) S] :
    Spec.map (CommRingCat.ofHom (algebraMap (triangleLevel K n) S)) ≫ triangleStructure k K n =
      (specOverField k K S).hom := by
  change _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap K (triangleLevel K n))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K))) =
    Spec.map (CommRingCat.ofHom (algebraMap K S)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

variable (hk) in
/-- The open `D(1 - x)` identified with `Spec R_n[1/(1 - x)]`, over `Spec k`. -/
def triangleLeftOver (n : ℕ) :
    specOverField k K (triangleLeft K n) ⟶
      (toSchemeOver 𝒞 _ hk).obj (triangleOpenSite K 𝒞 hk hR n false) :=
  Over.homMk (basicOpenIsoSpecAway (R := .of (triangleLevel K n)) (1 - triangleX K n)).inv (by
    have hι : (basicOpenIsoSpecAway (R := .of (triangleLevel K n)) (1 - triangleX K n)).inv ≫
        (triangleOpen K n false).ι =
        Spec.map (CommRingCat.ofHom (algebraMap (triangleLevel K n) (triangleLeft K n))) :=
      (Iso.inv_comp_eq _).mpr (basicOpenIsoSpecAway_hom_SpecMap _).symm
    have e : (basicOpenIsoSpecAway (R := .of (triangleLevel K n)) (1 - triangleX K n)).inv ≫
        (triangleOpen K n false).ι ≫ triangleStructure k K n =
        (specOverField k K (triangleLeft K n)).hom := by
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ triangleStructure k K n) hι).trans
        (Spec_algebraMap_comp_triangleStructure K n _))
    exact e)

variable (hk) in
/-- The open `D(1 - y)` identified with `Spec R_n[1/(1 - y)]`, over `Spec k`. -/
def triangleRightOver (n : ℕ) :
    specOverField k K (triangleRight K n) ⟶
      (toSchemeOver 𝒞 _ hk).obj (triangleOpenSite K 𝒞 hk hR n true) :=
  Over.homMk (basicOpenIsoSpecAway (R := .of (triangleLevel K n)) (1 - triangleY K n)).inv (by
    have hι : (basicOpenIsoSpecAway (R := .of (triangleLevel K n)) (1 - triangleY K n)).inv ≫
        (triangleOpen K n true).ι =
        Spec.map (CommRingCat.ofHom (algebraMap (triangleLevel K n) (triangleRight K n))) :=
      (Iso.inv_comp_eq _).mpr (basicOpenIsoSpecAway_hom_SpecMap _).symm
    have e : (basicOpenIsoSpecAway (R := .of (triangleLevel K n)) (1 - triangleY K n)).inv ≫
        (triangleOpen K n true).ι ≫ triangleStructure k K n =
        (specOverField k K (triangleRight K n)).hom := by
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ triangleStructure k K n) hι).trans
        (Spec_algebraMap_comp_triangleStructure K n _))
    exact e)

/-- On `U`, the inclusion of `U ∩ W`, over `Spec k`. -/
lemma toSchemeOver_map_triangleOverlapSiteToOpen_false (n : ℕ) :
    (toSchemeOver 𝒞 _ hk).map (triangleOverlapSiteToOpen K hk hR n false) =
      specOverFieldMap (triangleLeftToOverlap K n) ≫ triangleLeftOver K hk hR n :=
  Over.OverMorphism.ext (triangleOverlapToOpen_false K n)

/-- On `W`, the inclusion of `U ∩ W`, over `Spec k`. -/
lemma toSchemeOver_map_triangleOverlapSiteToOpen_true (n : ℕ) :
    (toSchemeOver 𝒞 _ hk).map (triangleOverlapSiteToOpen K hk hR n true) =
      specOverFieldMap (triangleRightToOverlap K n) ≫ triangleRightOver K hk hR n :=
  Over.OverMorphism.ext (triangleOverlapToOpen_true K n)

end Overlap

/-! ### The Čech class of `ξ_0` -/

section NonTorsion

variable {A : Over (Spec (.of k))} [GrpObj A] [IsAbelianVariety k A] (hA : 𝒞.Contains A.left)
  (hRA : ∀ n : ℕ, 𝒞.Contains (Spec (.of (triangleLevel A.left.functionField n))))

/-- **The Čech class of `ξ_0` has infinite order.** Let `A` be a nonzero abelian variety over an
infinite field `k` and `K = k(A)`. The Čech cocycle of the covering `{U, W}` of the reduced
triangle `X_0` over `K` with values in the points of `A`, given by the glueing cocycle along
the generic point of `A`, which represents the descent datum of `ξ_0`, has no nonzero power
which is a coboundary. -/
theorem not_isTorsionClass_triangleSiteCocycle_genericPointOverField [Infinite k]
    (hdim : 1 ≤ Stacks.Groupoids.abelianVarietyDimension A) :
    letI := functionFieldAlgebra A
    ¬ (triangleSiteCocycle (hk := hk) A.left.functionField hRA hA
      (genericPointOverField A) 0).IsTorsionClass := by
  let _ := functionFieldAlgebra A
  rintro ⟨m, hm, s, hs⟩
  have hab := triangleOverlapSiteToOpen_comp_ι (hk := hk) A.left.functionField hRA 0
  have h := hs _ _ hab
  rw [triangleSiteCocycle_val_false_true,
    triangleGamma_of_eq A.left.functionField hRA hA (genericPointOverField A) 0 _ _ hab] at h
  have hsU := (pointOfScheme A hA).apply_symm_apply (s false)
  have hsW := (pointOfScheme A hA).apply_symm_apply (s true)
  rw [← hsU, ← hsW, ← pointOfScheme_naturality, ← pointOfScheme_naturality,
    toSchemeOver_map_triangleOverlapSiteToOpen_false,
    toSchemeOver_map_triangleOverlapSiteToOpen_true, ← map_pow, ← _root_.map_inv, ← map_mul]
    at h
  have h' := (pointOfScheme A hA).injective h
  have hlift : triangleOverlapLiftOver A.left.functionField hRA
      (triangleOverlapSiteToOpen A.left.functionField hk hRA 0 false)
      (triangleOverlapSiteToOpen A.left.functionField hk hRA 0 true) hab = 𝟙 _ :=
    Over.OverMorphism.ext (triangleOverlapLift_triangleOverlapSiteToOpen A.left.functionField hRA 0)
  have hcomp : triangleOverlapLiftOver A.left.functionField hRA
      (triangleOverlapSiteToOpen A.left.functionField hk hRA 0 false)
      (triangleOverlapSiteToOpen A.left.functionField hk hRA 0 true) hab ≫
        triangleCocycle A.left.functionField 0 A (genericPointOverField A) =
      triangleCocycle A.left.functionField 0 A (genericPointOverField A) := by
    rw [hlift]
    exact Category.id_comp _
  have h'' : triangleCocycle A.left.functionField 0 A (genericPointOverField A) ^ m =
      (specOverFieldMap (triangleLeftToOverlap A.left.functionField 0) ≫
        (triangleLeftOver A.left.functionField hk hRA 0 ≫
          (pointOfScheme A hA).symm (s false)))⁻¹ *
      (specOverFieldMap (triangleRightToOverlap A.left.functionField 0) ≫
        (triangleRightOver A.left.functionField hk hRA 0 ≫
          (pointOfScheme A hA).symm (s true))) := by
    rw [← Category.assoc, ← Category.assoc]
    exact (congrArg (· ^ m) hcomp.symm).trans h'
  exact triangleCocycle_genericPointOverField_pow_ne A hdim hm _ _ h''

/-- A class map on the objects of the classifying stack `[Spec(k)/G]` is *Čech-compatible* when
an object `x` presented, relative to an fppf covering `𝒰` of its base, by a descent datum for
the presentation represented by a Čech cocycle `c` has a class of finite order only if the Čech
class of `c` is torsion. This is what holds when the class of such an `x` is the image of the
Čech class of `c` under an injective homomorphism of groups, as for the classes of torsors
trivial on a covering (`Stacks.Cohomology.Torsors.cechClass_injective`). -/
def IsCechCompatible
    (G : GroupAlgebraicSpace 𝒞 (Spec (.of k)) hk (baseS 𝒞 _ hk) (isAlgebraicSpace_baseS 𝒞 _ hk))
    {M : BigFppfOver 𝒞 (Spec (.of k)) hk → Type*} [∀ T, AddMonoid (M T)]
    (cls : ∀ x : (Stack.quotientStack (baseTrivialActionGroupoid G)).obj,
      M ((Stack.quotientStack (baseTrivialActionGroupoid G)).p.obj x)) : Prop :=
  ∀ ⦃T : BigFppfOver 𝒞 (Spec (.of k)) hk⦄ (𝒰 : PreZeroHypercover.{0} T)
    (_ : 𝒰.sieve₀ ∈ BigFppfOver.topology 𝒞 _ hk T)
    (x : (Stack.quotientStack (baseTrivialActionGroupoid G)).p.Fiber T)
    (D : Functor.FamilyDescentDatum (Stack.quotientPrestack (baseTrivialActionGroupoid G)).p 𝒰)
    (c : Functor.FamilyCocycle (GroupAlgebraicSpace.pointsGrpPresheaf G) 𝒰.f),
    (trivialActionRigidification G).IsRepresentedBy D c →
    Nonempty ((Functor.toFamilyDescentDatum (Stack.quotientStack (baseTrivialActionGroupoid G)).p
      𝒰).obj x ≅ (Stack.presentingDescentFunctor (baseTrivialActionGroupoid G) 𝒰).obj D) →
    IsOfFinAddOrder (cls x.1) → c.IsTorsionClass

/-- **The class of `ξ_0` has infinite order** under every Čech-compatible class map on
`[Spec(k)/A]`, for a nonzero abelian variety `A` over an infinite field `k`. -/
theorem not_isOfFinAddOrder_triangleObject [Infinite k]
    (hdim : 1 ≤ Stacks.Groupoids.abelianVarietyDimension A)
    {M : BigFppfOver 𝒞 (Spec (.of k)) hk → Type*} [∀ T, AddMonoid (M T)]
    (cls : ∀ x : (Stack.quotientStack (baseTrivialActionGroupoid (siteGroupSpace A hA))).obj,
      M ((Stack.quotientStack (baseTrivialActionGroupoid (siteGroupSpace A hA))).p.obj x))
    (hcls : IsCechCompatible (siteGroupSpace A hA) cls) :
    letI := functionFieldAlgebra A
    ¬ IsOfFinAddOrder (cls (triangleObject A.left.functionField 𝒞 hk hRA hA
      (genericPointOverField A) 0).1) := by
  let _ := functionFieldAlgebra A
  intro h
  exact not_isTorsionClass_triangleSiteCocycle_genericPointOverField hA hRA hdim
    (hcls _ (triangleCover_mem A.left.functionField 𝒞 hk hRA 0) _ _ _
      (isRepresentedBy_triangleDescentDatum A.left.functionField 𝒞 hk hRA hA
        (genericPointOverField A) 0)
      ⟨triangleObjectIso A.left.functionField 𝒞 hk hRA hA (genericPointOverField A) 0⟩ h)

end NonTorsion

end Deformation.Artin

end
