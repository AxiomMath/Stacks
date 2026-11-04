module

public import StacksFrontier.AlgebraicGeometry.TwistExistence.Glue

/-!
# Twist data over a basis of affine opens, and the comparison of two of them

Twist data on a relative Proj `Proj_S(A)` over a **basis** `𝔅` of the topology of `S` consisting
of affine opens: an integer-graded sheaf of algebras with chart identifications with the absolute
twists over the members of `𝔅`, multiplicative, and carrying a homogeneous-section map to the
absolute homogeneous sections of Tag 01MP. Two such data have isomorphic graded algebras.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistExistenceBasis.BasisTwistData`: chart identifications over the
  members of `𝔅`, multiplicative, with a homogeneous-section map compatible with them.
* `Stacks.AlgebraicGeometry.TwistExistenceBasis.BasisTwistData.ofTwistData`: a twist datum of
  Tag 01NR, restricted to `𝔅`.
* `Stacks.AlgebraicGeometry.TwistExistenceBasis.glueAlgIso`: **the isomorphism of the graded
  algebras of two such data.**

## Main results

* `Stacks.AlgebraicGeometry.TwistExistenceBasis.glueIso_hom_app_of_le`: over the inverse image of
  a member of `𝔅` the isomorphism is the chart comparison.
* `Stacks.AlgebraicGeometry.TwistExistenceBasis.glueIso_psi`: it carries the first
  homogeneous-section map to the second, over every open of the base.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.TwistExistence

namespace Stacks.AlgebraicGeometry.TwistExistenceBasis

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (𝔅 : Set S.Opens)

/-- **Twist data over a family `𝔅` of affine opens of the base.** An integer-graded sheaf of
algebras on `Proj_S(A)`, identified over the chart of every member of `𝔅` with the absolute twists,
compatibly with the products, and a homogeneous-section map which the identifications carry to the
absolute homogeneous sections. -/
public structure BasisTwistData where
  /-- The integer-graded sheaf of algebras on the relative Proj. -/
  algebra : SchemeGradedAlgebra (relativeProj A).scheme
  /-- The chart identification over a member of `𝔅`, in each degree. -/
  chartIso (U : S.Opens) (hU : IsAffineOpen U) (hB : U ∈ 𝔅) (n : ℤ) :
    Scheme.Modules.restrict (algebra.piece n) ((relativeProj A).chart U hU) ≅
      twistingSheaf (A.grading U) n
  /-- The chart identifications carry the canonical product of absolute twists to the product. -/
  chartIso_mul (U : S.Opens) (hU : IsAffineOpen U) (hB : U ∈ 𝔅) (i j : ℤ)
    (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (a : (twistingSheaf (A.grading U) i).val.obj (op V))
    (b : (twistingSheaf (A.grading U) j).val.obj (op V)) :
    (Scheme.Modules.restrictAppIso ((relativeProj A).chart U hU) (algebra.piece (i + j)) V).hom
        ((chartIso U hU hB (i + j)).inv.val.app (op V)
          (absoluteTwistProduct (A.grading U) i j V a b)) =
      (algebra.mul i j).app (op (((relativeProj A).chart U hU) ''ᵁ V))
        ((Scheme.Modules.restrictAppIso ((relativeProj A).chart U hU) (algebra.piece i) V).hom
          ((chartIso U hU hB i).inv.val.app (op V) a))
        ((Scheme.Modules.restrictAppIso ((relativeProj A).chart U hU) (algebra.piece j) V).hom
          ((chartIso U hU hB j).inv.val.app (op V) b))
  /-- The homogeneous-section map. -/
  ψ (n : ℕ) : A.piece (n : ℤ) ⟶
    (Scheme.Modules.pushforward (relativeProj A).toBase).obj (algebra.piece (n : ℤ))
  /-- Under a chart identification the homogeneous-section map is the absolute one. -/
  ψ_chart (U : S.Opens) (hU : IsAffineOpen U) (hB : U ∈ 𝔅) (k : ℕ) (a : A.sectionPieces U k) :
    (Scheme.Modules.restrictAppIso ((relativeProj A).chart U hU) (algebra.piece (k : ℤ)) ⊤).hom
        ((chartIso U hU hB (k : ℤ)).inv.val.app (op ⊤)
          (degreeSection (A.grading U) k
            ⟨DirectSum.of (A.sectionPieces U) k a, A.of_mem_grading U a⟩)) =
      (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU).symm ▸
        ((ψ k).val.app (op U) a)

variable {A 𝔅}

/-- Restriction of the absolute twists from `⊤` to the preimage of the inverse image of `U`
under the chart is injective. -/
private theorem twistingSheaf_map_preimage_injective (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ) :
    Function.Injective ((twistingSheaf (A.grading U) n).val.map
      (homOfLE (le_top :
        (relativeProj A).chart U hU ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U) ≤ ⊤)).op) := by
  have hV₀ : (relativeProj A).chart U hU ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U) = ⊤ := by
    rw [← RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU]
    exact Scheme.Hom.preimage_image_eq _ _
  exact fun x y hxy =>
    (PresheafOfModules.map_map_eq_self (twistingSheaf (A.grading U) n).val
      (homOfLE le_top).op (homOfLE hV₀.ge).op x).symm.trans
      ((congrArg _ hxy).trans (PresheafOfModules.map_map_eq_self
        (twistingSheaf (A.grading U) n).val (homOfLE le_top).op (homOfLE hV₀.ge).op y))

namespace BasisTwistData

variable (E : BasisTwistData A 𝔅)

/-- The section comparison induced by a chart identification, with sections of the restriction
identified with sections on the image open. -/
public def mapSection (U : S.Opens) (hU : IsAffineOpen U) (hB : U ∈ 𝔅) (n : ℤ)
    (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (a : (twistingSheaf (A.grading U) n).val.obj (op V)) :
    (E.algebra.piece n).val.obj (op (((relativeProj A).chart U hU) ''ᵁ V)) :=
  (Scheme.Modules.restrictAppIso ((relativeProj A).chart U hU) (E.algebra.piece n) V).hom
    ((E.chartIso U hU hB n).inv.val.app (op V) a)

/-- The section comparison induced by a chart identification is injective. -/
public theorem mapSection_injective (U : S.Opens) (hU : IsAffineOpen U) (hB : U ∈ 𝔅) (n : ℤ)
    (V : (AlgebraicGeometry.Proj (A.grading U)).Opens) :
    Function.Injective (E.mapSection U hU hB n V) := by
  have key : ∀ a, (E.chartIso U hU hB n).hom.val.app (op V)
      ((Scheme.Modules.restrictAppIso ((relativeProj A).chart U hU)
        (E.algebra.piece n) V).inv (E.mapSection U hU hB n V a)) = a :=
    fun a => TwistRigidity.iso_hom_app_inv_app (E.chartIso U hU hB n) (op V) a
  intro a b hab
  refine (key a).symm.trans (Eq.trans ?_ (key b))
  exact congrArg (fun z => (E.chartIso U hU hB n).hom.val.app (op V)
    ((Scheme.Modules.restrictAppIso ((relativeProj A).chart U hU)
      (E.algebra.piece n) V).inv z)) hab

/-- **The chart identification carries the product to the canonical product of absolute
twists**, in the forward direction. -/
public theorem chartIso_hom_mul (U : S.Opens) (hU : IsAffineOpen U) (hB : U ∈ 𝔅) (i j : ℤ)
    (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (x : (E.algebra.piece i).val.obj (op ((relativeProj A).chart U hU ''ᵁ V)))
    (y : (E.algebra.piece j).val.obj (op ((relativeProj A).chart U hU ''ᵁ V))) :
    (E.chartIso U hU hB (i + j)).hom.val.app (op V)
        ((E.algebra.mul i j).app (op ((relativeProj A).chart U hU ''ᵁ V)) x y) =
      absoluteTwistProduct (A.grading U) i j V
        ((E.chartIso U hU hB i).hom.val.app (op V) x)
        ((E.chartIso U hU hB j).hom.val.app (op V) y) := by
  have h := E.chartIso_mul U hU hB i j V ((E.chartIso U hU hB i).hom.val.app (op V) x)
    ((E.chartIso U hU hB j).hom.val.app (op V) y)
  have hx := TwistRigidity.iso_inv_app_hom_app (E.chartIso U hU hB i) (op V) x
  have hy := TwistRigidity.iso_inv_app_hom_app (E.chartIso U hU hB j) (op V) y
  have h' : (E.chartIso U hU hB (i + j)).inv.val.app (op V)
      (absoluteTwistProduct (A.grading U) i j V
        ((E.chartIso U hU hB i).hom.val.app (op V) x)
        ((E.chartIso U hU hB j).hom.val.app (op V) y)) =
      (E.algebra.mul i j).app (op ((relativeProj A).chart U hU ''ᵁ V)) x y :=
    h.trans (TwistRigidity.mul_app_congr E.algebra i j _ hx hy)
  rw [← h']
  exact TwistRigidity.iso_hom_app_inv_app (E.chartIso U hU hB (i + j)) (op V) _

/-- The homogeneous-section compatibility of a chart identification, from its forward form. -/
public theorem psi_chart_of_hom (algebra : SchemeGradedAlgebra (relativeProj A).scheme)
    (chartIso : ∀ (U : S.Opens) (hU : IsAffineOpen U) (_ : U ∈ 𝔅) (n : ℤ),
      Scheme.Modules.restrict (algebra.piece n) ((relativeProj A).chart U hU) ≅
        twistingSheaf (A.grading U) n)
    (ψ : ∀ n : ℕ, A.piece (n : ℤ) ⟶
      (Scheme.Modules.pushforward (relativeProj A).toBase).obj (algebra.piece (n : ℤ)))
    (U : S.Opens) (hU : IsAffineOpen U) (hB : U ∈ 𝔅) (k : ℕ) (a : A.sectionPieces U k)
    (h : (chartIso U hU hB (k : ℤ)).hom.val.app
          (op ((relativeProj A).chart U hU ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U)))
          ((algebra.piece (k : ℤ)).val.map
            (homOfLE (((relativeProj A).chart U hU).image_preimage_le
              ((relativeProj A).toBase ⁻¹ᵁ U))).op ((ψ k).val.app (op U) a)) =
        (twistingSheaf (A.grading U) (k : ℤ)).val.map
          (homOfLE (le_top :
            (relativeProj A).chart U hU ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U) ≤ ⊤)).op
          (degreeSection (A.grading U) k
            ⟨DirectSum.of (A.sectionPieces U) k a, A.of_mem_grading U a⟩)) :
    (Scheme.Modules.restrictAppIso ((relativeProj A).chart U hU) (algebra.piece (k : ℤ)) ⊤).hom
        ((chartIso U hU hB (k : ℤ)).inv.val.app (op ⊤)
          (degreeSection (A.grading U) k
            ⟨DirectSum.of (A.sectionPieces U) k a, A.of_mem_grading U a⟩)) =
      (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU).symm ▸
        ((ψ k).val.app (op U) a) := by
  have hle : (relativeProj A).chart U hU ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U) ≤ ⊤ := le_top
  have hinj := twistingSheaf_map_preimage_injective (A := A) U hU (k : ℤ)
  have h4 := PresheafOfModules.rec_eq_map (algebra.piece (k : ℤ)).val
    (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU).symm ((ψ k).val.app (op U) a)
  refine Eq.trans ?_ h4.symm
  have hhom : (chartIso U hU hB (k : ℤ)).hom.val.app (op ⊤)
      ((algebra.piece (k : ℤ)).val.map
        (eqToHom (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU).symm.symm).op
        ((ψ k).val.app (op U) a)) =
      degreeSection (A.grading U) k
        ⟨DirectSum.of (A.sectionPieces U) k a, A.of_mem_grading U a⟩ := by
    refine hinj ?_
    refine Eq.trans (PresheafOfModules.naturality_apply
      (chartIso U hU hB (k : ℤ)).hom.val (homOfLE hle).op _).symm ?_
    refine Eq.trans ?_ h
    refine congrArg ((chartIso U hU hB (k : ℤ)).hom.val.app
      (op ((relativeProj A).chart U hU ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U)))) ?_
    exact PresheafOfModules.map_map_eq_map (algebra.piece (k : ℤ)).val _ _ _ _
  refine Eq.trans (congrArg ((chartIso U hU hB (k : ℤ)).inv.val.app (op ⊤)) hhom.symm) ?_
  exact TwistRigidity.iso_inv_app_hom_app (chartIso U hU hB (k : ℤ)) (op ⊤) _

/-- **Twist data over a basis, from its forward chart identifications**: the multiplicativity
and the homogeneous-section compatibility stated for the forward direction of the chart
identifications, on the sections over every open of a chart and over the inverse image of the
member, respectively. -/
public def ofHom (algebra : SchemeGradedAlgebra (relativeProj A).scheme)
    (chartIso : ∀ (U : S.Opens) (hU : IsAffineOpen U) (_ : U ∈ 𝔅) (n : ℤ),
      Scheme.Modules.restrict (algebra.piece n) ((relativeProj A).chart U hU) ≅
        twistingSheaf (A.grading U) n)
    (chartIso_hom_mul : ∀ (U : S.Opens) (hU : IsAffineOpen U) (hB : U ∈ 𝔅) (i j : ℤ)
      (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
      (x : (algebra.piece i).val.obj (op ((relativeProj A).chart U hU ''ᵁ V)))
      (y : (algebra.piece j).val.obj (op ((relativeProj A).chart U hU ''ᵁ V))),
      (chartIso U hU hB (i + j)).hom.val.app (op V)
          ((algebra.mul i j).app (op ((relativeProj A).chart U hU ''ᵁ V)) x y) =
        absoluteTwistProduct (A.grading U) i j V
          ((chartIso U hU hB i).hom.val.app (op V) x)
          ((chartIso U hU hB j).hom.val.app (op V) y))
    (ψ : ∀ n : ℕ, A.piece (n : ℤ) ⟶
      (Scheme.Modules.pushforward (relativeProj A).toBase).obj (algebra.piece (n : ℤ)))
    (ψ_chart_hom : ∀ (U : S.Opens) (hU : IsAffineOpen U) (hB : U ∈ 𝔅) (k : ℕ)
      (a : A.sectionPieces U k),
      (chartIso U hU hB (k : ℤ)).hom.val.app
          (op ((relativeProj A).chart U hU ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U)))
          ((algebra.piece (k : ℤ)).val.map
            (homOfLE (((relativeProj A).chart U hU).image_preimage_le
              ((relativeProj A).toBase ⁻¹ᵁ U))).op ((ψ k).val.app (op U) a)) =
        (twistingSheaf (A.grading U) (k : ℤ)).val.map
          (homOfLE (le_top :
            (relativeProj A).chart U hU ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U) ≤ ⊤)).op
          (degreeSection (A.grading U) k
            ⟨DirectSum.of (A.sectionPieces U) k a, A.of_mem_grading U a⟩)) :
    BasisTwistData A 𝔅 where
  algebra := algebra
  chartIso := chartIso
  chartIso_mul U hU hB i j V a b := by
    have h := chartIso_hom_mul U hU hB i j V ((chartIso U hU hB i).inv.val.app (op V) a)
      ((chartIso U hU hB j).inv.val.app (op V) b)
    have h' : absoluteTwistProduct (A.grading U) i j V a b =
        (chartIso U hU hB (i + j)).hom.val.app (op V)
          ((algebra.mul i j).app (op ((relativeProj A).chart U hU ''ᵁ V))
            ((chartIso U hU hB i).inv.val.app (op V) a)
            ((chartIso U hU hB j).inv.val.app (op V) b)) :=
      (congrArg₂ (absoluteTwistProduct (A.grading U) i j V)
        (TwistRigidity.iso_hom_app_inv_app (chartIso U hU hB i) (op V) a).symm
        (TwistRigidity.iso_hom_app_inv_app (chartIso U hU hB j) (op V) b).symm).trans h.symm
    exact (congrArg ((chartIso U hU hB (i + j)).inv.val.app (op V)) h').trans
      (TwistRigidity.iso_inv_app_hom_app (chartIso U hU hB (i + j)) (op V) _)
  ψ := ψ
  ψ_chart U hU hB k a := psi_chart_of_hom algebra chartIso ψ U hU hB k a (ψ_chart_hom U hU hB k a)

/-- **Twist data over a basis, from forward chart identifications indexed by the members of the
basis**, the affineness of each member being a function of its membership. -/
public def ofHom' (h𝔅a : ∀ U ∈ 𝔅, IsAffineOpen U)
    (algebra : SchemeGradedAlgebra (relativeProj A).scheme)
    (chartIso : ∀ (V : 𝔅) (n : ℤ),
      Scheme.Modules.restrict (algebra.piece n) ((relativeProj A).chart V.1 (h𝔅a V.1 V.2)) ≅
        twistingSheaf (A.grading V.1) n)
    (chartIso_hom_mul : ∀ (V : 𝔅) (i j : ℤ)
      (W : (AlgebraicGeometry.Proj (A.grading V.1)).Opens)
      (x : (algebra.piece i).val.obj (op ((relativeProj A).chart V.1 (h𝔅a V.1 V.2) ''ᵁ W)))
      (y : (algebra.piece j).val.obj (op ((relativeProj A).chart V.1 (h𝔅a V.1 V.2) ''ᵁ W))),
      (chartIso V (i + j)).hom.val.app (op W)
          ((algebra.mul i j).app (op ((relativeProj A).chart V.1 (h𝔅a V.1 V.2) ''ᵁ W)) x y) =
        absoluteTwistProduct (A.grading V.1) i j W
          ((chartIso V i).hom.val.app (op W) x) ((chartIso V j).hom.val.app (op W) y))
    (ψ : ∀ n : ℕ, A.piece (n : ℤ) ⟶
      (Scheme.Modules.pushforward (relativeProj A).toBase).obj (algebra.piece (n : ℤ)))
    (ψ_chart_hom : ∀ (V : 𝔅) (k : ℕ) (a : A.sectionPieces V.1 k),
      (chartIso V (k : ℤ)).hom.val.app
          (op ((relativeProj A).chart V.1 (h𝔅a V.1 V.2) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V.1)))
          ((algebra.piece (k : ℤ)).val.map
            (homOfLE (((relativeProj A).chart V.1 (h𝔅a V.1 V.2)).image_preimage_le
              ((relativeProj A).toBase ⁻¹ᵁ V.1))).op ((ψ k).val.app (op V.1) a)) =
        (twistingSheaf (A.grading V.1) (k : ℤ)).val.map
          (homOfLE (le_top : (relativeProj A).chart V.1 (h𝔅a V.1 V.2) ⁻¹ᵁ
            ((relativeProj A).toBase ⁻¹ᵁ V.1) ≤ ⊤)).op
          (degreeSection (A.grading V.1) k
            ⟨DirectSum.of (A.sectionPieces V.1) k a, A.of_mem_grading V.1 a⟩)) :
    BasisTwistData A 𝔅 :=
  ofHom algebra (fun U _ hB n => chartIso ⟨U, hB⟩ n)
    (by
      intro U hU hB
      have key : ∀ (X : S.Opens) (_ : (⟨U, hB⟩ : 𝔅).1 = X) (hX : X ∈ 𝔅) (hXa : IsAffineOpen X)
          (i j : ℤ) (W : (AlgebraicGeometry.Proj (A.grading X)).Opens)
          (x : (algebra.piece i).val.obj (op ((relativeProj A).chart X hXa ''ᵁ W)))
          (y : (algebra.piece j).val.obj (op ((relativeProj A).chart X hXa ''ᵁ W))),
          (chartIso ⟨X, hX⟩ (i + j)).hom.val.app (op W)
              ((algebra.mul i j).app (op ((relativeProj A).chart X hXa ''ᵁ W)) x y) =
            absoluteTwistProduct (A.grading X) i j W
              ((chartIso ⟨X, hX⟩ i).hom.val.app (op W) x)
              ((chartIso ⟨X, hX⟩ j).hom.val.app (op W) y) := by
        rintro X rfl hX hXa i j W x y
        exact chartIso_hom_mul ⟨U, hB⟩ i j W x y
      exact key U rfl hB hU) ψ
    (by
      intro U hU hB
      have key : ∀ (X : S.Opens) (_ : (⟨U, hB⟩ : 𝔅).1 = X) (hX : X ∈ 𝔅) (hXa : IsAffineOpen X)
          (k : ℕ) (a : A.sectionPieces X k),
          (chartIso ⟨X, hX⟩ (k : ℤ)).hom.val.app
              (op ((relativeProj A).chart X hXa ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ X)))
              ((algebra.piece (k : ℤ)).val.map
                (homOfLE (((relativeProj A).chart X hXa).image_preimage_le
                  ((relativeProj A).toBase ⁻¹ᵁ X))).op ((ψ k).val.app (op X) a)) =
            (twistingSheaf (A.grading X) (k : ℤ)).val.map
              (homOfLE (le_top :
                (relativeProj A).chart X hXa ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ X) ≤ ⊤)).op
              (degreeSection (A.grading X) k
                ⟨DirectSum.of (A.sectionPieces X) k a, A.of_mem_grading X a⟩) := by
        rintro X rfl hX hXa k a
        exact ψ_chart_hom ⟨U, hB⟩ k a
      exact key U rfl hB hU)

/-- The algebra of `ofHom'` is the given algebra. -/
@[simp] public theorem ofHom'_algebra (h𝔅a : ∀ U ∈ 𝔅, IsAffineOpen U)
    (algebra : SchemeGradedAlgebra (relativeProj A).scheme) (chartIso) (chartIso_hom_mul) (ψ)
    (ψ_chart_hom) :
    (ofHom' h𝔅a algebra chartIso chartIso_hom_mul ψ ψ_chart_hom).algebra = algebra := rfl

/-- The homogeneous-section map of `ofHom'` is the given one. -/
@[simp] public theorem ofHom'_ψ (h𝔅a : ∀ U ∈ 𝔅, IsAffineOpen U)
    (algebra : SchemeGradedAlgebra (relativeProj A).scheme) (chartIso) (chartIso_hom_mul) (ψ)
    (ψ_chart_hom) :
    (ofHom' h𝔅a algebra chartIso chartIso_hom_mul ψ ψ_chart_hom).ψ = ψ := rfl

/-- **A twist datum of Tag 01NR, restricted to a family of affine opens.** -/
public def ofTwistData (D : TwistData A) : BasisTwistData A 𝔅 where
  algebra := D.algebra
  chartIso U hU _ n := D.chartData.chartIso U hU n
  chartIso_mul U hU _ i j V a b := D.chartIso_mul U hU i j V a b
  ψ := D.ψ
  ψ_chart U hU _ k a := D.ψ_chart U hU k a

/-- The algebra of `ofTwistData D` is that of `D`. -/
@[simp] public theorem ofTwistData_algebra (D : TwistData A) :
    (ofTwistData (𝔅 := 𝔅) D).algebra = D.algebra := rfl

/-- The homogeneous-section map of `ofTwistData D` is that of `D`. -/
@[simp] public theorem ofTwistData_ψ (D : TwistData A) (n : ℕ) :
    (ofTwistData (𝔅 := 𝔅) D).ψ n = D.ψ n := rfl

end BasisTwistData

/-! ### The chart identification as a local isomorphism -/

section Chart

variable (E : BasisTwistData A 𝔅) (U : S.Opens) (hU : IsAffineOpen U) (hB : U ∈ 𝔅)

/-- The homogeneous piece of the algebra, compared with the direct image of the absolute twist
along the chart over a member of `𝔅`. -/
public def chartPush (n : ℤ) :
    E.algebra.piece n ⟶
      (Scheme.Modules.pushforward ((relativeProj A).chart U hU)).obj
        (twistingSheaf (A.grading U) n) :=
  (Scheme.Modules.restrictAdjunction ((relativeProj A).chart U hU)).unit.app
      (E.algebra.piece n) ≫
    (Scheme.Modules.pushforward ((relativeProj A).chart U hU)).map (E.chartIso U hU hB n).hom

/-- `chartPush` on sections: restrict to the image of the inverse image under the chart, then
apply the chart identification. -/
public theorem chartPush_val_app (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (x : (E.algebra.piece n).val.obj (op V)) :
    (chartPush E U hU hB n).val.app (op V) x =
      (E.chartIso U hU hB n).hom.val.app
        (op ((relativeProj A).chart U hU ⁻¹ᵁ V))
        ((E.algebra.piece n).val.map
          (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op x) :=
  rfl

/-- `chartPush` is bijective on sections over every open inside the inverse image of the
member. -/
public theorem bijective_chartPush (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ U) :
    Function.Bijective ((chartPush E U hU hB n).val.app (op V)).hom := by
  have heq : ((relativeProj A).chart U hU) ''ᵁ (((relativeProj A).chart U hU) ⁻¹ᵁ V) = V :=
    TwistUnique.image_preimage_eq_self ((relativeProj A).chart U hU)
      (hV.trans (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU).ge)
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun a => (E.algebra.piece n).val.map (homOfLE heq.ge).op
      ((E.chartIso U hU hB n).inv.val.app
        (op ((relativeProj A).chart U hU ⁻¹ᵁ V)) a), fun x => ?_, fun a => ?_⟩
  · refine Eq.trans (congrArg (fun z => (E.algebra.piece n).val.map (homOfLE heq.ge).op
      ((E.chartIso U hU hB n).inv.val.app
        (op ((relativeProj A).chart U hU ⁻¹ᵁ V)) z)) (chartPush_val_app E U hU hB n V x)) ?_
    refine Eq.trans (congrArg ((E.algebra.piece n).val.map (homOfLE heq.ge).op)
      (TwistRigidity.iso_inv_app_hom_app (E.chartIso U hU hB n)
        (op ((relativeProj A).chart U hU ⁻¹ᵁ V)) _)) ?_
    exact PresheafOfModules.map_map_eq_self (E.algebra.piece n).val _ _ x
  · refine Eq.trans (chartPush_val_app E U hU hB n V _) ?_
    refine Eq.trans (congrArg ((E.chartIso U hU hB n).hom.val.app
      (op ((relativeProj A).chart U hU ⁻¹ᵁ V)))
      (PresheafOfModules.map_map_eq_self (E.algebra.piece n).val _ _ _)) ?_
    exact TwistRigidity.iso_hom_app_inv_app (E.chartIso U hU hB n)
      (op ((relativeProj A).chart U hU ⁻¹ᵁ V)) a

/-- **The chart identification over a member of `𝔅`, as a local isomorphism** over the inverse
image of that member. -/
public def chartLoc (n : ℤ) :
    TopCat.Sheaf.LocalModuleEquiv (E.algebra.piece n).val
      (ChartTransNonNested.pushforwardVal ((relativeProj A).chart U hU)
        (twistingSheaf (A.grading U) n))
      ((relativeProj A).toBase ⁻¹ᵁ U) :=
  ChartTransRelativeProj.localModuleEquivOfBijective (chartPush E U hU hB n).val
    ((relativeProj A).toBase ⁻¹ᵁ U) (bijective_chartPush E U hU hB n)

/-- `chartLoc` on sections: restrict to the image of the inverse image under the chart, then
apply the chart identification. -/
public theorem chartLoc_app_eq (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ U) (x : (E.algebra.piece n).val.obj (op V)) :
    (chartLoc E U hU hB n).app V hV x =
      (E.chartIso U hU hB n).hom.val.app
        (op ((relativeProj A).chart U hU ⁻¹ᵁ V))
        ((E.algebra.piece n).val.map
          (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op x) :=
  ChartTransRelativeProj.localModuleEquivOfBijective_app _ _ _ V hV x

/-- The section comparison undoes the chart identification. -/
public theorem mapSection_chartLoc (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ U) (x : (E.algebra.piece n).val.obj (op V)) :
    E.mapSection U hU hB n ((relativeProj A).chart U hU ⁻¹ᵁ V)
        ((chartLoc E U hU hB n).app V hV x) =
      (E.algebra.piece n).val.map
        (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op x :=
  Eq.trans
    (congrArg (E.mapSection U hU hB n ((relativeProj A).chart U hU ⁻¹ᵁ V))
      (chartLoc_app_eq E U hU hB n V hV x))
    (TwistRigidity.iso_inv_app_hom_app (E.chartIso U hU hB n)
      (op ((relativeProj A).chart U hU ⁻¹ᵁ V)) _)

/-- The chart identification carries the product to the canonical product of absolute twists. -/
public theorem chartLoc_mul (i j : ℤ) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (x : (E.algebra.piece i).val.obj (op V)) (y : (E.algebra.piece j).val.obj (op V)) :
    (chartLoc E U hU hB (i + j)).app V hV ((E.algebra.mul i j).app (op V) x y) =
      absoluteTwistProduct (A.grading U) i j ((relativeProj A).chart U hU ⁻¹ᵁ V)
        ((chartLoc E U hU hB i).app V hV x) ((chartLoc E U hU hB j).app V hV y) := by
  refine Eq.trans (chartLoc_app_eq E U hU hB (i + j) V hV _) ?_
  refine Eq.trans (congrArg ((E.chartIso U hU hB (i + j)).hom.val.app
      (op ((relativeProj A).chart U hU ⁻¹ᵁ V)))
    ((E.algebra.mul i j).naturality
      (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op x y)) ?_
  refine Eq.trans (E.chartIso_hom_mul U hU hB i j ((relativeProj A).chart U hU ⁻¹ᵁ V) _ _) ?_
  exact congrArg₂ (absoluteTwistProduct (A.grading U) i j ((relativeProj A).chart U hU ⁻¹ᵁ V))
    (chartLoc_app_eq E U hU hB i V hV x).symm (chartLoc_app_eq E U hU hB j V hV y).symm

/-- **The chart identification carries the homogeneous-section map to the restriction of the
absolute homogeneous section.** -/
public theorem chartLoc_psi (k : ℕ) (a : A.sectionPieces U k) :
    (chartLoc E U hU hB (k : ℤ)).app ((relativeProj A).toBase ⁻¹ᵁ U) le_rfl
        ((E.ψ k).val.app (op U) a) =
      (twistingSheaf (A.grading U) (k : ℤ)).val.map
        (homOfLE (le_top :
          (relativeProj A).chart U hU ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U) ≤ ⊤)).op
        (degreeSection (A.grading U) k
          ⟨DirectSum.of (A.sectionPieces U) k a, A.of_mem_grading U a⟩) := by
  have hVle : (relativeProj A).chart U hU ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U) ≤ ⊤ := le_top
  refine E.mapSection_injective U hU hB (k : ℤ)
    ((relativeProj A).chart U hU ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U)) ?_
  have h1 := mapSection_chartLoc E U hU hB (k : ℤ) ((relativeProj A).toBase ⁻¹ᵁ U) le_rfl
    ((E.ψ k).val.app (op U) a)
  have h2 := PresheafOfModules.naturality_apply
    (E.chartIso U hU hB (k : ℤ)).inv.val (homOfLE hVle).op
    (degreeSection (A.grading U) k
      ⟨DirectSum.of (A.sectionPieces U) k a, A.of_mem_grading U a⟩)
  have h3 := E.ψ_chart U hU hB k a
  have h4 := PresheafOfModules.rec_eq_map (E.algebra.piece (k : ℤ)).val
    (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU).symm ((E.ψ k).val.app (op U) a)
  have h5 := PresheafOfModules.map_map_eq_map (E.algebra.piece (k : ℤ)).val
    (eqToHom (RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU)).op
    (homOfLE (((relativeProj A).chart U hU).image_mono hVle)).op
    (homOfLE (((relativeProj A).chart U hU).image_preimage_le
      ((relativeProj A).toBase ⁻¹ᵁ U))).op ((E.ψ k).val.app (op U) a)
  refine h1.trans (Eq.trans ?_ h2.symm)
  refine Eq.trans ?_ (congrArg
    ((Scheme.Modules.restrict (E.algebra.piece (k : ℤ))
      ((relativeProj A).chart U hU)).val.map (homOfLE hVle).op) (h3.trans h4)).symm
  exact h5.symm

end Chart

/-! ### The comparison over one member -/

section Cmp

variable (D E : BasisTwistData A 𝔅) (U : S.Opens) (hU : IsAffineOpen U) (hB : U ∈ 𝔅)

/-- **The comparison of two data over a member of `𝔅`.** -/
public def cmp (n : ℤ) :
    TopCat.Sheaf.LocalModuleEquiv (D.algebra.piece n).val (E.algebra.piece n).val
      ((relativeProj A).toBase ⁻¹ᵁ U) :=
  ChartTransRelativeProj.modelPair (chartLoc D U hU hB n) (chartLoc E U hU hB n)

/-- The comparison followed by the chart identification of the second datum is the chart
identification of the first. -/
public theorem chartLoc_cmp (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ U) (x : (D.algebra.piece n).val.obj (op V)) :
    (chartLoc E U hU hB n).app V hV ((cmp D E U hU hB n).app V hV x) =
      (chartLoc D U hU hB n).app V hV x :=
  (congrArg ((chartLoc E U hU hB n).app V hV)
      (ChartTransRelativeProj.modelPair_app (chartLoc D U hU hB n) (chartLoc E U hU hB n)
        V hV x)).trans
    (LinearEquiv.apply_symm_apply ((chartLoc E U hU hB n).app V hV) _)

/-- The comparison sends `x` to `y` when the chart identification of the second datum sends `y`
where that of the first sends `x`. -/
public theorem cmp_eq_of_chartLoc_eq (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    {x : (D.algebra.piece n).val.obj (op V)} {y : (E.algebra.piece n).val.obj (op V)}
    (hxy : (chartLoc E U hU hB n).app V hV y = (chartLoc D U hU hB n).app V hV x) :
    (cmp D E U hU hB n).app V hV x = y :=
  ((chartLoc E U hU hB n).app V hV).injective
    ((chartLoc_cmp D E U hU hB n V hV x).trans hxy.symm)

/-- The comparison over a member of `𝔅` is multiplicative. -/
public theorem cmp_mul (i j : ℤ) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (x : (D.algebra.piece i).val.obj (op V)) (y : (D.algebra.piece j).val.obj (op V)) :
    (cmp D E U hU hB (i + j)).app V hV ((D.algebra.mul i j).app (op V) x y) =
      (E.algebra.mul i j).app (op V)
        ((cmp D E U hU hB i).app V hV x) ((cmp D E U hU hB j).app V hV y) := by
  refine cmp_eq_of_chartLoc_eq D E U hU hB (i + j) V hV ?_
  refine Eq.trans (chartLoc_mul E U hU hB i j V hV _ _) ?_
  refine Eq.trans ?_ (chartLoc_mul D U hU hB i j V hV x y).symm
  exact congrArg₂ (absoluteTwistProduct (A.grading U) i j ((relativeProj A).chart U hU ⁻¹ᵁ V))
    (chartLoc_cmp D E U hU hB i V hV x) (chartLoc_cmp D E U hU hB j V hV y)

/-- The comparison over a member of `𝔅` carries the first homogeneous-section map to the
second. -/
public theorem cmp_psi (k : ℕ) (a : A.sectionPieces U k) :
    (cmp D E U hU hB (k : ℤ)).app ((relativeProj A).toBase ⁻¹ᵁ U) le_rfl
        ((D.ψ k).val.app (op U) a) = (E.ψ k).val.app (op U) a :=
  cmp_eq_of_chartLoc_eq D E U hU hB (k : ℤ) ((relativeProj A).toBase ⁻¹ᵁ U) le_rfl
    ((chartLoc_psi E U hU hB k a).trans (chartLoc_psi D U hU hB k a).symm)

end Cmp

/-! ### Agreement on the overlaps, by relative rigidity -/

/-- The inverse images of a nested pair of opens of the base are nested. -/
public theorem preimage_mono {W U : S.Opens} (h : W ≤ U) :
    (relativeProj A).toBase ⁻¹ᵁ W ≤ (relativeProj A).toBase ⁻¹ᵁ U :=
  fun _ hx => h hx

/-- The image of the chart over the smaller member lies in the inverse image of the larger. -/
public theorem chart_image_le {W U : S.Opens} (h : W ≤ U) (hW : IsAffineOpen W) :
    (relativeProj A).chart W hW ''ᵁ (⊤ : (AlgebraicGeometry.Proj (A.grading W)).Opens) ≤
      (relativeProj A).toBase ⁻¹ᵁ U :=
  (RelativeProjTwistGlue.chart_image_top (relativeProj A) W hW).le.trans (preimage_mono h)

section Nested

variable (D E : BasisTwistData A 𝔅) {W U : S.Opens} (h : W ≤ U) (hW : IsAffineOpen W)
  (hU : IsAffineOpen U) (hWB : W ∈ 𝔅) (hUB : U ∈ 𝔅)

/-- The comparison attached to the larger member, restricted along the chart of the smaller. -/
public def overlapIso (n : ℤ) :
    Scheme.Modules.restrict (D.algebra.piece n) ((relativeProj A).chart W hW) ≅
      Scheme.Modules.restrict (E.algebra.piece n) ((relativeProj A).chart W hW) :=
  isoOfLocalEquiv
    (restrictLocalEquiv ((relativeProj A).chart W hW) (cmp D E U hU hUB n)
      (chart_image_le h hW))

/-- **The overlap endomorphism** of the absolute twists on `Proj Γ(W, A)`. -/
public def overlapEndo (n : ℤ) :
    twistingSheaf (A.grading W) n ⟶ twistingSheaf (A.grading W) n :=
  (D.chartIso W hW hWB n).inv ≫ (overlapIso D E h hW hU hUB n).hom ≫
    (E.chartIso W hW hWB n).hom

/-- The overlap endomorphism on sections. -/
public theorem overlapEndo_app (n : ℤ) (V : (AlgebraicGeometry.Proj (A.grading W)).Opens)
    (a : (twistingSheaf (A.grading W) n).val.obj (op V)) :
    (overlapEndo D E h hW hU hWB hUB n).val.app (op V) a =
      (E.chartIso W hW hWB n).hom.val.app (op V)
        ((cmp D E U hU hUB n).app ((relativeProj A).chart W hW ''ᵁ V)
          ((((relativeProj A).chart W hW).image_mono le_top).trans (chart_image_le h hW))
          ((D.chartIso W hW hWB n).inv.val.app (op V) a)) :=
  rfl

/-- **The overlap endomorphism is multiplicative.** -/
public theorem isMultiplicative_overlapEndo :
    TwistRigidity.IsMultiplicative (overlapEndo D E h hW hU hWB hUB) := by
  intro i j V a b
  have hV := (((relativeProj A).chart W hW).image_mono (le_top (a := V))).trans
    (chart_image_le h hW)
  have ha := TwistRigidity.iso_hom_app_inv_app (D.chartIso W hW hWB i) (op V) a
  have hb := TwistRigidity.iso_hom_app_inv_app (D.chartIso W hW hWB j) (op V) b
  have hprod : absoluteTwistProduct (A.grading W) i j V a b =
      (D.chartIso W hW hWB (i + j)).hom.val.app (op V)
        ((D.algebra.mul i j).app (op ((relativeProj A).chart W hW ''ᵁ V))
          ((D.chartIso W hW hWB i).inv.val.app (op V) a)
          ((D.chartIso W hW hWB j).inv.val.app (op V) b)) :=
    (congrArg₂ (absoluteTwistProduct (A.grading W) i j V) ha.symm hb.symm).trans
      (D.chartIso_hom_mul W hW hWB i j V _ _).symm
  refine Eq.trans (overlapEndo_app D E h hW hU hWB hUB (i + j) V _) ?_
  refine Eq.trans (congrArg (fun z => (E.chartIso W hW hWB (i + j)).hom.val.app (op V)
      ((cmp D E U hU hUB (i + j)).app ((relativeProj A).chart W hW ''ᵁ V) hV
        ((D.chartIso W hW hWB (i + j)).inv.val.app (op V) z))) hprod) ?_
  refine Eq.trans (congrArg (fun z => (E.chartIso W hW hWB (i + j)).hom.val.app (op V)
      ((cmp D E U hU hUB (i + j)).app ((relativeProj A).chart W hW ''ᵁ V) hV z))
    (TwistRigidity.iso_inv_app_hom_app (D.chartIso W hW hWB (i + j)) (op V) _)) ?_
  refine Eq.trans (congrArg ((E.chartIso W hW hWB (i + j)).hom.val.app (op V))
    (cmp_mul D E U hU hUB i j _ hV _ _)) ?_
  exact E.chartIso_hom_mul W hW hWB i j V _ _

/-- **The overlap endomorphism fixes the homogeneous sections restricted from the larger
member.** -/
public theorem fixes_degreeSection_resPiece (k : ℕ) (b : A.sectionPieces U k) :
    (overlapEndo D E h hW hU hWB hUB (k : ℤ)).val.app (op ⊤)
        (degreeSection (A.grading W) k
          ⟨DirectSum.of (A.sectionPieces W) k (A.resPiece h k b),
            A.of_mem_grading W (A.resPiece h k b)⟩) =
      degreeSection (A.grading W) k
        ⟨DirectSum.of (A.sectionPieces W) k (A.resPiece h k b),
          A.of_mem_grading W (A.resPiece h k b)⟩ := by
  have hle : (relativeProj A).chart W hW ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W) ≤ ⊤ := le_top
  have hτ : (relativeProj A).chart W hW ''ᵁ
      ((relativeProj A).chart W hW ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W)) ≤
        (relativeProj A).toBase ⁻¹ᵁ U :=
    (((relativeProj A).chart W hW).image_preimage_le _).trans (preimage_mono h)
  have hinj := twistingSheaf_map_preimage_injective (A := A) W hW (k : ℤ)
  refine hinj ?_
  refine Eq.trans (PresheafOfModules.naturality_apply
    (overlapEndo D E h hW hU hWB hUB (k : ℤ)).val (homOfLE hle).op _).symm ?_
  refine Eq.trans (congrArg ((overlapEndo D E h hW hU hWB hUB (k : ℤ)).val.app
    (op ((relativeProj A).chart W hW ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W))))
    (chartLoc_psi D W hW hWB k (A.resPiece h k b)).symm) ?_
  refine Eq.trans ?_ (chartLoc_psi E W hW hWB k (A.resPiece h k b))
  refine Eq.trans (overlapEndo_app D E h hW hU hWB hUB (k : ℤ) _ _) ?_
  refine Eq.trans ?_ (chartLoc_app_eq E W hW hWB (k : ℤ) _ le_rfl _).symm
  refine congrArg ((E.chartIso W hW hWB (k : ℤ)).hom.val.app
    (op ((relativeProj A).chart W hW ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W)))) ?_
  have hD1 := TwistRigidity.iso_inv_app_hom_app (D.chartIso W hW hWB (k : ℤ))
    (op ((relativeProj A).chart W hW ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W)))
    ((D.algebra.piece (k : ℤ)).val.map
      (homOfLE (((relativeProj A).chart W hW).image_preimage_le
        ((relativeProj A).toBase ⁻¹ᵁ W))).op ((D.ψ k).val.app (op W) (A.resPiece h k b)))
  refine Eq.trans (ChartTransRelativeProj.app_congr_arg (cmp D E U hU hUB (k : ℤ)) _
    ((congrArg ((D.chartIso W hW hWB (k : ℤ)).inv.val.app
      (op ((relativeProj A).chart W hW ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W))))
      (chartLoc_app_eq D W hW hWB (k : ℤ) _ le_rfl _)).trans hD1)) ?_
  have hDnat := PresheafOfModules.naturality_apply (D.ψ k).val (homOfLE h).op b
  have hEnat := PresheafOfModules.naturality_apply (E.ψ k).val (homOfLE h).op b
  refine Eq.trans (ChartTransRelativeProj.app_congr_arg (cmp D E U hU hUB (k : ℤ)) _
    ((congrArg ((D.algebra.piece (k : ℤ)).val.map
      (homOfLE (((relativeProj A).chart W hW).image_preimage_le
        ((relativeProj A).toBase ⁻¹ᵁ W))).op) hDnat).trans
      (PresheafOfModules.map_map_eq_map (D.algebra.piece (k : ℤ)).val _ _
        (homOfLE hτ).op _))) ?_
  refine Eq.trans ((cmp D E U hU hUB (k : ℤ)).naturality le_rfl hτ
    ((D.ψ k).val.app (op U) b)) ?_
  refine Eq.trans (congrArg ((E.algebra.piece (k : ℤ)).val.resLE hτ)
    (cmp_psi D E U hU hUB k b)) ?_
  refine Eq.trans ?_ (congrArg ((E.algebra.piece (k : ℤ)).val.map
      (homOfLE (((relativeProj A).chart W hW).image_preimage_le
        ((relativeProj A).toBase ⁻¹ᵁ W))).op) hEnat).symm
  exact (PresheafOfModules.map_map_eq_map (E.algebra.piece (k : ℤ)).val
    (homOfLE (preimage_mono h)).op _ (homOfLE hτ).op _).symm

/-- The overlap endomorphism satisfies the relative fixing hypothesis. -/
public theorem fixesResDegreeSections_overlapEndo :
    RelativeTwistRigidity.FixesResDegreeSections (A.res h)
      (overlapEndo D E h hW hU hWB hUB) := by
  intro k c
  obtain ⟨b, hb⟩ := c.2
  have hw : (⟨(A.res h) (c : A.sectionRing U), (A.res h).map_mem c.2⟩ : A.grading W k) =
      ⟨DirectSum.of (A.sectionPieces W) k (A.resPiece h k b),
        A.of_mem_grading W (A.resPiece h k b)⟩ :=
    Subtype.ext ((congrArg (fun z : A.sectionRing U => (A.res h) z) hb).symm.trans
      (A.resRingHom_of h b))
  exact (congrArg (fun w : A.grading W k =>
      (overlapEndo D E h hW hU hWB hUB (k : ℤ)).val.app (op ⊤)
        (degreeSection (A.grading W) k w)) hw).trans
    ((fixes_degreeSection_resPiece D E h hW hU hWB hUB k b).trans
      (congrArg (fun w : A.grading W k => degreeSection (A.grading W) k w) hw).symm)

/-- **The overlap endomorphism is the identity**, by relative rigidity. -/
public theorem overlapEndo_eq_id (n : ℤ) :
    overlapEndo D E h hW hU hWB hUB n = 𝟙 (twistingSheaf (A.grading W) n) :=
  RelativeTwistRigidity.eq_id_res A W U h hW hU
    (isMultiplicative_overlapEndo D E h hW hU hWB hUB)
    (fixesResDegreeSections_overlapEndo D E h hW hU hWB hUB) n

include h in
/-- **The comparisons attached to a nested pair of members agree.** -/
public theorem cmp_agreeOn_nested (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (hVU : V ≤ (relativeProj A).toBase ⁻¹ᵁ U) (hVW : V ≤ (relativeProj A).toBase ⁻¹ᵁ W) :
    ChartTransRelativeProj.AgreeOn (cmp D E U hU hUB n) (cmp D E W hW hWB n) V hVU hVW := by
  intro x
  set j := (relativeProj A).chart W hW with hj
  have hIm : j ''ᵁ (j ⁻¹ᵁ V) = V :=
    TwistUnique.image_preimage_eq_self j
      (hVW.trans (RelativeProjTwistGlue.chart_image_top (relativeProj A) W hW).ge)
  have hid := congrArg
    (fun φ : twistingSheaf (A.grading W) n ⟶ twistingSheaf (A.grading W) n =>
      φ.val.app (op (j ⁻¹ᵁ V)) ((chartLoc D W hW hWB n).app V hVW x))
    (overlapEndo_eq_id D E h hW hU hWB hUB n)
  simp only at hid
  have hl : (overlapEndo D E h hW hU hWB hUB n).val.app (op (j ⁻¹ᵁ V))
      ((chartLoc D W hW hWB n).app V hVW x) =
      (E.chartIso W hW hWB n).hom.val.app (op (j ⁻¹ᵁ V))
        ((E.algebra.piece n).val.map (homOfLE (j.image_preimage_le V)).op
          ((cmp D E U hU hUB n).app V hVU x)) := by
    refine Eq.trans (overlapEndo_app D E h hW hU hWB hUB n _ _) ?_
    refine congrArg ((E.chartIso W hW hWB n).hom.val.app (op (j ⁻¹ᵁ V))) ?_
    refine Eq.trans (congrArg ((cmp D E U hU hUB n).app (j ''ᵁ (j ⁻¹ᵁ V)) _)
      ((congrArg ((D.chartIso W hW hWB n).inv.val.app (op (j ⁻¹ᵁ V)))
        (chartLoc_app_eq D W hW hWB n V hVW x)).trans
        (TwistRigidity.iso_inv_app_hom_app (D.chartIso W hW hWB n) _ _))) ?_
    exact (cmp D E U hU hUB n).naturality hVU (j.image_preimage_le V) x
  have hr : (chartLoc D W hW hWB n).app V hVW x =
      (E.chartIso W hW hWB n).hom.val.app (op (j ⁻¹ᵁ V))
        ((E.algebra.piece n).val.map (homOfLE (j.image_preimage_le V)).op
          ((cmp D E W hW hWB n).app V hVW x)) :=
    (chartLoc_cmp D E W hW hWB n V hVW x).symm.trans
      (chartLoc_app_eq E W hW hWB n V hVW _)
  have hcomb := (hl.symm.trans hid).trans hr
  have hres :=
    (TwistRigidity.iso_inv_app_hom_app (E.chartIso W hW hWB n) (op (j ⁻¹ᵁ V)) _).symm.trans
      ((congrArg ((E.chartIso W hW hWB n).inv.val.app (op (j ⁻¹ᵁ V))) hcomb).trans
        (TwistRigidity.iso_inv_app_hom_app (E.chartIso W hW hWB n) (op (j ⁻¹ᵁ V)) _))
  have h1 := PresheafOfModules.map_map_eq_self (E.algebra.piece n).val
    (homOfLE (j.image_preimage_le V)).op (homOfLE hIm.ge).op ((cmp D E U hU hUB n).app V hVU x)
  have h2 := PresheafOfModules.map_map_eq_self (E.algebra.piece n).val
    (homOfLE (j.image_preimage_le V)).op (homOfLE hIm.ge).op ((cmp D E W hW hWB n).app V hVW x)
  exact h1.symm.trans ((congrArg ((E.algebra.piece n).val.map (homOfLE hIm.ge).op) hres).trans h2)

end Nested

variable (h𝔅 : Opens.IsBasis 𝔅) (h𝔅a : ∀ U ∈ 𝔅, IsAffineOpen U)

include h𝔅 in
/-- The members of `𝔅` below an open of the base cover its inverse image. -/
public theorem le_iSup_preimage_le (T : S.Opens) :
    (relativeProj A).toBase ⁻¹ᵁ T ≤
      ⨆ m : {m : S.Opens // m ∈ 𝔅 ∧ m ≤ T}, (relativeProj A).toBase ⁻¹ᵁ m.1 := by
  intro x hx
  obtain ⟨m, hmB, hxm, hmT⟩ := Opens.isBasis_iff_nbhd.mp h𝔅
    (show (relativeProj A).toBase x ∈ T from hx)
  exact Opens.mem_iSup.mpr ⟨⟨m, hmB, hmT⟩, hxm⟩

include h𝔅 in
/-- The inverse images of the members of `𝔅` cover the relative Proj. -/
public theorem iSup_preimage_eq_top :
    (⨆ m : {m : S.Opens // m ∈ 𝔅}, (relativeProj A).toBase ⁻¹ᵁ m.1) = ⊤ := by
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨⟨m, hmB, _⟩, hxm⟩ := Opens.mem_iSup.mp
    (le_iSup_preimage_le h𝔅 ⊤ (show x ∈ (relativeProj A).toBase ⁻¹ᵁ ⊤ from trivial))
  exact Opens.mem_iSup.mpr ⟨⟨m, hmB⟩, hxm⟩

include h𝔅 h𝔅a in
/-- **Any two comparisons agree where both are defined.** -/
public theorem cmp_agreeOn (D E : BasisTwistData A 𝔅) (P Q : S.Opens) (hP : IsAffineOpen P)
    (hQ : IsAffineOpen Q) (hPB : P ∈ 𝔅) (hQB : Q ∈ 𝔅) (n : ℤ)
    (V : (relativeProj A).scheme.Opens)
    (hVP : V ≤ (relativeProj A).toBase ⁻¹ᵁ P) (hVQ : V ≤ (relativeProj A).toBase ⁻¹ᵁ Q) :
    ChartTransRelativeProj.AgreeOn (cmp D E P hP hPB n) (cmp D E Q hQ hQB n) V hVP hVQ := by
  refine ChartTransRelativeProj.agreeOn_of_cover (E.algebra.piece n).isSheaf _ _
    (fun r : {m : S.Opens // m ∈ 𝔅 ∧ m ≤ P ⊓ Q} => (relativeProj A).toBase ⁻¹ᵁ r.1)
    (fun r V' hV'P hV'Q hV'r x => ?_) V hVP hVQ
    ((show V ≤ (relativeProj A).toBase ⁻¹ᵁ (P ⊓ Q) from fun y hy => ⟨hVP hy, hVQ hy⟩).trans
      (le_iSup_preimage_le h𝔅 (P ⊓ Q)))
  have hr := h𝔅a r.1 r.2.1
  refine Eq.trans (cmp_agreeOn_nested D E (r.2.2.trans inf_le_left) hr hP r.2.1 hPB n
    V' hV'P hV'r x) ?_
  exact (cmp_agreeOn_nested D E (r.2.2.trans inf_le_right) hr hQ r.2.1 hQB n
    V' hV'Q hV'r x).symm

/-! ### The glued isomorphism -/

section Glue

variable (D E : BasisTwistData A 𝔅)

/-- The comparisons, as a family indexed by the members of `𝔅`. -/
public def cmpFamily (n : ℤ) (i : {m : S.Opens // m ∈ 𝔅}) :
    TopCat.Sheaf.LocalModuleEquiv (D.algebra.piece n).val (E.algebra.piece n).val
      ((relativeProj A).toBase ⁻¹ᵁ i.1) :=
  cmp D E i.1 (h𝔅a i.1 i.2) i.2 n

/-- **The glued comparison**, as a local isomorphism on the whole relative Proj. -/
public def glueLoc (n : ℤ) :
    TopCat.Sheaf.LocalModuleEquiv (D.algebra.piece n).val (E.algebra.piece n).val ⊤ :=
  TopCat.Sheaf.LocalModuleEquiv.glueLE (D.algebra.piece n).isSheaf
    (E.algebra.piece n).isSheaf (cmpFamily h𝔅a D E n)
    (fun i j V hVi hVj x => cmp_agreeOn h𝔅 h𝔅a D E i.1 j.1 _ _ i.2 j.2 n V hVi hVj x)
    (iSup_preimage_eq_top h𝔅).ge

/-- **The glued isomorphism of the `n`-th pieces of two data.** -/
public def glueIso (n : ℤ) : D.algebra.piece n ≅ E.algebra.piece n :=
  isoOfLocalEquiv (X := (relativeProj A).scheme) (glueLoc h𝔅 h𝔅a D E n)

/-- Over the inverse image of a member of `𝔅` the glued isomorphism is the comparison there. -/
public theorem glueIso_hom_app_of_le (U : S.Opens) (hU : IsAffineOpen U) (hB : U ∈ 𝔅) (n : ℤ)
    (V : (relativeProj A).scheme.Opens) (hVU : V ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (x : (D.algebra.piece n).val.obj (op V)) :
    (glueIso h𝔅 h𝔅a D E n).hom.val.app (op V) x = (cmp D E U hU hB n).app V hVU x :=
  (isoOfLocalEquiv_hom_app (X := (relativeProj A).scheme) (glueLoc h𝔅 h𝔅a D E n) V x).trans
    (TopCat.Sheaf.LocalModuleEquiv.glueLE_app_of_le (D.algebra.piece n).isSheaf
      (E.algebra.piece n).isSheaf (cmpFamily h𝔅a D E n)
      (fun i j V hVi hVj x => cmp_agreeOn h𝔅 h𝔅a D E i.1 j.1 _ _ i.2 j.2 n V hVi hVj x)
      (iSup_preimage_eq_top h𝔅).ge (i := ⟨U, hB⟩) le_top hVU x)

/-- **The glued isomorphism is multiplicative**, over every open of the relative Proj. -/
public theorem glueIso_mul (i j : ℤ) (V : (relativeProj A).scheme.Opensᵒᵖ)
    (x : (D.algebra.piece i).val.obj V) (y : (D.algebra.piece j).val.obj V) :
    (glueIso h𝔅 h𝔅a D E (i + j)).hom.val.app V ((D.algebra.mul i j).app V x y) =
      (E.algebra.mul i j).app V ((glueIso h𝔅 h𝔅a D E i).hom.val.app V x)
        ((glueIso h𝔅 h𝔅a D E j).hom.val.app V y) := by
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (E.algebra.piece (i + j)).isSheaf
    (fun m : {m : S.Opens // m ∈ 𝔅} => V.unop ⊓ (relativeProj A).toBase ⁻¹ᵁ m.1)
    (fun _ => inf_le_left)
    (TopCat.Sheaf.le_iSup_inf (iSup_preimage_eq_top h𝔅) V.unop) fun m => ?_
  refine Eq.trans (PresheafOfModules.app_resLE (glueIso h𝔅 h𝔅a D E (i + j)).hom.val
    (inf_le_left : V.unop ⊓ (relativeProj A).toBase ⁻¹ᵁ m.1 ≤ V.unop)
    ((D.algebra.mul i j).app V x y)).symm ?_
  refine Eq.trans (congrArg ((glueIso h𝔅 h𝔅a D E (i + j)).hom.val.app
    (op (V.unop ⊓ (relativeProj A).toBase ⁻¹ᵁ m.1)))
    ((D.algebra.mul i j).naturality
      (homOfLE (inf_le_left : V.unop ⊓ (relativeProj A).toBase ⁻¹ᵁ m.1 ≤ V.unop)).op x y)) ?_
  refine Eq.trans (glueIso_hom_app_of_le h𝔅 h𝔅a D E m.1 (h𝔅a m.1 m.2) m.2 (i + j)
    (V.unop ⊓ (relativeProj A).toBase ⁻¹ᵁ m.1) inf_le_right _) ?_
  refine Eq.trans (cmp_mul D E m.1 (h𝔅a m.1 m.2) m.2 i j
    (V.unop ⊓ (relativeProj A).toBase ⁻¹ᵁ m.1) inf_le_right _ _) ?_
  refine Eq.trans (TwistRigidity.mul_app_congr E.algebra i j _
    (glueIso_hom_app_of_le h𝔅 h𝔅a D E m.1 (h𝔅a m.1 m.2) m.2 i
      (V.unop ⊓ (relativeProj A).toBase ⁻¹ᵁ m.1) inf_le_right _).symm
    (glueIso_hom_app_of_le h𝔅 h𝔅a D E m.1 (h𝔅a m.1 m.2) m.2 j
      (V.unop ⊓ (relativeProj A).toBase ⁻¹ᵁ m.1) inf_le_right _).symm) ?_
  refine Eq.trans (TwistRigidity.mul_app_congr E.algebra i j _
    (PresheafOfModules.app_resLE (glueIso h𝔅 h𝔅a D E i).hom.val
      (inf_le_left : V.unop ⊓ (relativeProj A).toBase ⁻¹ᵁ m.1 ≤ V.unop) x)
    (PresheafOfModules.app_resLE (glueIso h𝔅 h𝔅a D E j).hom.val
      (inf_le_left : V.unop ⊓ (relativeProj A).toBase ⁻¹ᵁ m.1 ≤ V.unop) y)) ?_
  exact ((E.algebra.mul i j).naturality
    (homOfLE (inf_le_left : V.unop ⊓ (relativeProj A).toBase ⁻¹ᵁ m.1 ≤ V.unop)).op _ _).symm

/-- **The glued isomorphism carries the first homogeneous-section map to the second**, over every
open of the base. -/
public theorem glueIso_psi (k : ℕ) :
    D.ψ k ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (glueIso h𝔅 h𝔅a D E (k : ℤ)).hom = E.ψ k := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (E.algebra.piece (k : ℤ)).isSheaf
    (fun m : {m : S.Opens // m ∈ 𝔅 ∧ m ≤ V.unop} => (relativeProj A).toBase ⁻¹ᵁ m.1)
    (fun m => preimage_mono m.2.2) (le_iSup_preimage_le h𝔅 V.unop) fun m => ?_
  refine Eq.trans (PresheafOfModules.app_resLE (glueIso h𝔅 h𝔅a D E (k : ℤ)).hom.val
    (preimage_mono m.2.2) ((D.ψ k).val.app V s)).symm ?_
  refine Eq.trans (congrArg ((glueIso h𝔅 h𝔅a D E (k : ℤ)).hom.val.app
      (op ((relativeProj A).toBase ⁻¹ᵁ m.1)))
    (PresheafOfModules.app_resLE (D.ψ k).val m.2.2 s).symm) ?_
  refine Eq.trans (glueIso_hom_app_of_le h𝔅 h𝔅a D E m.1 (h𝔅a m.1 m.2.1) m.2.1 (k : ℤ)
    ((relativeProj A).toBase ⁻¹ᵁ m.1) le_rfl _) ?_
  refine Eq.trans (cmp_psi D E m.1 (h𝔅a m.1 m.2.1) m.2.1 k
    ((A.piece (k : ℤ)).val.resLE m.2.2 s)) ?_
  exact PresheafOfModules.app_resLE (E.ψ k).val m.2.2 s

/-- The forward homomorphism of graded algebras. -/
public def glueHom : D.algebra ⟶ E.algebra where
  app n := (glueIso h𝔅 h𝔅a D E n).hom
  map_mul i j V x y := glueIso_mul h𝔅 h𝔅a D E i j V x y

/-- The backward homomorphism of graded algebras. -/
public def glueInvHom : E.algebra ⟶ D.algebra where
  app n := (glueIso h𝔅 h𝔅a D E n).inv
  map_mul i j V x y :=
    ((TwistRigidity.iso_inv_app_hom_app (glueIso h𝔅 h𝔅a D E (i + j)) V
          ((D.algebra.mul i j).app V ((glueIso h𝔅 h𝔅a D E i).inv.val.app V x)
            ((glueIso h𝔅 h𝔅a D E j).inv.val.app V y))).symm.trans
        (congrArg ((glueIso h𝔅 h𝔅a D E (i + j)).inv.val.app V)
          ((glueIso_mul h𝔅 h𝔅a D E i j V _ _).trans
            (TwistRigidity.mul_app_congr E.algebra i j V
              (TwistRigidity.iso_hom_app_inv_app (glueIso h𝔅 h𝔅a D E i) V x)
              (TwistRigidity.iso_hom_app_inv_app (glueIso h𝔅 h𝔅a D E j) V y))))).symm

/-- **The isomorphism of the graded algebras of two data over a basis.** -/
public def glueAlgIso : D.algebra ≅ E.algebra where
  hom := glueHom h𝔅 h𝔅a D E
  inv := glueInvHom h𝔅 h𝔅a D E
  hom_inv_id :=
    SheafOfModules.GradedAlgebra.Hom.ext fun n => (glueIso h𝔅 h𝔅a D E n).hom_inv_id
  inv_hom_id :=
    SheafOfModules.GradedAlgebra.Hom.ext fun n => (glueIso h𝔅 h𝔅a D E n).inv_hom_id

/-- The degree-`n` component of `glueAlgIso` is `glueIso`. -/
@[simp] public theorem glueAlgIso_hom_app (n : ℤ) :
    (glueAlgIso h𝔅 h𝔅a D E).hom.app n = (glueIso h𝔅 h𝔅a D E n).hom := rfl

end Glue

end Stacks.AlgebraicGeometry.TwistExistenceBasis

end
