module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.Iso
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistAlgebra
public import StacksFrontier.AlgebraicGeometry.TwistExistence.Basis

/-!
# The pulled-back twists of a relative `Proj` on the charts of its base change

Let `A` be a quasi-coherent graded `𝒪_S`-algebra, `g : S' ⟶ S` a morphism of schemes and
`f : Proj_{S'}(g^*A) ⟶ Proj_S(A)` the base-change morphism of
`Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom`. This file factors the chart
of `Proj_{S'}(g^*A)` over an affine open `V` of `S'` lying over an affine open `U` of `S`, followed
by `f`, as `Proj Γ(V, g^*A) ≅ U(φ) ⟶ Proj Γ(U, A) ⟶ Proj_S(A)` for the graded ring map
`φ : Γ(U, A) ⟶ Γ(V, g^*A)` of sections, and provides the generic leg calculus (`legTail`,
`legTail_mul`) along which the inverse image `f^*𝒪_{Proj_S(A)}(n)` of the twists of Tag 01NR is
identified with the absolute twists of `Proj Γ(V, g^*A)`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeBasis`: the affine opens of `S'`
  carried into an affine open of `S`.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.legTail`: the leg of an inverse image
  along a factorization, followed by a comparison map.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.chart_comp_baseChangeHom`: the
  factorization of the chart followed by `f`.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.legTail_mul`: the leg is multiplicative.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.ProjPresentation
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare Stacks.AlgebraicGeometry.ProjTwistTheta
open Stacks.AlgebraicGeometry.Tag07ZGTwist

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### Generic multiplicativity inputs -/

section Generic

/-- The categorical shape of `mul_pullbackId`, with every object and morphism free. -/
theorem mul_of_unitor_gen {C : Type*} [Category C] {T T' P P' Q : C}
    {cinv : T ⟶ T'} {chom : T' ⟶ T} {Fm : T' ⟶ P'} {p : P' ⟶ Q} {pT : T' ⟶ P}
    {tsm : T ⟶ P} {mul : P ⟶ Q}
    (hcc : cinv ≫ chom = 𝟙 T) (hc : chom ≫ tsm = pT) (hn : Fm ≫ p = pT ≫ mul) :
    (cinv ≫ Fm) ≫ p = tsm ≫ mul := by
  rw [Category.assoc, hn, ← hc, Category.assoc, ← Category.assoc cinv, hcc, Category.id_comp]

variable {X : Scheme.{u}}

/-- **The identification of the inverse image along the identity is multiplicative.** -/
theorem mul_pullbackId {Pm Pn Pmn : X.Modules}
    (mul : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj (Pm)).obj (Pn)) ⟶ Pmn) :
    TwistMulLeg.pbMul (𝟙 X) mul ≫ (Scheme.Modules.pullbackId X).hom.app Pmn =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩)).map
          (((Scheme.Modules.pullbackId X).hom.app Pm,
            (Scheme.Modules.pullbackId X).hom.app Pn) : (_, _) ⟶ (_, _))) ≫ mul :=
  mul_of_unitor_gen
    (Iso.inv_hom_id_app (Stacks.PullbackTensorIso.pullbackTensorIso
      (𝟙 X : X ⟶ X).toLRSHom.toShHom) (Pm, Pn))
    (TwistMultTransport.comparison_pullbackId X Pm Pn)
    ((Scheme.Modules.pullbackId X).hom.naturality mul)

/-- **A leg, followed by the inverse image of a morphism, followed by the contraction of a
section.** For a factorization `k ≫ h = ρ ≫ hU ≫ c` with `ρ ≫ ι = 𝟙`, an identification `χ` of
`c^*M` with `N` and a morphism `tw : hU^*N ⟶ ι^*B`: the morphism `k^*h^*M ⟶ B` that is the leg
of `Stacks.AlgebraicGeometry.TwistMulLeg.legIso`, then `ρ^*tw`, then the contraction
`ρ^*ι^*B ≅ (ρ ≫ ι)^*B = B`. Every scheme, module and morphism is free. -/
def legTail {W Z Y D Vv : Scheme.{u}} (k : W ⟶ Z) (h : Z ⟶ Y) (ρ : W ⟶ D)
    (hU : D ⟶ Vv) (c : Vv ⟶ Y) (ι : D ⟶ W) (e : k ≫ h = ρ ≫ hU ≫ c) (hρι : ρ ≫ ι = 𝟙 W)
    {M : Y.Modules} {N : Vv.Modules} {B : W.Modules}
    (χ : (Scheme.Modules.pullback c).obj M ≅ N)
    (tw : (Scheme.Modules.pullback hU).obj N ⟶ (Scheme.Modules.pullback ι).obj B) :
    (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback h).obj M) ⟶ B :=
  (TwistMulLeg.legIso k h ρ hU c e χ).hom ≫ (Scheme.Modules.pullback ρ).map tw ≫
    ((Scheme.Modules.pullbackComp ρ ι).app B ≪≫ (Scheme.Modules.pullbackCongr hρι).app B ≪≫
      (Scheme.Modules.pullbackId W).app B).hom

/-- **`legTail` is multiplicative** as soon as the identification and the morphism are. -/
theorem legTail_mul {W Z Y D Vv : Scheme.{u}} (k : W ⟶ Z) (h : Z ⟶ Y) (ρ : W ⟶ D)
    (hU : D ⟶ Vv) (c : Vv ⟶ Y) (ι : D ⟶ W) (e : k ≫ h = ρ ≫ hU ≫ c) (hρι : ρ ≫ ι = 𝟙 W)
    {Mm Mn Mmn : Y.Modules} {Nm Nn Nmn : Vv.Modules} {Bm Bn Bmn : W.Modules}
    (mulY : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(Y.toRingedSpace).presheaf, (Y.toRingedSpace).IsSheaf⟩).obj (Mm)).obj (Mn)) ⟶ Mmn)
    (mulV : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(Vv.toRingedSpace).presheaf, (Vv.toRingedSpace).IsSheaf⟩).obj (Nm)).obj (Nn)) ⟶ Nmn)
    (mulB : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩).obj (Bm)).obj (Bn)) ⟶ Bmn)
    (χm : (Scheme.Modules.pullback c).obj Mm ≅ Nm)
    (χn : (Scheme.Modules.pullback c).obj Mn ≅ Nn)
    (χmn : (Scheme.Modules.pullback c).obj Mmn ≅ Nmn)
    (hχ : TwistMulLeg.pbMul c mulY ≫ χmn.hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(Vv.toRingedSpace).presheaf, (Vv.toRingedSpace).IsSheaf⟩)).map
          ((χm.hom, χn.hom) : (_, _) ⟶ (_, _))) ≫ mulV)
    (twm : (Scheme.Modules.pullback hU).obj Nm ⟶ (Scheme.Modules.pullback ι).obj Bm)
    (twn : (Scheme.Modules.pullback hU).obj Nn ⟶ (Scheme.Modules.pullback ι).obj Bn)
    (twmn : (Scheme.Modules.pullback hU).obj Nmn ⟶ (Scheme.Modules.pullback ι).obj Bmn)
    (htw : TwistMulLeg.pbMul hU mulV ≫ twmn =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(D.toRingedSpace).presheaf, (D.toRingedSpace).IsSheaf⟩)).map
          ((twm, twn) : (_, _) ⟶ (_, _))) ≫ TwistMulLeg.pbMul ι mulB) :
    TwistMulLeg.pbMul k (TwistMulLeg.pbMul h mulY) ≫ legTail k h ρ hU c ι e hρι χmn twmn =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩)).map
          ((legTail k h ρ hU c ι e hρι χm twm, legTail k h ρ hU c ι e hρι χn twn) :
            (_, _) ⟶ (_, _))) ≫ mulB :=
  TwistMulLeg.mul_comp (TwistMulLeg.leg_mul k h ρ hU c e mulY mulV χm χn χmn hχ)
    (TwistMulLeg.mul_comp (TwistMulLeg.mul_pullback ρ htw)
      (TwistMulLeg.mul_comp (TwistMulLeg.mul_pullbackComp ρ ι mulB)
        (TwistMulLeg.mul_comp (TwistMulLeg.mul_pullbackCongr hρι mulB) (mul_pullbackId mulB))))

end Generic

section MidGeneric

universe w w'

variable {R₁ R₂ : Type u} {σ : Type w} {τ : Type w'}
  [CommRing R₁] [CommRing R₂] [SetLike σ R₁] [AddSubgroupClass σ R₁]
  [SetLike τ R₂] [AddSubgroupClass τ R₂]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **Tag 01MY's multiplicativity clause, in the normal form of
`Stacks.AlgebraicGeometry.TwistMulLeg`**, for an arbitrary homomorphism of graded rings: the
inverse image along `r_φ` of Tag 01MU's multiplication map, followed by the comparison map on the
`(m + n)`-th twist, is the tensor product of the comparison maps followed by the inverse image
along the inclusion of `U(φ)` of the multiplication map. -/
theorem pbMul_twistMultiplicationMap_twistMap (φ : 𝒜 →+*ᵍ ℬ) (m n : ℤ) :
    TwistMulLeg.pbMul (mapHom 𝒜 ℬ φ)
          (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap 𝒜 m n) ≫
        twistMap 𝒜 ℬ φ (m + n) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((mapDomain 𝒜 ℬ φ).toScheme.toRingedSpace).presheaf,
            ((mapDomain 𝒜 ℬ φ).toScheme.toRingedSpace).IsSheaf⟩)).map
          ((twistMap 𝒜 ℬ φ m, twistMap 𝒜 ℬ φ n) : (_, _) ⟶ (_, _))) ≫
        TwistMulLeg.pbMul (mapDomain 𝒜 ℬ φ).ι
          (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap ℬ m n) :=
  TwistMulLeg.mul_of_comparison_split_gen
    ((Stacks.PullbackTensorIso.pullbackTensorIso (mapHom 𝒜 ℬ φ).toLRSHom.toShHom).app
        (twistingSheaf 𝒜 m, twistingSheaf 𝒜 n))
    ((Stacks.PullbackTensorIso.pullbackTensorIso
      (mapDomain 𝒜 ℬ φ).ι.toLRSHom.toShHom).app (twistingSheaf ℬ m, twistingSheaf ℬ n))
    (TwistMulLeg.pbMul_eq (mapHom 𝒜 ℬ φ)
      (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap 𝒜 m n))
    (TwistMulLeg.pbMul_eq (mapDomain 𝒜 ℬ φ).ι
      (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap ℬ m n))
    (TwistMultTransport.transport_middle _ _ _ _ _ _ _
      (Iso.hom_inv_id_app
        (Stacks.PullbackTensorIso.pullbackTensorIso (mapHom 𝒜 ℬ φ).toLRSHom.toShHom)
        (twistingSheaf 𝒜 m, twistingSheaf 𝒜 n))
      (ProjMapCard.twistMap_comp_pullbackTwistMultiplication 𝒜 ℬ φ m n))

end MidGeneric

/-! ### The basis of the base, and the charts -/

section Chart

variable {S S' : Scheme.{u}} (A : SheafGradedAlgebra S) (g : S' ⟶ S)

/-- **The affine opens of `S'` carried by `g` into an affine open of `S`.** -/
def baseChangeBasis : Set S'.Opens :=
  {V | IsAffineOpen V ∧ ∃ U : S.Opens, IsAffineOpen U ∧ V ≤ g ⁻¹ᵁ U}

/-- The affine opens carried into an affine open of `S` form a basis of the topology of `S'`. -/
theorem isBasis_baseChangeBasis : Opens.IsBasis (baseChangeBasis g) := by
  refine Opens.isBasis_iff_nbhd.2 fun {W x} hx => ?_
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ := (Scheme.isBasis_affineOpens S).exists_subset_of_mem_open
    (Set.mem_univ (g.base x)) isOpen_univ
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVW⟩ := (Scheme.isBasis_affineOpens S').exists_subset_of_mem_open
    (show x ∈ ((W ⊓ g ⁻¹ᵁ U : S'.Opens) : Set S') from ⟨hx, hxU⟩) (W ⊓ g ⁻¹ᵁ U).2
  exact ⟨V, ⟨hV, U, hU, fun y hy => (hVW hy).2⟩, hxV, fun y hy => (hVW hy).1⟩

/-- Every member of `baseChangeBasis g` is an affine open of `S'`. -/
theorem isAffineOpen_of_mem_baseChangeBasis :
    ∀ V ∈ baseChangeBasis g, IsAffineOpen V := fun _ h => h.1

variable {g}

/-- A chosen affine open of `S` into which a member of the basis is carried. -/
def baseOpen (V : baseChangeBasis g) : S.AffineZariskiSite :=
  ⟨V.2.2.choose, V.2.2.choose_spec.1⟩

/-- A member `V` of the basis is contained in the inverse image under `g` of `baseOpen V`. -/
theorem le_baseOpen (V : baseChangeBasis g) : V.1 ≤ g ⁻¹ᵁ (baseOpen V).toOpens :=
  V.2.2.choose_spec.2

/-- A member of the basis, as an object of the affine Zariski site of `S'`. -/
abbrev siteOf (V : baseChangeBasis g) : S'.AffineZariskiSite := ⟨V.1, V.2.1⟩

/-- The chosen affine open of `S`, as an affine open. -/
abbrev affOf (V : baseChangeBasis g) : S.affineOpens :=
  ⟨(baseOpen V).toOpens, isAffineOpen_toOpens _⟩

variable (g)

/-- **The graded ring map of sections attached to a member of the basis**:
`Γ(U, A) ⟶ Γ(V, g^*A)` for the chosen affine open `U` of `S`. -/
abbrev chartMap (V : baseChangeBasis g) :
    A.grading (affOf V).1 →+*ᵍ (A.pullback g).grading V.1 :=
  sectionBaseChange A g (baseOpen V) (siteOf V) (le_baseOpen V)

/-- The irrelevant ideal of `Γ(V, g^*A)` is contained in the ideal generated by the image under
`chartMap A g V` of the irrelevant ideal of `Γ(U, A)`. -/
theorem irrelevant_le_map_chartMap (V : baseChangeBasis g) :
    HomogeneousIdeal.irrelevant ((A.pullback g).grading V.1) ≤
      (HomogeneousIdeal.irrelevant (A.grading (affOf V).1)).map (chartMap A g V) :=
  irrelevant_le_map_sectionBaseChange A g (baseOpen V) (siteOf V) (le_baseOpen V)

/-- The graded ring map of sections is defined everywhere on `Proj Γ(V, g^*A)`. -/
theorem mapDomain_chartMap (V : baseChangeBasis g) :
    mapDomain (A.grading (affOf V).1) ((A.pullback g).grading V.1) (chartMap A g V) = ⊤ :=
  mapDomain_eq_top_of_irrelevant_le_map _ _ _ (irrelevant_le_map_chartMap A g V)

/-- The identification of `Proj Γ(V, g^*A)` with the domain of definition of the graded ring map
of sections, which is everything. -/
def chartSection (V : baseChangeBasis g) :
    AlgebraicGeometry.Proj ((A.pullback g).grading V.1) ⟶
      (mapDomain (A.grading (affOf V).1) ((A.pullback g).grading V.1)
        (chartMap A g V)).toScheme :=
  (Scheme.topIso _).inv ≫
    ((AlgebraicGeometry.Proj ((A.pullback g).grading V.1)).isoOfEq
      (mapDomain_chartMap A g V).symm).hom

/-- `chartSection A g V` followed by the inclusion of the domain of definition is the identity
of `Proj Γ(V, g^*A)`. -/
theorem chartSection_ι (V : baseChangeBasis g) :
    chartSection A g V ≫ (mapDomain (A.grading (affOf V).1)
      ((A.pullback g).grading V.1) (chartMap A g V)).ι = 𝟙 _ :=
  Stacks.AlgebraicGeometry.RelativeProj.topIso_inv_isoOfEq_hom_ι _ _ _
    (mapDomain_chartMap A g V)

/-- `chartSection A g V` followed by the morphism `mapHom` of the graded ring map of sections is
the morphism `Proj.map (chartMap A g V)` of `Proj` schemes. -/
theorem chartSection_mapHom (V : baseChangeBasis g) :
    chartSection A g V ≫ mapHom (A.grading (affOf V).1) ((A.pullback g).grading V.1)
        (chartMap A g V) =
      AlgebraicGeometry.Proj.map (chartMap A g V) (irrelevant_le_map_chartMap A g V) :=
  (Category.assoc _ _ _).trans (Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map _ _ _
    (irrelevant_le_map_chartMap A g V) (mapDomain_chartMap A g V))

/-- **The chart over a member of the basis, followed by the base-change morphism**, factored
through the identification with the domain of definition, Tag 01MY's morphism of the graded ring
map of sections, and the chart of `Proj_S(A)`. -/
theorem chart_comp_baseChangeHom (V : baseChangeBasis g) :
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).chart V.1 V.2.1 ≫
        baseChangeHom A g =
      chartSection A g V ≫ mapHom (A.grading (affOf V).1)
          ((A.pullback g).grading V.1) (chartMap A g V) ≫
        (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).chart (affOf V).1 (affOf V).2 :=
  (chart_baseChangeHom A g (baseOpen V) (siteOf V) (le_baseOpen V)).trans
    ((congrArg (fun z => z ≫ (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).chart
      (affOf V).1 (affOf V).2) (chartSection_mapHom A g V).symm).trans (Category.assoc _ _ _))

end Chart

/-! ### The comparison on a chart -/

section Comparison

variable {S S' : Scheme.{u}} (A : SheafGradedAlgebra S) (g : S' ⟶ S)

/-- The chart over a member of the basis. -/
abbrev chartV (V : baseChangeBasis g) :=
  (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).chart V.1 V.2.1

/-- The chart of `Proj_S(A)` over the chosen affine open. -/
abbrev chartU (V : baseChangeBasis g) :=
  (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).chart (affOf V).1 (affOf V).2

/-- Tag 01NR's chart identification is multiplicative, with its type read over the chosen
affine open. -/
theorem chartTwistIso_mul_affOf (V : baseChangeBasis g) (i j : ℤ) :
    TwistMulLeg.pbMul (chartU A g V) (relativeTwistMul A i j) ≫
      (chartTwistIso A (i + j) (affOf V)).hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((AlgebraicGeometry.Proj (A.grading (affOf V).1)).toRingedSpace).presheaf,
            ((AlgebraicGeometry.Proj (A.grading (affOf V).1)).toRingedSpace).IsSheaf⟩)).map
          (((chartTwistIso A i (affOf V)).hom, (chartTwistIso A j (affOf V)).hom) :
            (_, _) ⟶ (_, _))) ≫
        Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
          (A.grading (affOf V).1) i j :=
  chartTwistIso_mul A i j (affOf V)

end Comparison

end Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist
