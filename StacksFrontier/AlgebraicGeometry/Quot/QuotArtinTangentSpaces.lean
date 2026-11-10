module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinTangentNat
public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinTangentHom
public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinOpenness
public import StacksFrontier.Deformation.Artin.FiniteDimensional.NaturalLinearBound
public import StacksFrontier.Deformation.Artin.FiniteDimensional.TangentTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfPostInclusion

/-!
# Axiom [3] for the Quot functor: finite-dimensional tangent spaces

Let `D` be the situation of Remark 0CZW, with `F` of finite presentation and flat over `S`, and
let `x₀` be a point of `Quot_{F/X/S}` over a field `k`, a quotient `F_k ⟶ F_k/𝒦₀` with support
proper over `k`. A lift of `x₀` over `k[V]` is a quotient of `F_{k[V]}` flat over `k[V]`
restricting to `F_k/𝒦₀`; its difference with the trivial lift `x₀ ⊗ k[V]`
(`Deformation.ModuleDeformation.CopowerQuotientLift.difference`) is a morphism
`𝒦₀ ⟶ (F_k/𝒦₀) ⊗ V`. This assignment is natural in `V` and injective, so the tangent space of
`Quot_{F/X/S}` at `x₀` embeds `k`-linearly into `Hom(𝒦₀, F_k/𝒦₀)`, which is finite-dimensional
because `𝒦₀` is coherent and `F_k/𝒦₀` is coherent with support proper over `k`
(`AlgebraicGeometry.Space.finiteDimensional_hom_of_hasProperSupport`).

## Main results

* `AlgebraicGeometry.Space.hasFiniteDimensionalTangentSpaces_quotOverBase`:
  **Stacks 0CZW, axiom [3]**.

## References

* [Stacks Project, Tag 0CZW](https://stacks.math.columbia.edu/tag/0CZW)
* [Stacks Project, Tag 0CZV](https://stacks.math.columbia.edu/tag/0CZV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation Deformation.Artin

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels
attribute [-instance] CategoryTheory.IsGrothendieckAbelian.hasExt
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS)
  (ι : ∀ T : BigFppfOver B S hS, (schemeSpaceFunctor B S hS).obj T ⟶ D.Y)
  [hY : ∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)]
  (M : QuotSitePresheafModel D)

/-! ### Quotients named by sections of a model -/

/-- The quotient named by a section of a model of the Quot presheaf. -/
def kerOf {A : BigFppfOver B S hS} (z : M.presheaf.obj (op A)) :
    D.properlySupportedQuotients (D.testOver ι A) :=
  (D.ofQuot_surjective ι A (M.iso.hom.app (op A) ⟨z⟩)).choose

/-- The point of `Quot` given by the quotient named by `z` is the image of `z` under the model
isomorphism. -/
theorem ofQuot_kerOf {A : BigFppfOver B S hS} (z : M.presheaf.obj (op A)) :
    D.ofQuot ι A (D.kerOf ι M z) = M.iso.hom.app (op A) ⟨z⟩ :=
  (D.ofQuot_surjective ι A (M.iso.hom.app (op A) ⟨z⟩)).choose_spec

/-- Two sections naming the same quotient are equal. -/
theorem kerOf_injective {A : BigFppfOver B S hS} {z w : M.presheaf.obj (op A)}
    (h : (D.kerOf ι M z).1 = (D.kerOf ι M w).1) : z = w := by
  apply M.iso_hom_app_injective (op A)
  change M.iso.hom.app (op A) ⟨z⟩ = M.iso.hom.app (op A) ⟨w⟩
  rw [← D.ofQuot_kerOf ι M z, ← D.ofQuot_kerOf ι M w, Subtype.ext h]

include hY in
/-- **The quotient named by a restriction is the pullback.** -/
theorem kerOf_map {A A' : BigFppfOver B S hS} (g : A' ⟶ A) (z : M.presheaf.obj (op A)) :
    (D.kerOf ι M (M.presheaf.map g.op z)).1 =
      D.quotientPullback (D.testHom ι g) (D.kerOf ι M z).1 := by
  have h1 := D.ofQuot_kerOf ι M (M.presheaf.map g.op z)
  rw [M.iso_hom_app_map g z, ← D.ofQuot_kerOf ι M z] at h1
  have h2 := D.baseChange_ofQuot ι g (D.kerOf ι M z)
  exact congrArg Subtype.val (D.ofQuot_injective ι A' (h1.trans h2))

variable {k : Type u} [Field k] (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))
  (hF : IsFlatOver B S hS D.X.2 D.f.hom D.F)
  (z₀ : M.presheaf.obj (op (algebraOver k B S hS toS hk)))

/-! ### The lift attached to a section over `k[V]` -/

/-- The kernel `𝒦₀` of the quotient of `F_k` named by `z₀`. -/
def ker₀ : Subobject (D.baseChangeModule (D.sq₀ ι toS hk)) := (D.kerOf ι M z₀).1

/-- The quotient `F_k/𝒦₀` named by `z₀` is a properly supported quotient. -/
theorem ker₀_mem : D.ker₀ ι M toS hk z₀ ∈ D.properlySupportedQuotients (D.sq₀ ι toS hk) :=
  (D.kerOf ι M z₀).2

/-- The kernel of the quotient of `F_{k[V]}` named by a section over `k[V]`. -/
def kerAt (V : FGModuleCat.{u} k) (z : M.presheaf.obj (op (sqObj hS toS hk V))) :
    Subobject (D.baseChangeModule (D.sqT ι toS hk V)) := (D.kerOf ι M z).1

/-- The quotient of `F_{k[V]}` named by a section over `k[V]` is a properly supported
quotient. -/
theorem kerAt_mem (V : FGModuleCat.{u} k) (z : M.presheaf.obj (op (sqObj hS toS hk V))) :
    D.kerAt ι M toS hk V z ∈ D.properlySupportedQuotients (D.sqT ι toS hk V) :=
  (D.kerOf ι M z).2

/-- Two sections over `k[V]` with the same kernel are equal. -/
theorem kerAt_injective (V : FGModuleCat.{u} k) {z w : M.presheaf.obj (op (sqObj hS toS hk V))}
    (h : D.kerAt ι M toS hk V z = D.kerAt ι M toS hk V w) : z = w :=
  D.kerOf_injective ι M h

include hY in
/-- For a section over `k[V]` restricting to `z₀`, the pullback of its kernel along
`Spec k ⟶ Spec k[V]` is `𝒦₀`. -/
theorem kerAt_sqArrow (V : FGModuleCat.{u} k) (z : M.presheaf.obj (op (sqObj hS toS hk V)))
    (hz : M.presheaf.map (sqArrow hS toS hk V).op z = z₀) :
    D.quotientPullback (D.sqβ ι toS hk V) (D.kerAt ι M toS hk V z) = D.ker₀ ι M toS hk z₀ :=
  (D.kerOf_map ι M (sqArrow hS toS hk V) z).symm.trans (congrArg (fun w => (D.kerOf ι M w).1) hz)

include hY in
/-- For `f : V ⟶ W`, the pullback of the kernel named by `z` along the map induced by
`k[V] ⟶ k[W]` is the kernel named by the restriction of `z`. -/
theorem kerAt_sqMap {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (z : M.presheaf.obj (op (sqObj hS toS hk V))) :
    D.quotientPullback (D.sqσ ι toS hk f) (D.kerAt ι M toS hk V z) =
      D.kerAt ι M toS hk W (M.presheaf.map (sqMap hS toS hk f).op z) :=
  (D.kerOf_map ι M (sqMap hS toS hk f) z).symm

/-- The lift of `F_k ⟶ F_k/𝒦₀` attached to a section over `k[V]` restricting to `z₀`. -/
abbrev elemLift (V : FGModuleCat.{u} k) (z : M.presheaf.obj (op (sqObj hS toS hk V)))
    (hz : M.presheaf.map (sqArrow hS toS hk V).op z = z₀) :
    letI := D.sqLinear ι toS hk
    ModuleDeformation.CopowerQuotientLift (D.qProj (D.sq₀ ι toS hk) (D.ker₀ ι M toS hk z₀))
      (D.sqBaseExtension ι toS hk hF V) :=
  D.sqLift ι toS hk hF (D.ker₀ ι M toS hk z₀) V (D.kerAt ι M toS hk V z)
    (D.kerAt_mem ι M toS hk V z).1.1 (D.kerAt_sqArrow ι M toS hk z₀ V z hz)

/-- The trivial lift of `z₀` over `k[V]`. -/
abbrev trivElem (V : FGModuleCat.{u} k) : M.presheaf.obj (op (sqObj hS toS hk V)) :=
  M.presheaf.map (sqRetraction hS toS hk V).op z₀

omit hY in
/-- The trivial lift of `z₀` over `k[V]` restricts to `z₀`. -/
theorem trivElem_sqArrow (V : FGModuleCat.{u} k) :
    M.presheaf.map (sqArrow hS toS hk V).op (D.trivElem M toS hk z₀ V) = z₀ := by
  rw [trivElem, ← Functor.map_comp_apply, ← op_comp, sqArrow_sqRetraction, op_id,
    Functor.map_id_apply]

omit hY in
/-- For `f : V ⟶ W`, the restriction of the trivial lift over `k[V]` along `k[V] ⟶ k[W]` is the
trivial lift over `k[W]`. -/
theorem trivElem_sqMap {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    M.presheaf.map (sqMap hS toS hk f).op (D.trivElem M toS hk z₀ V) =
      D.trivElem M toS hk z₀ W := by
  rw [trivElem, trivElem, ← Functor.map_comp_apply, ← op_comp, sqMap_sqRetraction]

omit hY in
/-- For `f : V ⟶ W`, a section over `k[V]` restricting to `z₀` has restriction along
`k[V] ⟶ k[W]` again restricting to `z₀`. -/
theorem sqMap_sqArrow_apply {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (z : M.presheaf.obj (op (sqObj hS toS hk V)))
    (hz : M.presheaf.map (sqArrow hS toS hk V).op z = z₀) :
    M.presheaf.map (sqArrow hS toS hk W).op (M.presheaf.map (sqMap hS toS hk f).op z) = z₀ := by
  rw [← Functor.map_comp_apply, ← op_comp, sqArrow_sqMap, hz]

/-- The underlying module of `𝒦₀`. -/
abbrev kerMod₀ : Modules.{u, u} B S hS (D.space (D.sq₀ ι toS hk)).1 (D.space (D.sq₀ ι toS hk)).2 :=
  Subobject.underlying.obj (D.ker₀ ι M toS hk z₀)

/-- The quotient `F_k/𝒦₀`. -/
abbrev quotMod₀ : Modules.{u, u} B S hS (D.space (D.sq₀ ι toS hk)).1 (D.space (D.sq₀ ι toS hk)).2 :=
  D.quotientModule (D.sq₀ ι toS hk) (D.ker₀ ι M toS hk z₀)

/-- **The class of a section over `k[V]` restricting to `z₀`**: the difference of its lift with
the trivial lift, a morphism `𝒦₀ ⟶ (F_k/𝒦₀) ⊗ V`. -/
def sqClass (V : FGModuleCat.{u} k) (z : M.presheaf.obj (op (sqObj hS toS hk V)))
    (hz : M.presheaf.map (sqArrow hS toS hk V).op z = z₀) :
    letI := D.sqLinear ι toS hk
    D.kerMod₀ ι M toS hk z₀ ⟶ ModuleDeformation.copowerObj (D.quotMod₀ ι M toS hk z₀) V :=
  letI := D.sqLinear ι toS hk
  ModuleDeformation.CopowerQuotientLift.difference
    (D.kArrow_qProj (T := D.sq₀ ι toS hk) (D.ker₀ ι M toS hk z₀))
    (D.exact_kArrow_qProj (T := D.sq₀ ι toS hk) (D.ker₀ ι M toS hk z₀))
    (D.elemLift ι M toS hk hF z₀ V (D.trivElem M toS hk z₀ V) (D.trivElem_sqArrow M toS hk z₀ V))
    (D.elemLift ι M toS hk hF z₀ V z hz)

include hY in
/-- **Naturality of the class in the coefficient space.** -/
theorem sqClass_map {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (z : M.presheaf.obj (op (sqObj hS toS hk V)))
    (hz : M.presheaf.map (sqArrow hS toS hk V).op z = z₀) :
    letI := D.sqLinear ι toS hk
    D.sqClass ι M toS hk hF z₀ W (M.presheaf.map (sqMap hS toS hk f).op z)
        (D.sqMap_sqArrow_apply M toS hk z₀ f z hz) =
      D.sqClass ι M toS hk hF z₀ V z hz ≫ ModuleDeformation.copowerMap _ f := by
  let := D.sqLinear ι toS hk
  have et : D.quotientPullback (D.sqσ ι toS hk f)
      (D.kerAt ι M toS hk V (D.trivElem M toS hk z₀ V)) =
        D.kerAt ι M toS hk W (D.trivElem M toS hk z₀ W) :=
    (D.kerAt_sqMap ι M toS hk f _).trans
      (congrArg (D.kerAt ι M toS hk W) (D.trivElem_sqMap M toS hk z₀ f))
  have ex := D.kerAt_sqMap ι M toS hk f z
  exact ModuleDeformation.CopowerQuotientLift.difference_naturality
    (A := D.sqBaseExtension ι toS hk hF V) (B := D.sqBaseExtension ι toS hk hF W) _ _ f
    (D.sqTransfer ι toS hk f) (D.sqTransfer_p ι toS hk hF f)
    (D.elemLift ι M toS hk hF z₀ V (D.trivElem M toS hk z₀ V) (D.trivElem_sqArrow M toS hk z₀ V))
    (D.elemLift ι M toS hk hF z₀ V z hz)
    (D.elemLift ι M toS hk hF z₀ W (D.trivElem M toS hk z₀ W) (D.trivElem_sqArrow M toS hk z₀ W))
    (D.elemLift ι M toS hk hF z₀ W _ (D.sqMap_sqArrow_apply M toS hk z₀ f z hz))
    (D.sqTransferQ ι toS hk f _ _ et) (D.sqG_comp_sqTransferQ ι toS hk f _ _ et)
    (D.sqTransferQ ι toS hk f _ _ ex) (D.sqG_comp_sqTransferQ ι toS hk f _ _ ex)
    (fun v => D.sqμ_comp_sqTransferQ ι toS hk f _ _ _ ex (D.kerAt_mem ι M toS hk V z).1.1
      (D.kerAt_mem ι M toS hk W _).1.1 _ _ v)

include hY in
/-- If two sections over `k[V]` restricting to `z₀` have the same class, the kernel named by the
first is contained in the kernel named by the second. -/
theorem kerAt_le_of_sqClass_eq (V : FGModuleCat.{u} k)
    {z w : M.presheaf.obj (op (sqObj hS toS hk V))}
    (hz : M.presheaf.map (sqArrow hS toS hk V).op z = z₀)
    (hw : M.presheaf.map (sqArrow hS toS hk V).op w = z₀)
    (h : D.sqClass ι M toS hk hF z₀ V z hz = D.sqClass ι M toS hk hF z₀ V w hw) :
    D.kerAt ι M toS hk V z ≤ D.kerAt ι M toS hk V w := by
  let := D.sqLinear ι toS hk
  let R := retractionPushforward B S hS (D.relativeMap (D.sqπ ι toS hk V)) (D.sqRep ι toS hk V)
  let qz := D.qProj (D.sqT ι toS hk V) (D.kerAt ι M toS hk V z)
  let qw := D.qProj (D.sqT ι toS hk V) (D.kerAt ι M toS hk V w)
  have hqc : (kernel qz).IsQuasicoherentOnSite :=
    ObjectProperty.prop_kernel (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _) qz
      (D.isQuasicoherentOnSite_baseChangeModule _) (D.kerAt_mem ι M toS hk V z).1.1.1
  have hφ : R.map (kernel.ι qz) ≫ (D.elemLift ι M toS hk hF z₀ V z hz).g = 0 := by
    change R.map (kernel.ι qz) ≫ R.map qz = 0
    rw [← Functor.map_comp, kernel.condition, Functor.map_zero]
  have h0 := ModuleDeformation.CopowerQuotientLift.comp_g_eq_zero_of_difference_eq _ _ _ _ _ h
    (R.map (kernel.ι qz)) hφ
  have h0' : R.map (kernel.ι qz ≫ qw) = R.map 0 :=
    (Functor.map_comp R _ _).trans (h0.trans (Functor.map_zero R _ _).symm)
  have hr : IsAffineHom B S hS (D.relativeMap (D.sqπ ι toS hk V)).hom :=
    D.morphismCoherentSituation.isAffineHom_relativeMap (D.sqπ ι toS hk V)
  have h1 : kernel.ι qz ≫ qw = 0 :=
    retractionPushforward_map_injective B S hS _ _ hr hqc h0'
  refine D.le_of_kArrow_qProj _ _ ?_
  have h2 := kernel.lift_ι qz (D.kArrow _) (D.kArrow_qProj _)
  exact (congrArg (· ≫ qw) h2.symm).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) h1).trans comp_zero))

include hY in
/-- **The class determines the section.** -/
theorem eq_of_sqClass_eq (V : FGModuleCat.{u} k)
    {z w : M.presheaf.obj (op (sqObj hS toS hk V))}
    (hz : M.presheaf.map (sqArrow hS toS hk V).op z = z₀)
    (hw : M.presheaf.map (sqArrow hS toS hk V).op w = z₀)
    (h : D.sqClass ι M toS hk hF z₀ V z hz = D.sqClass ι M toS hk hF z₀ V w hw) : z = w :=
  D.kerAt_injective ι M toS hk V (le_antisymm (D.kerAt_le_of_sqClass_eq ι M toS hk hF z₀ V hz hw h)
    (D.kerAt_le_of_sqClass_eq ι M toS hk hF z₀ V hw hz h.symm))

/-- Equal sections over `k[V]` restricting to `z₀` have equal classes. -/
theorem sqClass_congr (V : FGModuleCat.{u} k) {z w : M.presheaf.obj (op (sqObj hS toS hk V))}
    (e : z = w) (hz : M.presheaf.map (sqArrow hS toS hk V).op z = z₀)
    (hw : M.presheaf.map (sqArrow hS toS hk V).op w = z₀) :
    D.sqClass ι M toS hk hF z₀ V z hz = D.sqClass ι M toS hk hF z₀ V w hw := by
  subst e
  rfl

/-! ### Finite-dimensionality -/

variable (hFfp : D.F.IsFinitePresentationOnSite)

include hFfp in
/-- For `F` of finite presentation, `𝒦₀` and `F_k/𝒦₀` are coherent. -/
theorem isCoherent_kerMod₀_and_quotMod₀ :
    IsCoherent B S hS (D.space (D.sq₀ ι toS hk)).1 (D.space (D.sq₀ ι toS hk)).2
        (D.kerMod₀ ι M toS hk z₀) ∧
      IsCoherent B S hS (D.space (D.sq₀ ι toS hk)).1 (D.space (D.sq₀ ι toS hk)).2
        (D.quotMod₀ ι M toS hk z₀) := by
  have : Fact (HasEtaleLocalProperty B S hS (D.space (D.sq₀ ι toS hk)).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_toScheme_eq (D.space (D.sq₀ ι toS hk))
      (D.projection (D.sq₀ ι toS hk)) (D.isLocallyOfFiniteType_projection _)
      (D.toScheme_sq₀ ι toS hk)⟩
  have hF₀ : IsCoherent B S hS (D.space (D.sq₀ ι toS hk)).1 (D.space (D.sq₀ ι toS hk)).2
      (D.baseChangeModule (D.sq₀ ι toS hk)) :=
    (isCoherent_iff_isFinitePresentationOnSite B S hS _ _ _).2
      (isFinitePresentationOnSite_modulePullback B S hS (D.sourceProjection _) D.F hFfp)
  have hQ₀ : IsCoherent B S hS (D.space (D.sq₀ ι toS hk)).1 (D.space (D.sq₀ ι toS hk)).2
      (D.quotMod₀ ι M toS hk z₀) :=
    (isCoherent_iff_isFinitePresentationOnSite B S hS _ _ _).2 (D.ker₀_mem ι M toS hk z₀).1.2
  refine ⟨?_, hQ₀⟩
  have hK := isCoherent_kernel B S hS _ _ hF₀ hQ₀
    (D.quotientProjection (D.sq₀ ι toS hk) (D.ker₀ ι M toS hk z₀))
  exact isCoherent_of_iso B S hS _ ((kernelSubobjectIso _).symm ≪≫
    Subobject.isoOfEq _ _ (kernelSubobject_cokernel_π (D.ker₀ ι M toS hk z₀))) hK

include hFfp in
/-- **`Hom(𝒦₀, F_k/𝒦₀)` is finite-dimensional.** -/
theorem finiteDimensional_hom₀ :
    letI := D.sqLinear ι toS hk
    FiniteDimensional k (D.kerMod₀ ι M toS hk z₀ ⟶ D.quotMod₀ ι M toS hk z₀) :=
  finiteDimensional_hom_of_hasProperSupport_of_toScheme_eq (D.space (D.sq₀ ι toS hk))
    (D.projection (D.sq₀ ι toS hk)) (D.isLocallyOfFiniteType_projection _)
    (D.toScheme_sq₀ ι toS hk) (D.sqScalars₀ ι toS hk) (fun _ => rfl) _ _
    (D.isCoherent_kerMod₀_and_quotMod₀ ι M toS hk z₀ hFfp).1
    (D.isCoherent_kerMod₀_and_quotMod₀ ι M toS hk z₀ hFfp).2 (D.ker₀_mem ι M toS hk z₀).2

/-- The `Ext` groups of the modules of `X_k`. -/
abbrev sqHasExt : HasExt.{u + 1} (Modules.{u, u} B S hS (D.space (D.sq₀ ι toS hk)).1
    (D.space (D.sq₀ ι toS hk)).2) :=
  HasExt.standard _

/-- **The functor `V ↦ Hom(𝒦₀, (F_k/𝒦₀) ⊗ V)`**, as `Ext⁰`. -/
abbrev tangentBound : FGModuleCat.{u} k ⥤ ModuleCat.{u + 1} k :=
  letI := D.sqLinear ι toS hk
  letI := D.sqHasExt ι toS hk
  ModuleDeformation.extCoefficientFunctor (D.kerMod₀ ι M toS hk z₀)
    (ModuleDeformation.copowerFunctor (k := k) (D.quotMod₀ ι M toS hk z₀)) 0

/-- The functor `V ↦ Hom(𝒦₀, (F_k/𝒦₀) ⊗ V)` is additive. -/
instance : (D.tangentBound ι M toS hk z₀).Additive := by
  let := D.sqLinear ι toS hk
  let := D.sqHasExt ι toS hk
  infer_instance

/-- The functor `V ↦ Hom(𝒦₀, (F_k/𝒦₀) ⊗ V)` is `k`-linear. -/
instance : (D.tangentBound ι M toS hk z₀).Linear k := by
  let := D.sqLinear ι toS hk
  let := D.sqHasExt ι toS hk
  infer_instance

include hFfp in
/-- For `F` of finite presentation, `Hom(𝒦₀, (F_k/𝒦₀) ⊗ k)` is finite-dimensional over `k`. -/
theorem finiteDimensional_tangentBound :
    FiniteDimensional k ((D.tangentBound ι M toS hk z₀).obj (FGModuleCat.of k k)) := by
  let := D.sqLinear ι toS hk
  let := D.sqHasExt ι toS hk
  have := D.finiteDimensional_hom₀ ι M toS hk z₀ hFfp
  have : FiniteDimensional k (Abelian.Ext (D.kerMod₀ ι M toS hk z₀)
      (D.quotMod₀ ι M toS hk z₀) 0) :=
    Module.Finite.equiv (Abelian.Ext.linearEquiv₀ (R := k)).symm
  exact ModuleDeformation.finiteDimensional_ext_copowerObj _ _ _ 0

/-! ### Lift classes -/

/-- `k[V]` as an augmented ring of the site, with the section `Spec k ⟶ Spec k[V]`. -/
def sqAugRing (V : FGModuleCat.{u} k) : AugmentedSiteRing k B S hS toS hk where
  ring := squareZeroRing k ((fgSiteModule B hk).obj V).obj
  contains := ((fgSiteModule B hk).obj V).property
  structureMap := (squareZeroOver k B S hS toS ((fgSiteModule B hk).obj V)).hom
  aug := (squareZeroProjection k ((fgSiteModule B hk).obj V).obj).hom
  arrow := squareZeroArrow k B S hS toS hk ((fgSiteModule B hk).obj V)
  arrow_eq := rfl

variable (x : (Stack.fibredCategory B S hS M.presheaf).val.obj)
  (hx : (Stack.fibredCategory B S hS M.presheaf).val.p.obj x = algebraOver k B S hS toS hk)

/-- The section over `k[V]` named by a lift class of `x`. -/
abbrev liftSec (V : FGModuleCat.{u} k)
    (a : squareZeroLiftClasses k B S hS toS hk (Stack.fibredCategory B S hS M.presheaf).val.p x hx
      ((fgSiteModule B hk).obj V)) :
    M.presheaf.obj (op (sqObj hS toS hk V)) :=
  liftElem x hx (sqAugRing toS hk V) a

omit hY in
/-- The section named by a lift class of `x` restricts to the section of `x`. -/
theorem liftSec_sqArrow (V : FGModuleCat.{u} k)
    (a : squareZeroLiftClasses k B S hS toS hk (Stack.fibredCategory B S hS M.presheaf).val.p x hx
      ((fgSiteModule B hk).obj V)) :
    M.presheaf.map (sqArrow hS toS hk V).op (D.liftSec M toS hk x hx V a) =
      Stack.presheafFiberElement B S hS M.presheaf ⟨x, hx⟩ :=
  map_arrow_liftElem x hx (sqAugRing toS hk V) a

omit hY in
/-- Distinct lift classes of `x` over `k[V]` name distinct sections. -/
theorem liftSec_injective (V : FGModuleCat.{u} k) :
    Function.Injective (D.liftSec M toS hk x hx V) :=
  liftElem_injective x hx (sqAugRing toS hk V)

omit hY in
/-- If the lift class `b` over `k[W]` is the pullback of `a` over `k[V]` along `f : V ⟶ W`, the
section named by `b` is the restriction of the section named by `a`. -/
theorem liftSec_of_isPullback {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (a : squareZeroLiftClasses k B S hS toS hk (Stack.fibredCategory B S hS M.presheaf).val.p x hx
      ((fgSiteModule B hk).obj V))
    (b : squareZeroLiftClasses k B S hS toS hk (Stack.fibredCategory B S hS M.presheaf).val.p x hx
      ((fgSiteModule B hk).obj W))
    (h : IsPullbackOfSquareZeroLift k B S hS toS hk (Stack.fibredCategory B S hS M.presheaf).val.p
      x hx ((fgSiteModule B hk).map f) a b) :
    D.liftSec M toS hk x hx W b =
      M.presheaf.map (sqMap hS toS hk f).op (D.liftSec M toS hk x hx V a) := by
  obtain ⟨a', b', rfl, rfl, φ, hφ, -⟩ := h
  exact (Stack.presheafFiberElement_map B S hS M.presheaf (sqMap hS toS hk f)
    ⟨b'.1.right, underFiber_right_obj _ hx _ b'⟩ ⟨a'.1.right, underFiber_right_obj _ hx _ a'⟩ φ
    hφ.toIsHomLift).symm

/-- **The class of a lift class**, in `Hom(𝒦₀, (F_k/𝒦₀) ⊗ V)`. -/
def liftClassBound (V : FGModuleCat.{u} k)
    (a : squareZeroLiftClasses k B S hS toS hk (Stack.fibredCategory B S hS M.presheaf).val.p x hx
      ((fgSiteModule B hk).obj V)) :
    (D.tangentBound ι M toS hk (Stack.presheafFiberElement B S hS M.presheaf ⟨x, hx⟩)).obj V :=
  letI := D.sqLinear ι toS hk
  letI := D.sqHasExt ι toS hk
  Abelian.Ext.mk₀ (D.sqClass ι M toS hk hF _ V (D.liftSec M toS hk x hx V a)
    (D.liftSec_sqArrow M toS hk x hx V a))

include hY in
/-- The class of a lift class is natural in the coefficient space: if `b` is the pullback of `a`
along `f : V ⟶ W`, the class of `b` is the image of the class of `a` under `f`. -/
theorem liftClassBound_natural {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (a : squareZeroLiftClasses k B S hS toS hk (Stack.fibredCategory B S hS M.presheaf).val.p x hx
      ((fgSiteModule B hk).obj V))
    (b : squareZeroLiftClasses k B S hS toS hk (Stack.fibredCategory B S hS M.presheaf).val.p x hx
      ((fgSiteModule B hk).obj W))
    (h : IsPullbackOfSquareZeroLift k B S hS toS hk (Stack.fibredCategory B S hS M.presheaf).val.p
      x hx ((fgSiteModule B hk).map f) a b) :
    D.liftClassBound ι M toS hk hF x hx W b =
      (D.tangentBound ι M toS hk (Stack.presheafFiberElement B S hS M.presheaf ⟨x, hx⟩)).map f
        (D.liftClassBound ι M toS hk hF x hx V a) := by
  let := D.sqLinear ι toS hk
  let := D.sqHasExt ι toS hk
  rw [liftClassBound, liftClassBound, ModuleDeformation.extCoefficientFunctor_map_apply]
  exact (congrArg Abelian.Ext.mk₀ ((D.sqClass_congr ι M toS hk hF _ W
    (D.liftSec_of_isPullback M toS hk x hx f a b h) _ _).trans
      (D.sqClass_map ι M toS hk hF _ f _ (D.liftSec_sqArrow M toS hk x hx V a)))).trans
    (Abelian.Ext.mk₀_comp_mk₀ _ _).symm

include hY in
/-- A lift class of `x` over `k[V]` is determined by its class in `Hom(𝒦₀, (F_k/𝒦₀) ⊗ V)`. -/
theorem liftClassBound_injective (V : FGModuleCat.{u} k) :
    Function.Injective (D.liftClassBound ι M toS hk hF x hx V) := by
  let := D.sqLinear ι toS hk
  let := D.sqHasExt ι toS hk
  intro a b h
  have h' := (Abelian.Ext.mk₀_bijective _ _).1 h
  exact D.liftSec_injective M toS hk x hx V (D.eq_of_sqClass_eq ι M toS hk hF _ V _ _ h')

include ι hY in
/-- **Axiom [3] for a model of the Quot presheaf over a base with a unique point over every
scheme of the site**, for `F` of finite presentation and flat over the base, granted (RS*). -/
theorem hasFiniteDimensionalTangentSpaces_of_model
    (hF : IsFlatOver B S hS D.X.2 D.f.hom D.F) (hFfp : D.F.IsFinitePresentationOnSite)
    (hRS : SatisfiesRSStar B S hS (Stack.fibredCategory B S hS M.presheaf).val.p
      (Stack.fibredCategory B S hS M.presheaf).isFiberedInGroupoids) :
    Stack.HasFiniteDimensionalTangentSpaces B S hS (Stack.fibredCategory B S hS M.presheaf) := by
  intro k _ i₀ x₀ hx₀ _ _ s _ Λ _ _ _ iΛ _ hbase
  dsimp only
  intro hD
  have hx : ((Stack.fibredCategory B S hS M.presheaf).val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
    hx₀.trans (congrArg Over.mk hbase.symm)
  have hk : B.Contains (Spec (.of k)) := by
    have hb : B.inclusion.obj ((Stack.fibredCategory B S hS M.presheaf).val.p.obj x₀).left =
        Spec (.of k) := congrArg Comma.left hx₀
    exact hb ▸ ((Stack.fibredCategory B S hS M.presheaf).val.p.obj x₀).left.property
  have hx' : (Stack.fibredCategory B S hS M.presheaf).val.p.obj x₀ =
      algebraOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) hk :=
    BigFppfOver.obj_injective_post_inclusion B S hS hx
  have := D.finiteDimensional_tangentBound ι M _ hk
    (Stack.presheafFiberElement B S hS M.presheaf ⟨x₀, hx'⟩) hFfp
  refine (finiteDimensional_artinianTangentSpace_iff_tangentModuleAt hD).mpr ?_
  exact finiteDimensional_tangentModuleAt_of_natural_injective (hp :=
    (Stack.fibredCategory B S hS M.presheaf).isFiberedInGroupoids) (hRS := hRS) (hx₀ := hx)
    (hx' := hx') (G := D.tangentBound ι M _ hk
      (Stack.presheafFiberElement B S hS M.presheaf ⟨x₀, hx'⟩))
    (θ := D.liftClassBound ι M _ hk hF x₀ hx')
    (hθ := fun f a b h => D.liftClassBound_natural ι M _ hk hF x₀ hx' f a b h)
    (hinj := D.liftClassBound_injective ι M _ hk hF x₀ hx' _) (hD := hD)

end QuotSituation

section OverBase

variable (X : AlgebraicSpaces B S hS) (f : X ⟶ schemeSpace (BigFppfOver.terminalObj B S hS))
  (hf : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
  (hF : F.IsQuasicoherentOnSite)

/-- **Stacks 0CZW, axiom [3].** In the situation of the remark, with `F` of finite presentation
and flat over `S`, the tangent spaces of `Quot_{F/X/S}` at the points over fields of finite type
over `S` are finite-dimensional, for their canonical vector space structure.

A lift over `k[V]` of a point `F_k ⟶ F_k/𝒦₀` is a quotient of `F_{k[V]}` flat over `k[V]`; its
difference with the trivial lift is a morphism `𝒦₀ ⟶ (F_k/𝒦₀) ⊗ V`, natural in `V` and
determining the lift, so the tangent space embeds `k`-linearly into `Hom(𝒦₀, F_k/𝒦₀)`
(the deformation theory of quotients of Stacks 0CZV). That space is finite-dimensional because
`𝒦₀` is coherent and `F_k/𝒦₀` is coherent with support proper over `k` (Stacks 0D0T). -/
@[stacks 0CZW "axiom [3]: the tangent spaces of Quot_{F/X/S} at finite type points are finite \
dimensional"]
theorem hasFiniteDimensionalTangentSpaces_quotOverBase (hFfp : F.IsFinitePresentationOnSite)
    (hflat : IsFlatOver B S hS X.2 f.hom F) :
    Stack.HasFiniteDimensionalTangentSpaces B S hS
      (Stack.fibredCategory B S hS (quotOverBasePresheaf X f hf F hF)) :=
  (quotOverBase X f hf F hF).hasFiniteDimensionalTangentSpaces_of_model
    (fun T => ObjectProperty.homMk (yoneda.map (Over.homMk T.hom (by simp))))
    (quotOverBase X f hf F hF).quotSitePresheafModel hflat hFfp
    (satisfiesRSStar_quotOverBase X f hf F hF)

end OverBase

end AlgebraicGeometry.Space

end
