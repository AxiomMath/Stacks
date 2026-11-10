module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.OpenSubspaceDerivedRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineEtaleDerivedCoheratorPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.EmptyOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquareSubmodules
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestrictionNaturality

/-!
# The comparison functor is an equivalence: the dévissage of Stacks 09TG

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` contained in a
big fppf site `B`.  Suppose that for every étale morphism `g : V ⟶ X` with `V` affine, the
direct image preserves quasi-coherence and some right derived functor `Rg_*` is computed by `g_*`
on K-injective complexes of quasi-coherent modules (the square of [Stacks, Tag 09TG] commutes
for `g`).  Then the comparison functor `i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1 is an
equivalence.

## The proof

`i_X` reflects isomorphisms, so it suffices that the counit of the derived coherator adjunction
`D(ι) ⊣ RQ_X` be invertible at every `M` of `D_QCoh(𝒪_X)`
(`AlgebraicGeometry.Space.quasicoherentDerivedComparison_isEquivalence_of_isIso_counit`).  Call
such an `M` *good*.  For a quasi-compact open subspace `W ⊆ X` let `C(W)` say that every `M` of
`D_QCoh(𝒪_X)` with `M|_W = 0` is good.  `C(X)` holds trivially and `C(∅)` is the claim.  The
induction principle of Stacks 09IT, read from the empty open subspace, reduces everything to the
step: for an elementary distinguished square `(W₁ ⊆ W₂, f : V ⟶ W₂)` with `V` affine, `C(W₂)`
implies `C(W₁)`.

For the step, let `M|_{W₁} = 0` and write `k : W₂ ⟶ X`.  In the Mayer–Vietoris triangle of
Stacks 08GW on `W₂` for `M|_{W₂}`, the terms over `W₁` and over `W₁ ×_{W₂} V` vanish, so
`M|_{W₂} ≅ Rf_*(M|_V)`.  Hence `Rk_*(M|_{W₂}) ≅ Rg_*(M|_V)` for the affine étale `g = k ∘ f`,
which is good with quasi-coherent cohomology by the key step
`AlgebraicGeometry.Space.derivedQuasicoherentProperty_and_isIso_counit_derivedPushforward`.
The cone `G` of `M ⟶ Rk_*(M|_{W₂})` restricts to zero on `W₂`, `k` being an open immersion, so
`G` is good by `C(W₂)`; and good objects satisfy two-out-of-three in a distinguished triangle.

## Main results

* `AlgebraicGeometry.Space.quasicoherentDerivedComparison_isEquivalence_of_forall_affineEtale` —
  the equivalence, from the square for every affine étale `g : V ⟶ X`.

## References

* [Stacks Project, Tag 09TG](https://stacks.math.columbia.edu/tag/09TG)
* [Stacks Project, Tag 09IT](https://stacks.math.columbia.edu/tag/09IT)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.PushforwardMayerVietoris

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_isGrothendieckAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat
  hasRightDerivedFunctor_mapHomotopyCategory_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Generalities -/

/-- An exact functor isomorphic to the identity reflects vanishing in the derived category. -/
lemma isZero_of_isZero_mapDerivedCategory_obj_of_iso_id {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {F : C ⥤ C} [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (e : F ≅ 𝟭 C) (M : DerivedCategory C)
    (h : IsZero (F.mapDerivedCategory.obj M)) : IsZero M := by
  have h' : IsZero ((𝟭 C).mapDerivedCategory.obj M) :=
    h.of_iso ((Stacks.Homology.mapDerivedCategoryIsoOfIso _ _ e).symm.app M)
  refine h'.of_iso ((DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
    DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexIdIso C _).app _).symm ≪≫
    (𝟭 C).mapDerivedCategoryFactors.symm.app _ ≪≫
    (𝟭 C).mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M))

/-- If a biproduct map `A ⟶ X ⊞ Y` is invertible and `X` is zero, its second component is
invertible. -/
lemma isIso_of_isIso_biprod_lift {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
    {A X Y : C} (f : A ⟶ X) (g : A ⟶ Y) (hX : IsZero X) (hfg : IsIso (biprod.lift f g)) :
    IsIso g := by
  have : IsIso (biprod.snd : X ⊞ Y ⟶ Y) :=
    ⟨⟨biprod.inr, by
      apply biprod.hom_ext <;>
        simp only [Category.assoc, BinaryBicone.inr_fst, BinaryBicone.inr_snd, comp_zero,
          Category.comp_id, Category.id_comp]
      exact hX.eq_of_tgt _ _, by simp⟩⟩
  have h : g = biprod.lift f g ≫ biprod.snd := by simp
  rw [h]
  infer_instance

/-- On an algebraic space without points every object of the derived category vanishes: every
module has subsingleton stalks at the (non-existent) geometric points. -/
lemma isZero_derivedCategory_of_isEmpty_points (Y : AlgebraicSpaces B S hS)
    (hY : IsEmpty (points B S hS Y.1)) (N : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :
    IsZero N := by
  have hK : IsZero (DerivedCategory.Q.objPreimage N) := by
    rw [IsZero.iff_id_eq_zero]
    refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
    exact (isZero_of_stalkSet_subsingleton B S hS Y _
      (fun p => (hY.false p.image).elim)).eq_of_src _ _
  exact (DerivedCategory.Q.map_isZero hK).of_iso (DerivedCategory.Q.objObjPreimageIso N).symm

/-! ### Open subspaces -/

section OpenSubspace

variable (X : AlgebraicSpaces B S hS)

/-- The inclusion of an open subspace `W` into `X` is a monomorphism of algebraic spaces. -/
instance mono_openSubspaceHom {W : Subfunctor X.1} (hW : IsOpenSubspace B S hS W) :
    Mono (openSubspaceHom B S hS _ hW) :=
  have : Mono ((ObjectProperty.ι _).map (openSubspaceHom B S hS _ hW)) :=
    (inferInstance : Mono W.ι)
  (ObjectProperty.ι _).mono_of_mono_map this

/-- `M` vanishes on the open subspace `W`: its restriction to `W` is zero. -/
def VanishesOn {W : Subfunctor X.1} (hW : IsOpenSubspace B S hS W)
    (M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) : Prop :=
  letI := etaleModulePullback_additive.{u, u} B S hS (openSubspaceHom B S hS _ hW)
    (isEtale_openSubspaceHom B S hS _ hW)
  letI := preservesFiniteLimits_etaleModulePullback B S hS (openSubspaceHom B S hS _ hW)
    (isEtale_openSubspaceHom B S hS _ hW)
  letI := preservesFiniteColimits_etaleModulePullback B S hS (openSubspaceHom B S hS _ hW)
    (isEtale_openSubspaceHom B S hS _ hW)
  IsZero ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS _ hW)
    (isEtale_openSubspaceHom B S hS _ hW)).mapDerivedCategory.obj M)

end OpenSubspace

/-! ### Good objects -/

section Good

variable (X : AlgebraicSpaces B S hS)

/-- `M` is *good* when the counit of the derived coherator adjunction is invertible at it. -/
def IsGoodForCoherator (M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) : Prop :=
  IsIso ((spaceDerivedInclusionAdjunction B S hS X).counit.app M)

variable {X}

/-- An object isomorphic to a good object is good. -/
lemma isGoodForCoherator_of_iso {M N : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)}
    (e : M ≅ N) (h : IsGoodForCoherator B S hS X M) : IsGoodForCoherator B S hS X N :=
  (NatTrans.isIso_app_iff_of_iso _ e).1 h

/-- A zero object of the derived category is good. -/
lemma isGoodForCoherator_of_isZero {M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)}
    (h : IsZero M) : IsGoodForCoherator B S hS X M :=
  have : (spaceDerivedCoherator B S hS X).Additive :=
    (spaceDerivedInclusionAdjunction B S hS X).right_adjoint_additive
  ((spaceDerivedCoherator B S hS X ⋙
    (quasicoherentSheavesι B S hS X).mapDerivedCategory).map_isZero h).isIso h _

/-- Good objects satisfy two-out-of-three at the first vertex of a distinguished triangle: the
counit is a natural transformation of triangulated functors. -/
lemma isGoodForCoherator_of_triangle
    (T : Triangle (DerivedCategory (Modules.{u, u} B S hS X.1 X.2))) (hT : T ∈ distTriang _)
    (h₂ : IsGoodForCoherator B S hS X T.obj₂) (h₃ : IsGoodForCoherator B S hS X T.obj₃) :
    IsGoodForCoherator B S hS X T.obj₁ := by
  let adj := spaceDerivedInclusionAdjunction B S hS X
  let : (spaceDerivedCoherator B S hS X).CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let : (spaceDerivedCoherator B S hS X).IsTriangulated := adj.isTriangulated_rightAdjoint
  exact Stacks.DerivedQCoh.isIso_app₁_of_isIso_app₂₃
    (spaceDerivedCoherator B S hS X ⋙ (quasicoherentSheavesι B S hS X).mapDerivedCategory) (𝟭 _)
    adj.counit T hT h₂ h₃

/-- The objects with quasi-coherent cohomology satisfy two-out-of-three at the third vertex. -/
lemma derivedQuasicoherentProperty_of_triangle
    (T : Triangle (DerivedCategory (Modules.{u, u} B S hS X.1 X.2))) (hT : T ∈ distTriang _)
    (h₁ : derivedQuasicoherentProperty B S hS X T.obj₁)
    (h₂ : derivedQuasicoherentProperty B S hS X T.obj₂) :
    derivedQuasicoherentProperty B S hS X T.obj₃ := by
  have := quasicoherentSheaves_isWeakSerreClass_schemeUniverse B S hS X.1 X.2
  obtain ⟨N, hN, ⟨e⟩⟩ :=
    (derivedQuasicoherentProperty B S hS X).ext_of_isTriangulatedClosed₃' T hT h₁ h₂
  exact derivedCategoryB_quasicoherent_of_iso B S hS X e.symm hN

end Good

/-! ### Restrictions along composites, and the Mayer–Vietoris triangle -/

section Restriction

/-- If the restriction of `N` along `b` vanishes, so does its restriction along `a ≫ b`. -/
lemma isZero_mapDerivedCategory_etaleModulePullback_comp {T U Y : AlgebraicSpaces B S hS}
    (a : T ⟶ U) (b : U ⟶ Y) (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (hab : IsEtale B S hS (a ≫ b).hom) (N : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (h : IsZero ((etaleModulePullback.{u, u} B S hS b hb).mapDerivedCategory.obj N)) :
    IsZero ((etaleModulePullback.{u, u} B S hS (a ≫ b) hab).mapDerivedCategory.obj N) :=
  ((etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategory.map_isZero h).of_iso
    ((Stacks.Homology.mapDerivedCategoryIsoOfIso _ _
        (etaleModulePullbackCompIso B S hS a b ha hb hab).symm).app N ≪≫
      (Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS b hb)
        (etaleModulePullback.{u, u} B S hS a ha)).app N)

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **An object of `D(𝒪_W)` vanishing on the open member of an elementary distinguished square
is the derived direct image of its restriction to the étale member.**  In the Mayer–Vietoris
triangle of Stacks 08GW the terms over the open member and over the intersection vanish, the
intersection mapping to `W` through the open member. -/
theorem isIso_derivedUnitEtale_of_isZero_restrict_open
    (M : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (h : IsZero ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj M)) :
    IsIso ((derivedUnitOfNatTrans (edsAdjEtale B S hS hsq).unit
      (edsDerivedRestrictPushEtale B S hS hsq)
      (edsTotalRightDerivedUnitEtale B S hS hsq)).app M) := by
  obtain ⟨δ, hT⟩ :=
    exists_mem_distTriang_edsDerivedRestrictPushMayerVietorisLowerShriek B S hS hsq M
  have hU : IsZero ((edsDerivedRestrictPushOpen B S hS hsq).obj M) :=
    isZero_derivedRestrictPush_of_isZero B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq) _ (edsTotalRightDerivedUnitOpen B S hS hsq) inferInstance M h
  have hP : IsZero ((edsDerivedRestrictPushInter B S hS hsq).obj M) :=
    isZero_derivedRestrictPush_of_isZero B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq) _ (edsTotalRightDerivedUnitInter B S hS hsq) inferInstance M
      (isZero_mapDerivedCategory_etaleModulePullback_comp B S hS (edsFst B S hS hsq)
        (edsOpenHom B S hS hsq) (isEtale_edsFst B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq) M h)
  have h₁ := (Triangle.isZero₃_iff_isIso₁ _ hT).1 hP
  exact isIso_of_isIso_biprod_lift _ _ hU h₁

end Restriction

/-! ### The dévissage step -/

section Step

variable (X : AlgebraicSpaces B S hS)

/-- Nothing but zero vanishes on the whole space: restriction along the isomorphism
`⊤ ⟶ X` followed by restriction along its inverse is restriction along the identity. -/
lemma isZero_of_vanishesOn_top (hW : IsOpenSubspace B S hS (⊤ : Subfunctor X.1))
    (M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (h : VanishesOn B S hS X hW M) :
    IsZero M := by
  let k := openSubspaceHom B S hS _ hW
  have hk : IsEtale B S hS k.hom := isEtale_openSubspaceHom B S hS _ hW
  have : IsIso ((ObjectProperty.ι _).map k) := (inferInstance : IsIso (⊤ : Subfunctor X.1).ι)
  have : IsIso k := isIso_of_fully_faithful (ObjectProperty.ι _) k
  have : IsIso (inv k).hom := (inferInstance : IsIso ((ObjectProperty.ι _).map (inv k)))
  have hinv : IsEtale B S hS (inv k).hom := isEtale_of_isIso B S hS _
  have hid : IsEtale B S hS (𝟙 X : X ⟶ X).hom := isEtale_of_isIso B S hS _
  have hcomp : IsEtale B S hS (inv k ≫ k).hom := by rw [IsIso.inv_hom_id]; exact hid
  have h₁ := isZero_mapDerivedCategory_etaleModulePullback_comp B S hS (inv k) k hinv hk hcomp M h
  refine isZero_of_isZero_mapDerivedCategory_obj_of_iso_id (etaleModulePullbackIdIso B S hS hid) M
    (h₁.of_iso ?_)
  exact (Stacks.Homology.mapDerivedCategoryIsoOfIso _ _
    (eqToIso (etaleModulePullback_congr B S hS hcomp hid (IsIso.inv_hom_id k)))).symm.app M

/-- **The square of Stacks 09TG commutes over every affine étale chart of `X`**: for every étale
`g : V ⟶ X` with `V` affine, the direct image preserves quasi-coherence and some right derived
functor `Rg_*` is computed by `g_*` on K-injective complexes of quasi-coherent modules. -/
def AffineEtaleChartsDerivedPushforwardComputedOnKInjectives : Prop :=
  ∀ (V : AlgebraicSpaces B S hS) (g : V ⟶ X), IsEtale B S hS g.hom → IsAffineSpace B S hS V.1 →
    ∃ (_ : PushforwardPreservesQuasicoherence B S hS g)
      (Rj : DerivedCategory (Modules.{u, u} B S hS V.1 V.2) ⥤
        DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
      (βj : (modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj),
      Rj.IsRightDerivedFunctor βj
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS V.1 V.2) (ComplexShape.up ℤ)) ∧
        DerivedPushforwardComputedOnKInjectives B S hS g Rj βj

/-- `C(W)`: every object of `D_QCoh(𝒪_X)` vanishing on `W` is good. -/
def CoheratorClaim {W : Subfunctor X.1} (hW : IsOpenSubspace B S hS W) : Prop :=
  ∀ M, derivedQuasicoherentProperty B S hS X M → VanishesOn B S hS X hW M →
    IsGoodForCoherator B S hS X M

attribute [local instance] hasRightDerivedFunctor_modulePushforward

/-- **The dévissage step**: for an elementary distinguished square `(W₁ ⊆ W₂, f : V ⟶ W₂)` with
`V` affine, `C(W₂)` implies `C(W₁)`. -/
theorem coheratorClaim_step
    (hcrit : AffineEtaleChartsDerivedPushforwardComputedOnKInjectives B S hS X)
    {W₁ W₂ : Subfunctor X.1} (hW₁ : IsOpenSubspace B S hS W₁) (hW₂ : IsOpenSubspace B S hS W₂)
    (hle : W₁ ≤ W₂) {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ W₂.toFunctor)
    (hV : IsAffineSpace B S hS V)
    (hsq : IsElementaryDistinguishedSquare B S hS hW₂.1
      (Subfunctor.range (Subfunctor.homOfLe hle)) f)
    (h₂ : CoheratorClaim B S hS X hW₂) : CoheratorClaim B S hS X hW₁ := by
  intro M hM hvan
  let Y := openSubspaceSpace B S hS _ hW₂
  let k := openSubspaceHom B S hS _ hW₂
  have hk : IsEtale B S hS k.hom := isEtale_openSubspaceHom B S hS _ hW₂
  let M' := (etaleModulePullback.{u, u} B S hS k hk).mapDerivedCategory.obj M
  -- the restriction of `M` to `W₂` vanishes on the open member of the square
  let o := edsOpenHom B S hS (W := Y) hsq
  have ho : IsEtale B S hS o.hom := isEtale_edsOpenHom B S hS (W := Y) hsq
  let e₀ : (Subfunctor.range (Subfunctor.homOfLe hle)).toFunctor ⟶ W₁.toFunctor :=
    (asIso (Subfunctor.toRange (Subfunctor.homOfLe hle))).inv
  let e₁ : edsOpen B S hS (W := Y) hsq ⟶ openSubspaceSpace B S hS _ hW₁ := ObjectProperty.homMk e₀
  have : IsIso e₁.hom := (inferInstance : IsIso (asIso (Subfunctor.toRange
    (Subfunctor.homOfLe hle))).inv)
  have he₁ : IsEtale B S hS e₁.hom := isEtale_of_isIso B S hS _
  have heq : o ≫ k = e₁ ≫ openSubspaceHom B S hS _ hW₁ := by
    apply ObjectProperty.hom_ext
    change (Subfunctor.range (Subfunctor.homOfLe hle)).ι ≫ W₂.ι =
      (asIso (Subfunctor.toRange (Subfunctor.homOfLe hle))).inv ≫ W₁.ι
    rw [← (asIso (Subfunctor.toRange (Subfunctor.homOfLe hle))).cancel_iso_hom_left,
      Iso.hom_inv_id_assoc, asIso_hom, ← Category.assoc, Subfunctor.toRange_ι,
      Subfunctor.homOfLe_ι]
  have hok : IsEtale B S hS (o ≫ k).hom := isEtale_comp B S hS ho hk
  have he₁k : IsEtale B S hS (e₁ ≫ openSubspaceHom B S hS _ hW₁).hom := heq ▸ hok
  have hopen : IsZero ((etaleModulePullback.{u, u} B S hS o ho).mapDerivedCategory.obj M') :=
    (isZero_mapDerivedCategory_etaleModulePullback_comp B S hS e₁
      (openSubspaceHom B S hS _ hW₁) he₁ (isEtale_openSubspaceHom B S hS _ hW₁) he₁k M
        hvan).of_iso <|
      (Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS k hk)
        (etaleModulePullback.{u, u} B S hS o ho)).symm.app M ≪≫
      (Stacks.Homology.mapDerivedCategoryIsoOfIso _ _
        (etaleModulePullbackCompIso B S hS o k ho hk hok)).app M ≪≫
      (Stacks.Homology.mapDerivedCategoryIsoOfIso _ _
        (eqToIso (etaleModulePullback_congr B S hS hok he₁k heq))).app M
  -- by Mayer–Vietoris, `M|_{W₂}` is the derived direct image of its restriction to `V`
  have hu := isIso_derivedUnitEtale_of_isZero_restrict_open B S hS (W := Y) hsq M' hopen
  -- the derived unit `M ⟶ Rk_*(M|_{W₂})` and its cone
  let Rk := ((etaleModulePullback.{u, u} B S hS k hk ⋙
      modulePushforward B S hS k).mapHomotopyCategory
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))
  let αk := ((etaleModulePullback.{u, u} B S hS k hk ⋙
      modulePushforward B S hS k).mapHomotopyCategory
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))
  let uX := derivedUnitOfNatTrans (etaleModulePullbackAdjunction B S hS k hk).unit Rk αk
  obtain ⟨G, g₂, δ, hT⟩ := distinguished_cocone_triangle (uX.app M)
  have hGvan : VanishesOn B S hS X hW₂ G :=
    Triangle.isZero₃_of_isIso₁ _
      ((etaleModulePullback.{u, u} B S hS k hk).mapDerivedCategory.map_distinguished _ hT)
      (isIso_mapDerivedCategory_map_derivedUnitOfNatTrans_of_mono B S hS k hk Rk αk M)
  -- the key step at the affine étale chart `V ⟶ W₂ ⟶ X`
  let f' := edsEtaleHom B S hS (W := Y) hsq
  have hf' : IsEtale B S hS f'.hom := isEtale_edsEtaleHom B S hS (W := Y) hsq
  have hg : IsEtale B S hS (f' ≫ k).hom := isEtale_comp B S hS hf' hk
  obtain ⟨hpush, Rj, βj, hRj, H⟩ := hcrit (edsEtale B S hS (W := Y) hsq) (f' ≫ k) hg hV
  obtain ⟨hPj, hGj⟩ := derivedQuasicoherentProperty_and_isIso_counit_derivedPushforward B S hS
    (f' ≫ k) hg hV hpush Rj βj H _
    (derivedQuasicoherent_etaleModulePullback B S hS (f' ≫ k) hg M hM)
  -- `Rk_*(M|_{W₂}) ≅ Rj_*(M|_V)`
  let Rk' := ((modulePushforward B S hS k).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))
  let βk' := ((modulePushforward B S hS k).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))
  let Rf' := ((modulePushforward B S hS f').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS (edsEtale B S hS (W := Y) hsq).1
        (edsEtale B S hS (W := Y) hsq).2) (ComplexShape.up ℤ))
  let βf' := ((modulePushforward B S hS f').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS (edsEtale B S hS (W := Y) hsq).1
        (edsEtale B S hS (W := Y) hsq).2) (ComplexShape.up ℤ))
  have := isRightDerivedFunctor_restrictThenPushUnit B S hS k hk Rk' βk'
  have := isRightDerivedFunctor_restrictThenPushUnit B S hS f' hf' Rf' βf'
  have := isRightDerivedFunctor_pushThenPushUnit B S hS f' hf' k Rf' βf' Rk' βk'
  let e₁' : Rk ≅ (etaleModulePullback.{u, u} B S hS k hk).mapDerivedCategory ⋙ Rk' :=
    Functor.rightDerivedUnique _ _ αk (restrictThenPushUnit B S hS k hk Rk' βk')
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))
  let e₂' : edsDerivedRestrictPushEtale B S hS (W := Y) hsq ≅
      (etaleModulePullback.{u, u} B S hS f' hf').mapDerivedCategory ⋙ Rf' :=
    Functor.rightDerivedUnique _ _ (edsTotalRightDerivedUnitEtale B S hS (W := Y) hsq)
      (restrictThenPushUnit B S hS f' hf' Rf' βf')
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))
  let e₃' : Rf' ⋙ Rk' ≅ Rj :=
    Functor.rightDerivedNatIso _ _ (pushThenPushUnit B S hS f' k Rf' βf' Rk' βk') βj
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      (Functor.isoWhiskerRight (Stacks.Homology.mapHomotopyCategoryIso
        (modulePushforwardCompIso B S hS f' k) (ComplexShape.up ℤ)) DerivedCategory.Qh)
  let e₄' : (etaleModulePullback.{u, u} B S hS f' hf').mapDerivedCategory.obj M' ≅
      (etaleModulePullback.{u, u} B S hS (f' ≫ k) hg).mapDerivedCategory.obj M :=
    (Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS k hk)
        (etaleModulePullback.{u, u} B S hS f' hf')).symm.app M ≪≫
      (Stacks.Homology.mapDerivedCategoryIsoOfIso _ _
        (etaleModulePullbackCompIso B S hS f' k hf' hk hg)).app M
  let eR : Rk.obj M ≅
      Rj.obj ((etaleModulePullback.{u, u} B S hS (f' ≫ k) hg).mapDerivedCategory.obj M) :=
    e₁'.app M ≪≫ Rk'.mapIso (asIso ((derivedUnitOfNatTrans (edsAdjEtale B S hS (W := Y) hsq).unit
      (edsDerivedRestrictPushEtale B S hS (W := Y) hsq)
      (edsTotalRightDerivedUnitEtale B S hS (W := Y) hsq)).app M')) ≪≫
      Rk'.mapIso (e₂'.app M') ≪≫ e₃'.app _ ≪≫ Rj.mapIso e₄'
  -- conclude by two-out-of-three
  have hP₂ : derivedQuasicoherentProperty B S hS X (Rk.obj M) :=
    derivedCategoryB_quasicoherent_of_iso B S hS X eR.symm hPj
  exact isGoodForCoherator_of_triangle B S hS _ hT (isGoodForCoherator_of_iso B S hS eR.symm hGj)
    (h₂ G (derivedQuasicoherentProperty_of_triangle B S hS _ hT hM hP₂) hGvan)

end Step

/-! ### The induction -/

section Induction

variable (X : AlgebraicSpaces B S hS)

/-- `C(X)`: an object vanishing on the whole space is zero, hence good. -/
lemma coheratorClaim_top (hW : IsOpenSubspace B S hS (⊤ : Subfunctor X.1)) :
    CoheratorClaim B S hS X hW := fun M _ h =>
  isGoodForCoherator_of_isZero B S hS (isZero_of_vanishesOn_top B S hS X hW M h)

/-- **`C(∅)`: every object of `D_QCoh(𝒪_X)` is good**, by the induction principle of Stacks 09IT
started at the empty open subspace, the dévissage step propagating `C` downwards. -/
theorem coheratorClaim_sheafify_bot (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hcrit : AffineEtaleChartsDerivedPushforwardComputedOnKInjectives B S hS X) :
    CoheratorClaim B S hS X (isOpenSubspace_sheafify_bot B S hS X.1 X.2) := by
  have hW₀ := isOpenSubspace_sheafify_bot B S hS X.1 X.2
  have hW₀qc : IsQuasiCompactSpace B S hS
      ((⊥ : Subfunctor X.1).sheafify (BigFppfOver.topology B S hS)).toFunctor := by
    let := pointTopology B S hS
      ((⊥ : Subfunctor X.1).sheafify (BigFppfOver.topology B S hS)).toFunctor
    have := isEmpty_points_sheafify_bot B S hS X.1
    exact (isQuasiCompactSpace_iff_compactSpace_points B S hS _ hW₀.1).2 inferInstance
  have key := qcqs_induction_on_enlargement B S hS hZ X hXqc hXqs _ hW₀ hW₀qc
    (fun D => ∀ hD : IsOpenSubspace B S hS D, CoheratorClaim B S hS X hD →
      CoheratorClaim B S hS X hW₀)
    (fun _ h => h)
    (fun W₁ W₂ hW₁ hW₂ _ _ hle _ _ f hV hsq hP _ h₂ =>
      hP hW₁ (coheratorClaim_step B S hS X hcrit hW₁ hW₂ hle f hV hsq h₂))
  exact key (isOpenSubspace_top X.2) (coheratorClaim_top B S hS X _)

/-- Every object of `D(𝒪_X)` vanishes on the empty open subspace. -/
lemma vanishesOn_sheafify_bot (M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    VanishesOn B S hS X (isOpenSubspace_sheafify_bot B S hS X.1 X.2) M :=
  isZero_derivedCategory_of_isEmpty_points B S hS _ (isEmpty_points_sheafify_bot B S hS X.1) _

/-- **The comparison functor `i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` is an equivalence** for a
quasi-compact and quasi-separated algebraic space `X` such that, for every étale `g : V ⟶ X`
with `V` affine, the direct image preserves quasi-coherence and some right derived functor
`Rg_*` is computed by `g_*` on K-injective complexes of quasi-coherent modules. -/
theorem quasicoherentDerivedComparison_isEquivalence_of_forall_affineEtale
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hcrit : AffineEtaleChartsDerivedPushforwardComputedOnKInjectives B S hS X) :
    (quasicoherentDerivedComparison B S hS X.1 X.2).IsEquivalence :=
  quasicoherentDerivedComparison_isEquivalence_of_isIso_counit B S hS X fun M hM =>
    coheratorClaim_sheafify_bot B S hS X hZ hXqc hXqs hcrit M hM
      (vanishesOn_sheafify_bot B S hS X M)

end Induction

end AlgebraicGeometry.Space

end
