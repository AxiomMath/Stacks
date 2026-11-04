module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PullbackFrobeniusLocalFactor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FinitePushforwardLFunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StratificationGlue

/-!
# The L-function of a sheaf is the product of the L-functions of its restrictions to strata

Let `X` be locally of finite type and quasi-compact over a finite field `k`, `Λ` a commutative
ring and `F` a sheaf of `Λ`-modules on `X_étale` with finite projective stalks. For a
constructible stratification of `X` by immersed strata `Z_i`,

`L(X, F) = ∏_i L(Z_i, F|_{Z_i})`.

Every closed point of `X` lies on exactly one stratum, where it is a closed point with the same
residue field; the stalk of `F|_{Z_i}` there is that of `F`, compatibly with the geometric
Frobenius (`Stacks.EtaleCohomology.charSeries_frobeniusStalk_inverseImage`), so the local factors
agree.

## Main results

* `Stacks.EtaleCohomology.charSeries_closedPointFrobenius_smallEtalePullObj`: the local factor of
  an inverse image along an immersion.
* `Stacks.EtaleCohomology.EulerSystem.eulerProduct_eq_prod_of_sigmaEquiv`: an Euler product over
  a finite disjoint union of index sets is the product of the Euler products.
* `Stacks.EtaleCohomology.lFunctionOfFiniteProjectiveStalks_eq_prod_stratification`:
  `L(X, F) = ∏_i L(Z_i, F|_{Z_i})`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

/-! ### Euler products over a finite disjoint union -/

/-- The Euler product agrees with the partial product up to degree `n`: `X ^ (n + 1)` divides
their difference. -/
public theorem EulerSystem.X_pow_dvd_eulerProduct_sub_partialProduct {Λ : Type*} [CommRing Λ]
    {ι : Type*} (E : EulerSystem Λ ι) (n : ℕ) :
    (PowerSeries.X : PowerSeries Λ) ^ (n + 1) ∣ E.eulerProduct - E.partialProduct n := by
  refine PowerSeries.X_pow_dvd_iff.2 fun j hj => ?_
  rw [map_sub, E.coeff_eulerProduct, E.coeff_partialProduct_of_le (Nat.lt_succ_iff.1 hj),
    sub_self]

/-- **An Euler product over a finite disjoint union of index sets is the product of the Euler
products.** -/
public theorem EulerSystem.eulerProduct_eq_prod_of_sigmaEquiv {Λ : Type*} [CommRing Λ]
    {I : Type*} [Fintype I] {κ : I → Type*} (E : ∀ i, EulerSystem Λ (κ i)) {ι : Type*}
    (E' : EulerSystem Λ ι) (e : (Σ i, κ i) ≃ ι) (hdeg : ∀ p, E'.deg (e p) = (E p.1).deg p.2)
    (hfac : ∀ p, E'.factor (e p) = (E p.1).factor p.2) :
    E'.eulerProduct = ∏ i, (E i).eulerProduct := by
  classical
  ext n
  have hprod : PowerSeries.coeff n (∏ i, (E i).eulerProduct) =
      PowerSeries.coeff n (∏ i, (E i).partialProduct n) := by
    let J := Ideal.span {(PowerSeries.X : PowerSeries Λ) ^ (n + 1)}
    have hq : Ideal.Quotient.mk J (∏ i, (E i).eulerProduct) =
        Ideal.Quotient.mk J (∏ i, (E i).partialProduct n) := by
      rw [map_prod, map_prod]
      exact Finset.prod_congr rfl fun i _ => Ideal.Quotient.eq.2
        (Ideal.mem_span_singleton.2 ((E i).X_pow_dvd_eulerProduct_sub_partialProduct n))
    have hd := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hq)
    have := PowerSeries.X_pow_dvd_iff.1 hd n (Nat.lt_succ_self n)
    rwa [map_sub, sub_eq_zero] at this
  let t : Finset (Σ i, κ i) := Finset.univ.sigma fun i => (E i).support n
  rw [hprod, E'.coeff_eulerProduct_eq (t := t.map e.toEmbedding) ?_]
  · rw [Finset.prod_map]
    simp only [Equiv.coe_toEmbedding, hfac]
    rw [Finset.prod_sigma]
    rfl
  · intro y hy
    rw [Finset.mem_map]
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_univ _, (E _).mem_support.2 ?_⟩
    rw [← hdeg, e.apply_symm_apply]
    exact E'.mem_support.1 hy

/-! ### Immersions -/

/-- The residue field map of a preimmersion is bijective. -/
public theorem residueFieldMap_bijective_of_isPreimmersion {X X' : Scheme.{u}} (g : X' ⟶ X)
    [IsPreimmersion g] (x' : X') : Function.Bijective (g.residueFieldMap x').hom := by
  refine ⟨(g.residueFieldMap x').hom.injective, fun z => ?_⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨b, rfl⟩ := g.stalkMap_surjective x' a
  exact ⟨X.residue (g x') b, congrArg (fun φ => φ.hom b) (Scheme.residue_residueFieldMap g x')⟩

/-- The degree of a point of a scheme over a field is unchanged along a morphism inducing an
isomorphism of residue fields. -/
public theorem residueDegree_comp_of_bijective {k : Type u} [Field k] {X X' : Scheme.{u}}
    (g : X' ⟶ X) (h : X ⟶ Spec (.of k)) (x' : X')
    (hbij : Function.Bijective (g.residueFieldMap x').hom) :
    residueDegree (g ≫ h) x' = residueDegree h (g x') := by
  let : Algebra k (X.residueField (g x')) := (fieldToResidue h (g x')).hom.toAlgebra
  let : Algebra k (X'.residueField x') := (fieldToResidue (g ≫ h) x').hom.toAlgebra
  let e : X.residueField (g x') ≃ₐ[k] X'.residueField x' :=
    AlgEquiv.ofBijective
      { toRingHom := (g.residueFieldMap x').hom
        commutes' := fun c => by
          show _ = (fieldToResidue (g ≫ h) x').hom c
          rw [fieldToResidue_comp]
          rfl } hbij
  exact e.toLinearEquiv.finrank_eq.symm

section Pullback

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (q : T ⟶ S) (Λ : Type r) [CommRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{max (u + 1) r} Λ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  (F : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) r} Λ))

/-- The inverse image of the bounded site, read on Mathlib's site, is Mathlib's inverse image. -/
public def sheafEquivSmallEtalePullObjIso :
    (SmallEtale.sheafEquiv B T.obj T.property (ModuleCat.{max (u + 1) r} Λ)).functor.obj
        (smallEtalePullObj B q F) ≅
      (etaleModuleInverseImage.{u, r} Λ (fS B q)).obj
        ((SmallEtale.sheafEquiv B S.obj S.property (ModuleCat.{max (u + 1) r} Λ)).functor.obj F) :=
  ((SmallEtale.sheafEquivPullbackBaseChangeIso B q (ModuleCat.{max (u + 1) r} Λ)
    (etaleModuleInverseImageAdj.{u, r} Λ (fS B q))
    (Functor.sheafAdjunctionContinuous (AlgebraicGeometry.smallEtaleBaseChange B q)
      (ModuleCat.{max (u + 1) r} Λ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property))).app F).symm

/-- **The stalk of an inverse image is the stalk at the image geometric point.** -/
public def etaleModuleStalk_smallEtalePullObjIso (s : GeometricPoint T.obj) :
    (etaleModuleStalkFunctor.{u, max (u + 1) r, r} B T Λ s).obj (smallEtalePullObj B q F) ≅
      (etaleModuleStalkFunctor.{u, max (u + 1) r, r} B S Λ (s.map (fS B q))).obj F :=
  ((sheafEquivCompSheafFiberIso.{u, max (u + 1) r, r} B T Λ s).app
      (smallEtalePullObj B q F)).symm ≪≫
    ((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).mapIso
      (sheafEquivSmallEtalePullObjIso B q Λ F) ≪≫
    (etaleModuleStalkPullbackIso Λ (fS B q) s.hom).app _ ≪≫
    (sheafEquivCompSheafFiberIso.{u, max (u + 1) r, r} B S Λ (s.map (fS B q))).app F

/-- The stalks of an inverse image are finite when those of the sheaf are. -/
public theorem finite_etaleModuleStalk_smallEtalePullObj
    (hfin : ∀ s : GeometricPoint S.obj,
      Module.Finite Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B S Λ s).obj F))
    (s : GeometricPoint T.obj) :
    Module.Finite Λ
      ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B T Λ s).obj (smallEtalePullObj B q F)) :=
  have := hfin (s.map (fS B q))
  Module.Finite.equiv (etaleModuleStalk_smallEtalePullObjIso B q Λ F s).symm.toLinearEquiv

/-- The stalks of an inverse image are projective when those of the sheaf are. -/
public theorem projective_etaleModuleStalk_smallEtalePullObj
    (hproj : ∀ s : GeometricPoint S.obj,
      Module.Projective Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B S Λ s).obj F))
    (s : GeometricPoint T.obj) :
    Module.Projective Λ
      ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B T Λ s).obj (smallEtalePullObj B q F)) :=
  have := hproj (s.map (fS B q))
  Module.Projective.of_equiv (etaleModuleStalk_smallEtalePullObjIso B q Λ F s).symm.toLinearEquiv

/-- **The local factor of an inverse image** at a closed point whose residue field maps
isomorphically onto that of its image. -/
public theorem charSeries_closedPointFrobenius_smallEtalePullObj
    (hfin : ∀ s : GeometricPoint S.obj,
      Module.Finite Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B S Λ s).obj F))
    (hproj : ∀ s : GeometricPoint S.obj,
      Module.Projective Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B S Λ s).obj F))
    {k : Type u} [Field k] [Finite k] (gS : S.obj ⟶ Spec (.of k)) [LocallyOfFiniteType gS]
    (gT : T.obj ⟶ Spec (.of k)) [LocallyOfFiniteType gT] (t : closedPoints T.obj)
    (ht : (fS B q) t.1 ∈ closedPoints S.obj)
    (hbij : Function.Bijective ((fS B q).residueFieldMap t.1).hom) (n : ℕ) :
    haveI := finite_sheafFiber_sheafEquiv B T Λ (geometricPointAt T.obj t.1)
      (smallEtalePullObj B q F) (finite_etaleModuleStalk_smallEtalePullObj B q Λ F hfin _)
    haveI := projective_sheafFiber_sheafEquiv B T Λ (smallEtalePullObj B q F)
      (geometricPointAt T.obj t.1) (projective_etaleModuleStalk_smallEtalePullObj B q Λ F hproj _)
    haveI := finite_sheafFiber_sheafEquiv B S Λ (geometricPointAt S.obj ((fS B q) t.1))
      F (hfin _)
    haveI := projective_sheafFiber_sheafEquiv B S Λ F
      (geometricPointAt S.obj ((fS B q) t.1)) (hproj _)
    ProjectiveDeterminant.charSeries
        (closedPointFrobenius.{u, max (u + 1) r, r} B T Λ (smallEtalePullObj B q F) gT t) n =
      ProjectiveDeterminant.charSeries
        (closedPointFrobenius.{u, max (u + 1) r, r} B S Λ F gS ⟨_, ht⟩) n := by
  have := finite_sheafFiber_sheafEquiv B T Λ (geometricPointAt T.obj t.1)
    (smallEtalePullObj B q F) (finite_etaleModuleStalk_smallEtalePullObj B q Λ F hfin _)
  have := projective_sheafFiber_sheafEquiv B T Λ (smallEtalePullObj B q F)
    (geometricPointAt T.obj t.1) (projective_etaleModuleStalk_smallEtalePullObj B q Λ F hproj _)
  have := finite_sheafFiber_sheafEquiv B S Λ (geometricPointAt S.obj ((fS B q) t.1))
    F (hfin _)
  have := projective_sheafFiber_sheafEquiv B S Λ F
    (geometricPointAt S.obj ((fS B q) t.1)) (hproj _)
  have := finite_residueField gT t.1 t.2
  have := finite_residueField gS _ ht
  let φ := (Scheme.pointSmallEtale (geometricPointAt T.obj t.1).hom).sheafFiber
    (A := ModuleCat.{max (u + 1) r} Λ) |>.mapIso (sheafEquivSmallEtalePullObjIso B q Λ F)
  have : Module.Finite Λ ((Scheme.pointSmallEtale (geometricPointAt T.obj t.1).hom).sheafFiber
      (A := ModuleCat.{max (u + 1) r} Λ) |>.obj ((etaleModuleInverseImage.{u, r} Λ
        (fS B q)).obj ((SmallEtale.sheafEquiv B S.obj S.property
          (ModuleCat.{max (u + 1) r} Λ)).functor.obj F))) :=
    Module.Finite.equiv φ.toLinearEquiv
  have : Module.Projective Λ ((Scheme.pointSmallEtale (geometricPointAt T.obj t.1).hom).sheafFiber
      (A := ModuleCat.{max (u + 1) r} Λ) |>.obj ((etaleModuleInverseImage.{u, r} Λ
        (fS B q)).obj ((SmallEtale.sheafEquiv B S.obj S.property
          (ModuleCat.{max (u + 1) r} Λ)).functor.obj F))) :=
    Module.Projective.of_equiv φ.toLinearEquiv
  have hnat := frobeniusStalk_naturality (ModuleCat.{max (u + 1) r} Λ) T.obj t.1
    (sheafEquivSmallEtalePullObjIso B q Λ F).hom
  have h : closedPointFrobenius.{u, max (u + 1) r, r} B T Λ (smallEtalePullObj B q F) gT t =
      φ.toLinearEquiv.symm.conj (frobeniusStalk (ModuleCat.{max (u + 1) r} Λ) T.obj t.1
        ((etaleModuleInverseImage.{u, r} Λ (fS B q)).obj
          ((SmallEtale.sheafEquiv B S.obj S.property
            (ModuleCat.{max (u + 1) r} Λ)).functor.obj F))).hom := by
    have h' : frobeniusStalk (ModuleCat.{max (u + 1) r} Λ) T.obj t.1
        ((SmallEtale.sheafEquiv B T.obj T.property (ModuleCat.{max (u + 1) r} Λ)).functor.obj
          (smallEtalePullObj B q F)) = φ.hom ≫ frobeniusStalk (ModuleCat.{max (u + 1) r} Λ) T.obj
            t.1 _ ≫ φ.inv := by
      show _ = (Scheme.pointSmallEtale (geometricPointAt T.obj t.1).hom).sheafFiber.map
        (sheafEquivSmallEtalePullObjIso B q Λ F).hom ≫ _ ≫ φ.inv
      rw [reassoc_of% hnat]
      show _ = _ ≫ φ.hom ≫ φ.inv
      rw [φ.hom_inv_id, Category.comp_id]
    exact LinearMap.ext fun v => congrArg (fun g => g.hom v) h'
  rw [h, ProjectiveDeterminant.charSeries_conj]
  exact charSeries_frobeniusStalk_inverseImage (fS B q) t.1 Λ hbij _ n

end Pullback

/-! ### The L-function along a stratification -/

section Stratification

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{max (u + 1) r} Λ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
  (hfin : ∀ s : GeometricPoint X.obj,
    Module.Finite Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).obj F))
  (hproj : ∀ s : GeometricPoint X.obj,
    Module.Projective Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).obj F))
  {k : Type u} [Field k] [Finite k] (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  (s : ConstructibleStratification B X ⊤)

omit [Finite k] in
include f in
/-- A point of a stratum is closed exactly when its image is. -/
public theorem isClosed_singleton_stratum_iff (i : Fin s.n) (z : (s.piece i).obj) :
    IsClosed ({z} : Set (s.piece i).obj) ↔
      IsClosed ({(fS B (s.inclusion i)) z} : Set X.obj) := by
  have : IsImmersion (fS B (s.inclusion i)) := s.isImmersion i
  have : JacobsonSpace X.obj := LocallyOfFiniteType.jacobsonSpace f
  constructor
  · exact fun hz => (fS B (s.inclusion i)).closePoints_subset_preimage_closedPoints hz
  · intro hz
    have h : (fS B (s.inclusion i)) ⁻¹' {(fS B (s.inclusion i)) z} = {z} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hw => (fS B (s.inclusion i)).isEmbedding.injective hw, fun hw => hw ▸ rfl⟩
    rw [← h]
    exact hz.preimage (fS B (s.inclusion i)).continuous

/-- The closed points of `X` are the closed points of the strata. -/
public def stratificationClosedPointsEquiv :
    (Σ i : Fin s.n, closedPoints (s.piece i).obj) ≃ closedPoints X.obj :=
  Equiv.ofBijective (fun p => ⟨(fS B (s.inclusion p.1)) p.2.1,
      (isClosed_singleton_stratum_iff B X f s p.1 p.2.1).1 p.2.2⟩) (by
    constructor
    · rintro ⟨i, z⟩ ⟨j, z'⟩ h
      have h' := congrArg Subtype.val h
      dsimp only at h'
      obtain rfl : i = j := by
        by_contra hij
        exact Set.disjoint_left.1 (s.pairwise_disjoint i j hij) ⟨z.1, rfl⟩ ⟨z'.1, h'.symm⟩
      have : IsImmersion (fS B (s.inclusion i)) := s.isImmersion i
      obtain rfl : z = z' := Subtype.ext ((fS B (s.inclusion i)).isEmbedding.injective h')
      rfl
    · intro x
      have hx : x.1 ∈ ⋃ i, Set.range (B.inclusion.map (s.inclusion i)).base := by
        rw [← s.covers, TopologicalSpace.Opens.coe_top]
        trivial
      obtain ⟨i, z, hz⟩ := Set.mem_iUnion.1 hx
      have hzc : IsClosed ({z} : Set (s.piece i).obj) :=
        (isClosed_singleton_stratum_iff B X f s i z).2 (by
          rw [show (fS B (s.inclusion i)) z = x.1 from hz]
          exact x.2)
      exact ⟨⟨i, ⟨z, hzc⟩⟩, Subtype.ext hz⟩)

variable [QuasiCompact f]

omit [Finite k] in
include f in
/-- The strata of a scheme of finite type over a field are Noetherian. -/
public theorem noetherianSpace_stratum (i : Fin s.n) :
    TopologicalSpace.NoetherianSpace (s.piece i).obj := by
  have : IsLocallyNoetherian X.obj := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X.obj :=
    ⟨by simpa using QuasiCompact.isCompact_preimage (f := f) Set.univ isOpen_univ isCompact_univ⟩
  have : AlgebraicGeometry.IsNoetherian X.obj := {}
  have : IsImmersion (fS B (s.inclusion i)) := s.isImmersion i
  exact (fS B (s.inclusion i)).isEmbedding.isInducing.noetherianSpace

/-- **The L-function is the product of the L-functions of the restrictions to the strata.** For a
constructible stratification of `X`, locally of finite type and quasi-compact over a finite field,
and a sheaf `F` of modules over a commutative ring with finite projective stalks,
`L(X, F) = ∏_i L(Z_i, F|_{Z_i})`. -/
public theorem lFunctionOfFiniteProjectiveStalks_eq_prod_stratification :
    lFunctionOfFiniteProjectiveStalks.{u, max (u + 1) r, r} B X Λ F f hfin hproj =
      ∏ i : Fin s.n,
        haveI := noetherianSpace_stratum B X f s i
        haveI : IsImmersion (fS B (s.inclusion i)) := s.isImmersion i
        lFunctionOfFiniteProjectiveStalks.{u, max (u + 1) r, r} B (s.piece i) Λ
          (smallEtalePullObj B (s.inclusion i) F) (fS B (s.inclusion i) ≫ f)
          (finite_etaleModuleStalk_smallEtalePullObj B (s.inclusion i) Λ F hfin)
          (projective_etaleModuleStalk_smallEtalePullObj B (s.inclusion i) Λ F hproj) := by
  refine EulerSystem.eulerProduct_eq_prod_of_sigmaEquiv _ _
    (stratificationClosedPointsEquiv B X f s) (fun p => ?_) (fun p => ?_)
  all_goals
    have : IsImmersion (fS B (s.inclusion p.1)) := s.isImmersion p.1
    have hbij := residueFieldMap_bijective_of_isPreimmersion (fS B (s.inclusion p.1)) p.2.1
    have hdeg := residueDegree_comp_of_bijective _ f _ hbij
  · exact hdeg.symm
  · have := noetherianSpace_stratum B X f s p.1
    show PowerSeries.invOfUnit _ 1 = PowerSeries.invOfUnit _ 1
    congr 1
    rw [finiteProjectiveLocalCharSeries, finiteProjectiveLocalCharSeries, hdeg]
    exact (charSeries_closedPointFrobenius_smallEtalePullObj B (s.inclusion p.1) Λ F hfin hproj f
      (fS B (s.inclusion p.1) ≫ f) p.2 _ hbij _).symm

/-- **`L(X, F) = ∏_i L(Z_i, F|_{Z_i})` for a constructible flat sheaf** (Tag 03UV on `X`). -/
public theorem constructibleFlatLFunction_eq_prod_stratification
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
        (ModuleCat.{max (u + 1) r} Λ)]
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) :
    constructibleFlatLFunction B X Λ F f hF =
      ∏ i : Fin s.n,
        haveI := noetherianSpace_stratum B X f s i
        haveI : IsImmersion (fS B (s.inclusion i)) := s.isImmersion i
        lFunctionOfFiniteProjectiveStalks.{u, max (u + 1) r, r} B (s.piece i) Λ
          (smallEtalePullObj B (s.inclusion i) F) (fS B (s.inclusion i) ≫ f)
          (finite_etaleModuleStalk_smallEtalePullObj B (s.inclusion i) Λ F
            (finite_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF))
          (projective_etaleModuleStalk_smallEtalePullObj B (s.inclusion i) Λ F
            (projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF)) :=
  lFunctionOfFiniteProjectiveStalks_eq_prod_stratification B X Λ F _ _ f s

end Stratification

end Stacks.EtaleCohomology

end
