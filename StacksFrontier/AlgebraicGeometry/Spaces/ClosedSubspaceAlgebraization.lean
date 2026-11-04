module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFibreSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceStructureQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealLattice
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.GrothendieckExistenceSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealQuotientAdicSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistenceSpaces

/-!
# Algebraization of closed subspaces over a complete Noetherian ring

Let `A` be a Noetherian ring complete with respect to an ideal `I`, and `W` an algebraic space
separated and of finite type over `Spec A`, with adic fibres `W_n`. Let `Γ_n ⊆ W_n` be closed
subspaces with `Γ_n = Γ_{n+1} ∩ W_n`, and `Γ_0` proper over `Spec A`. Then there is a closed
subspace `Z ⊆ W`, proper over `Spec A`, with `Z ∩ W_n = Γ_n` for every `n`: Stacks 08BG.

The proof is the source's. The ideals `𝒥_n` of the `Γ_n` satisfy `𝒥_n = 𝒥_{n+1} + I^{n+1} 𝒪_W`,
so the quotients `𝒪_W / 𝒥_n` form a coherent `I 𝒪_W`-adic system with support proper over
`Spec A`; Grothendieck's existence theorem, Stacks 08BE, algebraizes it to a coherent `𝒢`, and
full faithfulness of completion, Stacks 08B9, lifts the projections `𝒪_W ⟶ 𝒪_W / 𝒥_n` to a map
`𝒪_W ⟶ 𝒢`, surjective because its completion is. Its kernel cuts out `Z`.

## Main results

* `AlgebraicGeometry.Space.exists_closedSubspace_inf_adicFibreSubspace_eq`: Stacks 08BG.

## References

* [Stacks Project, Tag 08BG](https://stacks.math.columbia.edu/tag/08BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of A))) (hSn : ∀ n, B.Contains (adicThickening A I n))

/-- **The quotient of `𝒪_W` by the ideal of a closed subspace proper over the base has support
proper over the base.** -/
theorem hasProperSupport_cokernel_definingIdealSheaf_of_isAlgebraicSpace
    (W : AlgebraicSpaces B (Spec (.of A)) hS)
    {Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B _ hS Y)
    (f : W.1 ⟶ Y) (hf : IsLocallyOfFiniteType B _ hS f) (Z : ClosedSubspaces B _ hS W.1)
    (hZ : IsProper B _ hS (Z.1.ι ≫ f)) :
    HasProperSupport B _ hS W.2 hY f hf ((SheafOfModules.toSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B _ hS W.1 W.2).O)).obj
        (cokernel (definingIdealSheaf B _ hS W Z).ι)) := by
  have hcl := isClosed_range_pointsMap_of_isClosedImmersion B _ hS W.2 Z.1.ι Z.2.2
  exact (congrArg (fun T => ∃ hT : IsClosed T, IsProperOver B _ hS W.2 hY f hf T hT)
    (supportOfSheaf_cokernel_definingIdealSheaf B _ hS W Z)).mpr
    ⟨hcl, (isProper_reducedClosedSubspace_iff_exists B _ hS W.2 hY f hf _ hcl).2
      ⟨Z.1, Z.2, rfl, hZ⟩⟩

/-- **A closed subspace whose structure sheaf has support proper over the base is proper over
the base**: the support is the point set of the subspace, and Stacks 0CZC. -/
theorem isProper_of_hasProperSupport_cokernel_definingIdealSheaf
    (W : AlgebraicSpaces B (Spec (.of A)) hS)
    {Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B _ hS Y)
    (f : W.1 ⟶ Y) (hf : IsLocallyOfFiniteType B _ hS f) (Z : ClosedSubspaces B _ hS W.1)
    (hZ : HasProperSupport B _ hS W.2 hY f hf ((SheafOfModules.toSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B _ hS W.1 W.2).O)).obj
        (cokernel (definingIdealSheaf B _ hS W Z).ι))) :
    IsProper B _ hS (Z.1.ι ≫ f) := by
  obtain ⟨hcl', hp⟩ := (congrArg (fun T => ∃ hT : IsClosed T, IsProperOver B _ hS W.2 hY f hf T hT)
    (supportOfSheaf_cokernel_definingIdealSheaf B _ hS W Z)).mp hZ
  exact (exists_isProper_closedSubspace_iff_forall B _ hS W.2 hY f hf _ hcl').1
    ((isProper_reducedClosedSubspace_iff_exists B _ hS W.2 hY f hf _ hcl').1 hp) Z.1 Z.2 rfl

/-- A sheaf submodule `P ≤ Q` dies in the quotient by `Q`. -/
private theorem submodule_ι_comp_cokernel_π_eq_zero_of_le
    (W : AlgebraicSpaces B (Spec (.of A)) hS)
    {M : Modules.{u, u} B _ hS W.1 W.2} {P Q : M.Submodule} (h : P ≤ Q) :
    P.ι ≫ cokernel.π Q.ι = 0 := by
  ext U x
  exact (cokernel_π_app_eq_zero_iff B _ hS W.1 W.2 Q U x.1).2 (h U x.2)

/-- A factorisation `a ≫ b = c` of sheaf maps sends sections killed by `a` to sections killed
by `c`. -/
private theorem app_eq_zero_of_comp_eq
    (W : AlgebraicSpaces B (Spec (.of A)) hS)
    {M N P : Modules.{u, u} B _ hS W.1 W.2} {a : M ⟶ N} {b : N ⟶ P} {c : M ⟶ P}
    (h : a ≫ b = c) (U) (x) (hx : a.val.app U x = 0) : c.val.app U x = 0 := by
  rw [← h]
  show b.val.app U (a.val.app U x) = 0
  rw [hx, map_zero]

/-- The projections `𝒪_W / 𝓘^{n+1} ⟶ 𝒪_W / 𝒥_n` commute with the transition maps. -/
private theorem idealPowerQuotientMapOfLE_comp_cokernel_desc
    (W : AlgebraicSpaces B (Spec (.of A)) hS)
    (𝓘 : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B _ hS W.1 W.2).O)).Submodule)
    (𝒥 : ℕ → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B _ hS W.1 W.2).O)).Submodule) (h𝒥 : ∀ n, 𝒥 (n + 1) ≤ 𝒥 n)
    (hk : ∀ n, (idealPowerMultiple B _ hS W.1 W.2 𝓘 (n + 1) (SheafOfModules.unit _)).ι ≫
      cokernel.π (𝒥 n).ι = 0) (n : ℕ) :
    idealPowerQuotientMapOfLE B _ hS W.1 W.2 𝓘 (Nat.add_le_add_right (Nat.le_add_right n 1) 1)
        (SheafOfModules.unit _) ≫ cokernel.desc _ (cokernel.π (𝒥 n).ι) (hk n) =
      cokernel.desc _ (cokernel.π (𝒥 (n + 1)).ι) (hk (n + 1)) ≫
        (structureQuotientTower 𝒥 h𝒥).map (homOfLE (Nat.le_add_right n 1)).op := by
  refine (cancel_epi (cokernel.π (idealPowerMultiple B _ hS W.1 W.2 𝓘 (n + 1 + 1)
    (SheafOfModules.unit _)).ι)).1 ?_
  rw [structureQuotientTower_map_succ, ← Category.assoc, π_comp_idealPowerQuotientMapOfLE,
    cokernel.π_desc]
  have h : cokernel.π (idealPowerMultiple B _ hS W.1 W.2 𝓘 (n + 1 + 1)
      (SheafOfModules.unit _)).ι ≫ cokernel.desc _ (cokernel.π (𝒥 (n + 1)).ι) (hk (n + 1)) ≫
        structureQuotientTowerTransition 𝒥 h𝒥 n = cokernel.π (𝒥 n).ι := by
    rw [cokernel.π_desc_assoc, π_structureQuotientTowerTransition]
  exact h.symm

/-- **Grothendieck existence for a tower of quotients of `𝒪_W`.** In the situation of Stacks 08BG
the system `(𝒪_W / 𝒥_n)_n` is the completion of a coherent `𝒢` with support proper over `Spec A`,
through a map `φ : 𝒪_W ⟶ 𝒢` reducing modulo `I^{n+1}` to the projection onto `𝒪_W / 𝒥_n`. -/
theorem exists_completion_iso_idealQuotient [IsNoetherianRing A] [IsAdicComplete I A]
    (W : AlgebraicSpaces B (Spec (.of A)) hS) (f : W ⟶ schemeSpace (baseObject A B hS))
    (hft : IsFiniteType B _ hS f.hom) (hsep : IsSeparated B _ hS f.hom)
    (𝒥 : ℕ → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B _ hS W.1 W.2).O)).Submodule)
    (hq : ∀ n, (𝒥 n).toSheafOfModules.IsQuasicoherentOnSite)
    (h𝒥 : ∀ n, 𝒥 n = 𝒥 (n + 1) ⊔ C1573.baseIdealSubmodule W.1 W.2 (I ^ (n + 1)))
    (hE0 : HasProperSupport B _ hS W.2 (schemeSpace (baseObject A B hS)).2 f.hom hft.1
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B _ hS W.1 W.2).O)).obj (cokernel (𝒥 0).ι))) :
    ∃ (𝒢 : CoherentModulesProperOver B _ hS W.2 (schemeSpace (baseObject A B hS)).2 f.hom hft.1)
      (φ : SheafOfModules.unit _ ⟶ 𝒢.obj.obj), ∀ n,
        ∃ e : idealPowerQuotient B _ hS W.1 W.2 (C1573.baseIdealSubmodule W.1 W.2 I) (n + 1)
            𝒢.obj.obj ≅ cokernel (𝒥 n).ι,
          φ ≫ cokernel.π (idealPowerMultiple B _ hS W.1 W.2 (C1573.baseIdealSubmodule W.1 W.2 I)
            (n + 1) 𝒢.obj.obj).ι ≫ e.hom = cokernel.π (𝒥 n).ι := by
  have := C1573.fact_isLocallyNoetherian_of_baseObject W f hft.1
  let 𝓘 := C1573.baseIdealSubmodule W.1 W.2 I
  let hI := C1573.isQuasicoherentOnSite_baseIdealSubmodule (X := W.1) (hX := W.2) I
  let E : CoherentAdicSystemsProperOver B _ hS W.2 (schemeSpace (baseObject A B hS)).2 f.hom
      hft.1 𝓘 := ⟨⟨_, isCoherentAdicSystem_structureQuotientTower I 𝒥 hq h𝒥⟩, hE0⟩
  -- Stacks 08BE
  have := isEquivalence_completionFunctorProperOver I W f hft hsep
  let Φ := completionFunctorProperOver B (Spec (.of A)) hS W.1
    (schemeSpace (baseObject A B hS)).1 W.2 (schemeSpace (baseObject A B hS)).2 f.hom hft.1 𝓘 hI
  let G := Φ.objPreimage E
  let α : Φ.obj G ≅ E := Φ.objObjPreimageIso E
  -- the projections `𝒪_W / I^{n+1} ⟶ 𝒪_W / 𝒥_n`
  have hk : ∀ n, (idealPowerMultiple B _ hS W.1 W.2 𝓘 (n + 1)
      (SheafOfModules.unit _)).ι ≫ cokernel.π (𝒥 n).ι = 0 := fun n =>
    submodule_ι_comp_cokernel_π_eq_zero_of_le A B hS W (by
      rw [idealPowerMultiple_baseIdealSubmodule, h𝒥 n]
      exact le_sup_right)
  let O' : CoherentModules B _ hS W.1 W.2 :=
    ⟨SheafOfModules.unit _, isCoherent_structureSheaf B _ hS W.1 W.2⟩
  let C := completionFunctor B _ hS W.1 W.2 𝓘 hI
  let ρ : C.obj O' ⟶ E.obj := ObjectProperty.homMk (NatTrans.ofOpSequence
    (fun n => cokernel.desc _ (cokernel.π (𝒥 n).ι) (hk n))
    (idealPowerQuotientMapOfLE_comp_cokernel_desc A B hS W 𝓘 𝒥
      (fun n => (h𝒥 n).symm ▸ le_sup_left) hk))
  -- Stacks 08B9 lifts `ρ` composed with the inverse of `α` to `φ : 𝒪_W ⟶ 𝒢`
  have := isFiniteTypeOnSite_of_isCoherentOnSite B _ hS W O'.obj
  have := isFiniteTypeOnSite_of_isCoherentOnSite B _ hS W G.obj.obj
  obtain ⟨hGcl, hGp⟩ := G.property
  have hcl := (isClosed_supportOfSheaf_of_isFiniteTypeOnSite B _ hS W.1 W.2 O'.obj).inter hGcl
  obtain ⟨φ, hφ⟩ := (bijective_completionFunctor_map_of_isProperOver W I f hft.1 O' G.obj hcl
    (isProperOver_of_subset B _ hS W.2 _ f.hom hft.1 _ _ hcl hGcl Set.inter_subset_right hGp)).2
      (ρ ≫ α.inv.hom)
  let ainv : ∀ n, cokernel (𝒥 n).ι ⟶ idealPowerQuotient B _ hS W.1 W.2 𝓘 (n + 1) G.obj.obj :=
    fun n => α.inv.hom.hom.app (op n)
  let ahom : ∀ n, idealPowerQuotient B _ hS W.1 W.2 𝓘 (n + 1) G.obj.obj ⟶ cokernel (𝒥 n).ι :=
    fun n => α.hom.hom.hom.app (op n)
  have hah : ∀ n, ainv n ≫ ahom n = 𝟙 _ := fun n =>
    congrArg (fun k => k.hom.hom.app (op n)) α.inv_hom_id
  have hmap : ∀ n, idealPowerQuotientMapOfHom B _ hS W.1 W.2 𝓘 (n + 1) φ.hom =
      cokernel.desc _ (cokernel.π (𝒥 n).ι) (hk n) ≫ ainv n :=
    fun n => congrArg (fun k => k.hom.app (op n)) hφ
  -- `φ` reduces modulo `I^{n+1}` to the projection onto `𝒪_W / 𝒥_n`
  have hKR : ∀ n, φ.hom ≫ cokernel.π (idealPowerMultiple B _ hS W.1 W.2 𝓘 (n + 1) G.obj.obj).ι ≫
      ahom n = cokernel.π (𝒥 n).ι := fun n => by
    rw [← Category.assoc, ← π_comp_idealPowerQuotientMapOfHom, hmap, cokernel.π_desc_assoc,
      Category.assoc, hah, Category.comp_id]
  exact ⟨G, φ.hom, fun n => ⟨⟨ahom n, ainv n,
    congrArg (fun k => k.hom.hom.app (op n)) α.hom_inv_id, hah n⟩, hKR n⟩⟩

/-- **The lift of the projections is surjective.** A map `φ : 𝒪_W ⟶ 𝒢` to a coherent module
with support proper over `Spec A` whose reductions modulo the `I^{n+1}` are, up to isomorphism,
the projections onto the `𝒪_W / 𝒥_n` is an epimorphism: the completion of its cokernel vanishes,
and completion is faithful (Stacks 08B9). -/
theorem epi_of_reduction_iso_idealQuotient [IsNoetherianRing A] [IsAdicComplete I A]
    (W : AlgebraicSpaces B (Spec (.of A)) hS) (f : W ⟶ schemeSpace (baseObject A B hS))
    (hft : IsFiniteType B _ hS f.hom)
    (𝒥 : ℕ → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B _ hS W.1 W.2).O)).Submodule)
    (𝒢 : CoherentModulesProperOver B _ hS W.2 (schemeSpace (baseObject A B hS)).2 f.hom hft.1)
    (φ : SheafOfModules.unit _ ⟶ 𝒢.obj.obj)
    (hφ : ∀ n, ∃ e : idealPowerQuotient B _ hS W.1 W.2 (C1573.baseIdealSubmodule W.1 W.2 I) (n + 1)
        𝒢.obj.obj ≅ cokernel (𝒥 n).ι,
      φ ≫ cokernel.π (idealPowerMultiple B _ hS W.1 W.2 (C1573.baseIdealSubmodule W.1 W.2 I) (n + 1)
        𝒢.obj.obj).ι ≫ e.hom = cokernel.π (𝒥 n).ι) :
    Epi φ := by
  have := C1573.fact_isLocallyNoetherian_of_baseObject W f hft.1
  let 𝓘 := C1573.baseIdealSubmodule W.1 W.2 I
  let hI := C1573.isQuasicoherentOnSite_baseIdealSubmodule (X := W.1) (hX := W.2) I
  let O' : CoherentModules B _ hS W.1 W.2 :=
    ⟨SheafOfModules.unit _, isCoherent_structureSheaf B _ hS W.1 W.2⟩
  let Q : CoherentModules B _ hS W.1 W.2 :=
    ⟨cokernel φ, isCoherent_cokernel B _ hS W.1 W.2 O'.property 𝒢.obj.property φ⟩
  let c : 𝒢.obj ⟶ Q := ObjectProperty.homMk (cokernel.π φ)
  let z : 𝒢.obj ⟶ Q := ObjectProperty.homMk 0
  obtain ⟨hGcl, hGp⟩ := 𝒢.property
  have : SheafOfModules.IsCoherentOnSite Q.obj := Q.property.toIsCoherentOnSite
  have := isFiniteTypeOnSite_of_isCoherentOnSite B _ hS W Q.obj
  have hcl' := hGcl.inter (isClosed_supportOfSheaf_of_isFiniteTypeOnSite B _ hS W.1 W.2 Q.obj)
  have hb' := bijective_completionFunctor_map_of_isProperOver W I f hft.1 𝒢.obj Q hcl'
    (isProperOver_of_subset B _ hS W.2 _ f.hom hft.1 _ _ hcl' hGcl Set.inter_subset_left hGp)
  have hcz : c = z := hb'.1 (by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
    obtain ⟨e, he⟩ := hφ n.unop
    have hepi : Epi (idealPowerQuotientMapOfHom B _ hS W.1 W.2 𝓘 (n.unop + 1) φ) := by
      have h1 : φ ≫ cokernel.π (idealPowerMultiple B _ hS W.1 W.2 𝓘 (n.unop + 1)
          𝒢.obj.obj).ι = cokernel.π (𝒥 n.unop).ι ≫ e.inv := by
        rw [← he, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      have h2 : cokernel.π (idealPowerMultiple B _ hS W.1 W.2 𝓘 (n.unop + 1)
          (SheafOfModules.unit _)).ι ≫ idealPowerQuotientMapOfHom B _ hS W.1 W.2 𝓘
            (n.unop + 1) φ = cokernel.π (𝒥 n.unop).ι ≫ e.inv := by
        rw [π_comp_idealPowerQuotientMapOfHom, h1]
      exact epi_of_epi_fac h2
    refine (cancel_epi (idealPowerQuotientMapOfHom B _ hS W.1 W.2 𝓘 (n.unop + 1) φ)).1 ?_
    show _ ≫ idealPowerQuotientMapOfHom B _ hS W.1 W.2 𝓘 (n.unop + 1) (cokernel.π φ) =
      _ ≫ idealPowerQuotientMapOfHom B _ hS W.1 W.2 𝓘 (n.unop + 1) 0
    rw [← idealPowerQuotientMapOfHom_comp, ← idealPowerQuotientMapOfHom_comp,
      cokernel.condition, comp_zero])
  exact Abelian.epi_of_cokernel_π_eq_zero φ (congrArg (fun k => k.hom) hcz)

/-- **The kernel of the lift lies in every `𝒥_n`.** -/
theorem ker_le_of_reduction_iso_idealQuotient
    (W : AlgebraicSpaces B (Spec (.of A)) hS)
    (J : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B _ hS W.1 W.2).O)).Submodule)
    {𝒢 : Modules.{u, u} B _ hS W.1 W.2} (φ : SheafOfModules.unit _ ⟶ 𝒢) (n : ℕ)
    (e : idealPowerQuotient B _ hS W.1 W.2 (C1573.baseIdealSubmodule W.1 W.2 I) (n + 1) 𝒢 ≅
      cokernel J.ι)
    (he : φ ≫ cokernel.π (idealPowerMultiple B _ hS W.1 W.2 (C1573.baseIdealSubmodule W.1 W.2 I)
      (n + 1) 𝒢).ι ≫ e.hom = cokernel.π J.ι) :
    SheafOfModules.Submodule.ker φ ≤ J := by
  intro U x hx
  exact (cokernel_π_app_eq_zero_iff B _ hS W.1 W.2 J U x).1
    (app_eq_zero_of_comp_eq A B hS W he U x
      ((SheafOfModules.Submodule.mem_ker φ U x).1 hx))

/-- **`𝒥_n ⊆ 𝒦 + I^{n+1} 𝒪_W` for the kernel `𝒦` of the lift.** The projection of `𝒪_W` onto
`𝒪_W / (𝒦 + I^{n+1} 𝒪_W)` factors through `φ`, hence through `𝒢 / I^{n+1} 𝒢 ≅ 𝒪_W / 𝒥_n`. -/
theorem le_ker_sup_of_reduction_iso_idealQuotient
    (W : AlgebraicSpaces B (Spec (.of A)) hS)
    (J : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B _ hS W.1 W.2).O)).Submodule)
    {𝒢 : Modules.{u, u} B _ hS W.1 W.2} (φ : SheafOfModules.unit _ ⟶ 𝒢) [Epi φ] (n : ℕ)
    (e : idealPowerQuotient B _ hS W.1 W.2 (C1573.baseIdealSubmodule W.1 W.2 I) (n + 1) 𝒢 ≅
      cokernel J.ι)
    (he : φ ≫ cokernel.π (idealPowerMultiple B _ hS W.1 W.2 (C1573.baseIdealSubmodule W.1 W.2 I)
      (n + 1) 𝒢).ι ≫ e.hom = cokernel.π J.ι) :
    J ≤ SheafOfModules.Submodule.ker φ ⊔ C1573.baseIdealSubmodule W.1 W.2 (I ^ (n + 1)) := by
  set K := SheafOfModules.Submodule.ker φ ⊔ C1573.baseIdealSubmodule W.1 W.2 (I ^ (n + 1))
  have hc := Abelian.epiIsCokernelOfKernel _ (SheafOfModules.Submodule.isLimitKernelFork φ)
  have h0 : (SheafOfModules.Submodule.ker φ).ι ≫ cokernel.π K.ι = 0 :=
    submodule_ι_comp_cokernel_π_eq_zero_of_le A B hS W le_sup_left
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : 𝒢 ⟶ cokernel K.ι, φ ≫ ψ₀ = cokernel.π K.ι :=
    ⟨hc.desc (CokernelCofork.ofπ (cokernel.π K.ι) h0),
      hc.fac (CokernelCofork.ofπ (cokernel.π K.ι) h0) WalkingParallelPair.one⟩
  have h1 : (idealPowerMultiple B _ hS W.1 W.2 (C1573.baseIdealSubmodule W.1 W.2 I) (n + 1) 𝒢).ι ≫
      ψ₀ = 0 := by
    refine idealPowerMultiple_ι_comp_eq_zero_of_epi B _ hS W.1 W.2 _ (n + 1) φ ψ₀ ?_
    rw [hψ₀]
    refine submodule_ι_comp_cokernel_π_eq_zero_of_le A B hS W ?_
    rw [idealPowerMultiple_baseIdealSubmodule]
    exact le_sup_right
  obtain ⟨ψ, hψ⟩ : ∃ ψ : idealPowerQuotient B _ hS W.1 W.2 (C1573.baseIdealSubmodule W.1 W.2 I)
      (n + 1) 𝒢 ⟶ cokernel K.ι,
      cokernel.π (idealPowerMultiple B _ hS W.1 W.2 (C1573.baseIdealSubmodule W.1 W.2 I)
        (n + 1) 𝒢).ι ≫ ψ = ψ₀ :=
    ⟨cokernel.desc _ ψ₀ h1, cokernel.π_desc _ _ _⟩
  have hKR : φ ≫ cokernel.π (idealPowerMultiple B _ hS W.1 W.2 (C1573.baseIdealSubmodule W.1 W.2 I)
      (n + 1) 𝒢).ι = cokernel.π J.ι ≫ e.inv := by
    rw [← he]; simp
  have hfac : cokernel.π J.ι ≫ e.inv ≫ ψ = cokernel.π K.ι := by
    rw [← Category.assoc, ← hKR, Category.assoc, hψ, hψ₀]
  intro U x hx
  exact (cokernel_π_app_eq_zero_iff B _ hS W.1 W.2 K U x).1
    (app_eq_zero_of_comp_eq A B hS W hfac U x
      ((cokernel_π_app_eq_zero_iff B _ hS W.1 W.2 J U x).2 hx))

/-- **The kernel of an epimorphism from `𝒪_W` is quasi-coherent, and `𝒪_W` modulo it is the
target.** -/
theorem ker_isQuasicoherentOnSite_and_cokernel_iso
    (W : AlgebraicSpaces B (Spec (.of A)) hS)
    {𝒢 : Modules.{u, u} B _ hS W.1 W.2} (hG : 𝒢.IsQuasicoherentOnSite)
    (φ : SheafOfModules.unit _ ⟶ 𝒢) [Epi φ] :
    (SheafOfModules.Submodule.ker φ).toSheafOfModules.IsQuasicoherentOnSite ∧
      Nonempty (cokernel (SheafOfModules.Submodule.ker φ).ι ≅ 𝒢) := by
  have : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B _ hS W.1 W.2).O)).IsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_unit _
  exact ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso
      (SheafOfModules.Submodule.kerIsoKernel φ).symm
      (isQuasicoherentOnSite_kernel_of_quasicoherent B _ hS W.1 W.2 φ),
    ⟨(cokernelIsCokernel (SheafOfModules.Submodule.ker φ).ι).coconePointUniqueUpToIso
      (Abelian.epiIsCokernelOfKernel _ (SheafOfModules.Submodule.isLimitKernelFork φ))⟩⟩

/-- **The ideal-theoretic form of Stacks 08BG.** Let `A` be Noetherian and `I`-adically
complete and `W` separated of finite type over `Spec A`. A tower of quasi-coherent ideals
`𝒥_n = 𝒥_{n+1} + I^{n+1} 𝒪_W` such that `𝒪_W / 𝒥_0` has support proper over `Spec A` comes from
one quasi-coherent ideal `𝒦`: `𝒥_n = 𝒦 + I^{n+1} 𝒪_W`, and `𝒪_W / 𝒦` has support proper over
`Spec A`. -/
theorem exists_ideal_eq_sup_baseIdealSubmodule [IsNoetherianRing A] [IsAdicComplete I A]
    (W : AlgebraicSpaces B (Spec (.of A)) hS) (f : W ⟶ schemeSpace (baseObject A B hS))
    (hft : IsFiniteType B _ hS f.hom) (hsep : IsSeparated B _ hS f.hom)
    (𝒥 : ℕ → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B _ hS W.1 W.2).O)).Submodule)
    (hq : ∀ n, (𝒥 n).toSheafOfModules.IsQuasicoherentOnSite)
    (h𝒥 : ∀ n, 𝒥 n = 𝒥 (n + 1) ⊔ C1573.baseIdealSubmodule W.1 W.2 (I ^ (n + 1)))
    (hE0 : HasProperSupport B _ hS W.2 (schemeSpace (baseObject A B hS)).2 f.hom hft.1
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B _ hS W.1 W.2).O)).obj (cokernel (𝒥 0).ι))) :
    ∃ 𝒦 : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B _ hS W.1 W.2).O)).Submodule,
      𝒦.toSheafOfModules.IsQuasicoherentOnSite ∧
      (∀ n, 𝒦 ≤ 𝒥 n) ∧ (∀ n, 𝒥 n ≤ 𝒦 ⊔ C1573.baseIdealSubmodule W.1 W.2 (I ^ (n + 1))) ∧
      HasProperSupport B _ hS W.2 (schemeSpace (baseObject A B hS)).2 f.hom hft.1
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B _ hS W.1 W.2).O)).obj (cokernel 𝒦.ι)) := by
  obtain ⟨𝒢, φ, hφ⟩ := exists_completion_iso_idealQuotient A I B hS W f hft hsep 𝒥 hq h𝒥 hE0
  have := epi_of_reduction_iso_idealQuotient A I B hS W f hft 𝒥 𝒢 φ hφ
  obtain ⟨hKq, ⟨ε⟩⟩ := ker_isQuasicoherentOnSite_and_cokernel_iso A B hS W
    𝒢.obj.property.toIsQuasicoherentOnSite φ
  choose e he using hφ
  refine ⟨_, hKq, fun n => ker_le_of_reduction_iso_idealQuotient A I B hS W (𝒥 n) φ n (e n) (he n),
    fun n => le_ker_sup_of_reduction_iso_idealQuotient A I B hS W (𝒥 n) φ n (e n) (he n), ?_⟩
  obtain ⟨hGcl, hGp⟩ := 𝒢.property
  exact (congrArg (fun T => ∃ hT : IsClosed T, IsProperOver B _ hS W.2
    (schemeSpace (baseObject A B hS)).2 f.hom hft.1 T hT)
      (supportOfSheaf_eq_of_iso B _ hS W ε)).mpr ⟨hGcl, hGp⟩

/-- **Stacks 08BG.** Let `A` be a Noetherian ring complete with respect to `I` and `W` separated
and of finite type over `Spec A`, with adic fibres `W_n`. A family of closed subspaces
`Γ_n ⊆ W` with `Γ_n = Γ_{n+1} ∩ W_n` and `Γ_0` proper over `Spec A` is the family of
intersections `Z ∩ W_n` of one closed subspace `Z ⊆ W`, proper over `Spec A`. -/
theorem exists_closedSubspace_inf_adicFibreSubspace_eq [IsNoetherianRing A] [IsAdicComplete I A]
    (W : AlgebraicSpaces B (Spec (.of A)) hS) (f : W ⟶ schemeSpace (baseObject A B hS))
    (hft : IsFiniteType B _ hS f.hom) (hsep : IsSeparated B _ hS f.hom)
    (Γ : ℕ → ClosedSubspaces B _ hS W.1)
    (hΓ : ∀ n, (Γ n).1 = (Γ (n + 1)).1 ⊓ (adicFibreSubspace A I B hS hSn W f.hom n).1)
    (hp : IsProper B _ hS ((Γ 0).1.ι ≫ f.hom)) :
    ∃ Z : ClosedSubspaces B _ hS W.1,
      (∀ n, Z.1 ⊓ (adicFibreSubspace A I B hS hSn W f.hom n).1 = (Γ n).1) ∧
      IsProper B _ hS (Z.1.ι ≫ f.hom) := by
  have := C1573.fact_isLocallyNoetherian_of_baseObject W f hft.1
  let 𝒥 : ℕ → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B _ hS W.1 W.2).O)).Submodule :=
    fun n => definingIdealSheaf B _ hS W (Γ n)
  have h𝒥 : ∀ n, 𝒥 n = 𝒥 (n + 1) ⊔ C1573.baseIdealSubmodule W.1 W.2 (I ^ (n + 1)) := by
    intro n
    have e : Γ n = schemeTheoreticIntersection B _ hS W.1 W.2 (Γ (n + 1))
        (adicFibreSubspace A I B hS hSn W f.hom n) := Subtype.ext (hΓ n)
    show definingIdealSheaf B _ hS W (Γ n) = _
    rw [e, definingIdealSheaf_schemeTheoreticIntersection]
    exact congrArg₂ (· ⊔ ·) rfl (definingIdealSheaf_adicFibreSubspace A I B hS hSn W f.hom n)
  obtain ⟨𝒦, hKq, hK𝒥, h𝒥K, hKp⟩ := exists_ideal_eq_sup_baseIdealSubmodule A I B hS W f hft hsep 𝒥
    (fun n => isQuasicoherentOnSite_definingIdealSheaf B _ hS W (Γ n)) h𝒥
    (hasProperSupport_cokernel_definingIdealSheaf_of_isAlgebraicSpace A B hS W
      (schemeSpace (baseObject A B hS)).2 f.hom hft.1 (Γ 0) hp)
  obtain ⟨Z, hZ⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B _ hS W 𝒦 hKq
  refine ⟨Z, fun n => le_antisymm ?_ ?_, ?_⟩
  · exact le_of_definingIdealSheaf_le B _ hS W
      (schemeTheoreticIntersection B _ hS W.1 W.2 Z (adicFibreSubspace A I B hS hSn W f.hom n))
      (Γ n) (by
        rw [definingIdealSheaf_schemeTheoreticIntersection, hZ,
          definingIdealSheaf_adicFibreSubspace A I B hS hSn W f.hom n]
        exact h𝒥K n)
  · exact le_inf (le_of_definingIdealSheaf_le B _ hS W (Γ n) Z (hZ.trans_le (hK𝒥 n)))
      ((hΓ n).le.trans inf_le_right)
  · exact isProper_of_hasProperSupport_cokernel_definingIdealSheaf A B hS W _ f.hom hft.1 Z
      (hZ ▸ hKp)

end AlgebraicGeometry.Space

end
