module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.AdicFibreTower
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.TowerDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystemProperSupport

/-!
# Algebraizing a surjection onto a system on the adic fibres

Let `X` be an algebraic space separated and of finite type over a Noetherian ring `A` complete
along `I`, and let `Φ` be the restriction of coherent `𝒪_X`-modules to the tower of adic fibres.
Suppose Grothendieck's existence theorem holds on `X` in the two forms of Stacks 08BE (essential
surjectivity of the completion functor onto the systems with proper support) and Stacks 08B9 (its
full faithfulness on pairs whose target has proper support). Then a levelwise surjective morphism
of systems `σ : Φ(M₀) ⟶ (F_n)` from the restriction of a coherent module onto a system whose
lowest term has proper support is the restriction of a surjection `M₀ ⟶ ℱ` onto a coherent module
`ℱ` with proper support, `(F_n) ≅ Φ(ℱ)`.

## Main results

* `AlgebraicGeometry.Space.exists_epi_of_epi_adicFibreRestriction`: the algebraization of `σ`.

## References

* [Stacks Project, Tag 08BG](https://stacks.math.columbia.edu/tag/08BG)
* [Stacks Project, Tag 08BE](https://stacks.math.columbia.edu/tag/08BE)
* [Stacks Project, Tag 08B9](https://stacks.math.columbia.edu/tag/08B9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` competes with the abelian
structure of `AlgebraicGeometry.Space.Modules`; the cokernels below are those of the latter. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hA : B.Contains (Spec (.of A)))
  {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B (Spec (.of A)) hA X) (f : X ⟶ yoneda.obj (baseObject A B hA))
  (hft : IsLocallyOfFiniteType B (Spec (.of A)) hA f)

include hX f hft in
/-- The local Noetherianity of `X` as an instance argument. -/
theorem fact_hasEtaleLocalProperty_isLocallyNoetherian_of_baseObject :
    Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
  ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isFiniteType_baseObject A B hA hX f hft⟩

/-- **Algebraizing a levelwise surjection onto a system with proper support.** Granted
Grothendieck's existence theorem on `X` (essential surjectivity, `hES`, and full faithfulness,
`hFF`, of the completion functor along `I 𝒪_X` on modules with proper support), a morphism of
systems `σ : Φ(M₀) ⟶ (F_n)` which is surjective at every level, onto a system whose lowest term
has support proper over `Spec A`, is the restriction of a surjection `s : M₀ ⟶ ℱ` onto a coherent
module with support proper over `Spec A`, through an identification `Φ(ℱ) ≅ (F_n)`. -/
theorem exists_epi_of_epi_adicFibreRestriction
    (hES : letI := fact_hasEtaleLocalProperty_isLocallyNoetherian_of_baseObject A B hA hX f hft
      (completionFunctorProperOver B (Spec (.of A)) hA X (yoneda.obj (baseObject A B hA)) hX
        (isAlgebraicSpace_yoneda B (Spec (.of A)) hA (baseObject A B hA)) f hft
        (baseIdealSheaf A ⟨X, hX⟩ I) (isQuasicoherentOnSite_baseIdealSheaf A ⟨X, hX⟩ I)).EssSurj)
    (hFF : ∀ M N : CoherentModules.{u, u} B (Spec (.of A)) hA X hX,
      HasProperSupport B (Spec (.of A)) hA hX (isAlgebraicSpace_yoneda B _ hA _) f hft
        ((SheafOfModules.toSheaf _).obj N.obj) →
      letI := fact_hasEtaleLocalProperty_isLocallyNoetherian_of_baseObject A B hA hX f hft
      Function.Bijective (fun a : M ⟶ N => (completionFunctor B (Spec (.of A)) hA X hX
        (baseIdealSheaf A ⟨X, hX⟩ I) (isQuasicoherentOnSite_baseIdealSheaf A ⟨X, hX⟩ I)).map a))
    (G : ThickeningCoherentSystem B (Spec (.of A)) hA (adicFibreSpace A I B hA hX f)
      (adicFibreSuccHom A I B hA hX f))
    (hG : HasProperSupport B (Spec (.of A)) hA hX (isAlgebraicSpace_yoneda B _ hA _) f hft
      ((SheafOfModules.toSheaf _).obj ((modulePushforward B (Spec (.of A)) hA
        (adicFibreFstHom A I B hA hX f 0)).obj (G.term 0).obj)))
    (M₀ : CoherentModules.{u, u} B (Spec (.of A)) hA X hX)
    (σ : (adicFibreRestriction A I B hA hX f hft).obj M₀ ⟶ G) (hσ : ∀ n, Epi (σ.app n)) :
    ∃ (M : CoherentModules.{u, u} B (Spec (.of A)) hA X hX) (s : M₀ ⟶ M)
      (eM : (adicFibreRestriction A I B hA hX f hft).obj M ≅ G),
      HasProperSupport B (Spec (.of A)) hA hX (isAlgebraicSpace_yoneda B _ hA _) f hft
        ((SheafOfModules.toSheaf _).obj M.obj) ∧ Epi s.hom ∧
      (adicFibreRestriction A I B hA hX f hft).map s ≫ eM.hom = σ := by
  let := fact_hasEtaleLocalProperty_isLocallyNoetherian_of_baseObject A B hA hX f hft
  have hker := fun n M => kerIdealSmul_adicFibreFstHom_eq_idealPowerMultiple A I B hA hX f n M
  have hi := isClosedImmersion_adicFibreFstHom A I B hA hX f
  obtain ⟨M, hM, ⟨eM⟩⟩ := exists_hasProperSupport_iso_thickeningRestriction B (Spec (.of A)) hA
    (X := ⟨X, hX⟩) (adicFibreFstHom A I B hA hX f) (adicFibreSuccHom A I B hA hX f)
    (adicFibreSuccHom_comp_adicFibreFstHom A I B hA hX f) hi
    (hasEtaleLocalProperty_isLocallyNoetherian_adicFibre A I B hA hX f hft)
    hker (isQuasicoherentOnSite_baseIdealSheaf A ⟨X, hX⟩ I)
    (isAlgebraicSpace_yoneda B _ hA (baseObject A B hA)) f hft G hG
  have hbij : ∀ (M N : CoherentModules.{u, u} B (Spec (.of A)) hA X hX)
      (h : HasProperSupport B (Spec (.of A)) hA hX (isAlgebraicSpace_yoneda B _ hA _) f hft
        ((SheafOfModules.toSheaf _).obj N.obj)),
      Function.Bijective (fun a : M ⟶ N => (adicFibreRestriction A I B hA hX f hft).map a) :=
    fun M N h => bijective_thickeningRestriction_map_of_bijective B (Spec (.of A)) hA
      (X := ⟨X, hX⟩) (adicFibreFstHom A I B hA hX f) (adicFibreSuccHom A I B hA hX f)
      (adicFibreSuccHom_comp_adicFibreFstHom A I B hA hX f) hi
      (hasEtaleLocalProperty_isLocallyNoetherian_adicFibre A I B hA hX f hft)
      hker (isQuasicoherentOnSite_baseIdealSheaf A ⟨X, hX⟩ I) (hFF M N h)
  obtain ⟨s, hs⟩ := (hbij M₀ M hM).2 (σ ≫ eM.inv)
  have hs2 : (adicFibreRestriction A I B hA hX f hft).map s = σ ≫ eM.inv := hs
  have hs' : (adicFibreRestriction A I B hA hX f hft).map s ≫ eM.hom = σ := by
    rw [hs2, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨M, s, eM, hM, ?_, hs'⟩
  let C : CoherentModules.{u, u} B (Spec (.of A)) hA X hX :=
    ⟨cokernel s.hom, isCoherent_cokernel B (Spec (.of A)) hA X hX M₀.property M.property s.hom⟩
  have hC : HasProperSupport B (Spec (.of A)) hA hX (isAlgebraicSpace_yoneda B _ hA _) f hft
      ((SheafOfModules.toSheaf _).obj C.obj) :=
    hasProperSupport_of_epi B (Spec (.of A)) hA hX (isAlgebraicSpace_yoneda B _ hA _) f hft
      (cokernel.π s.hom)
      (isFiniteTypeOnSite_of_isCoherentOnSite B (Spec (.of A)) hA ⟨X, hX⟩ M.obj) hM
  refine epi_of_epi_modulePullback_map B (Spec (.of A)) hA (X := ⟨X, hX⟩)
    (adicFibreFstHom A I B hA hX f) (adicFibreSuccHom A I B hA hX f)
    (adicFibreSuccHom_comp_adicFibreFstHom A I B hA hX f)
    (hasEtaleLocalProperty_isLocallyNoetherian_adicFibre A I B hA hX f hft) s (C := C)
    (cokernel.π s.hom) (cokernel.condition s.hom) (cokernelIsCokernel s.hom)
    (hbij C C hC).1 fun n => ?_
  have h1 : (modulePullback B (Spec (.of A)) hA (adicFibreFstHom A I B hA hX f n)).map s.hom =
      σ.app n ≫ (eM.inv).app n :=
    congrArg (fun a => TowerSystem.Hom.app a n) hs2
  rw [h1]
  have := hσ n
  have : IsIso (eM.inv.app n) := ⟨⟨eM.hom.app n, by
    rw [← TowerSystem.comp_app, eM.inv_hom_id, TowerSystem.id_app], by
    rw [← TowerSystem.comp_app, eM.hom_inv_id, TowerSystem.id_app]⟩⟩
  exact @epi_comp _ _ _ _ _ (σ.app n) (hσ n) (eM.inv.app n) inferInstance

end AlgebraicGeometry.Space

end
