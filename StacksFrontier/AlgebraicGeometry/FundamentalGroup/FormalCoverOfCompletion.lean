module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FormalCoverNeighbourhoodLift
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FiniteLocallyFreeAdic

/-!
# The formal finite étale cover as the completion of a module on a neighbourhood

Let `i : Z ⟶ X` be a closed immersion of locally Noetherian schemes with ideal sheaf `J`, `A ⟶ Z`
a finite étale cover and `(ℱₙ)` the finite locally free object of `Coh(X, J)` attached to it
(`Stacks.FundamentalGroup.InfinitesimalLift.system`). If `ℱ` is the completion of a module `𝒢` on
an open neighbourhood `V` of `Z`, then the completion maps `𝒢 ⟶ 𝒢/J^{n+1}𝒢 ≅ ℱₙ|_V` form a formal
datum on `V` (`Stacks.FundamentalGroup.InfinitesimalLift.FormalDatum`). This is how the
essential surjectivity half of the hypothesis of [Stacks, Tag 0EK1] enters its proof.

## Main definitions

* `Stacks.FundamentalGroup.InfinitesimalLift.adicSystemOfKer` — the formal cover as an object of
  `Coh(X, J)` for any presentation `J` of the ideal sheaf of `i`.
* `Stacks.FundamentalGroup.InfinitesimalLift.moduleIsoPushforwardOpenModule` — `ℱₙ` is the
  direct image along `V ⟶ X` of the direct image of the structure sheaf of `Cₙ` along `Cₙ ⟶ V`.
* `Stacks.FundamentalGroup.InfinitesimalLift.restrictModuleIso` — `ℱₙ|_V` is the direct image of
  the structure sheaf of `Cₙ` along `Cₙ ⟶ V`.
* `Stacks.FundamentalGroup.InfinitesimalLift.formalDatumOfCompletion` — the formal datum.

## References

* [Stacks Project, Tag 0EK1](https://stacks.math.columbia.edu/tag/0EK1)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec (AlgebraSheaf)
open Stacks.Thickenings

universe u

namespace Stacks.FundamentalGroup.InfinitesimalLift

open Stacks.Algebraization

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (A : FiniteEtaleOver Z)

/-- The formal cover as an object of `Coh(X, J)`, for any ideal sheaf `J` equal to that of `i`. -/
public def adicSystemOfKer [IsLocallyNoetherian X] (J : X.IdealSheafData) (hJ : i.ker = J) :
    Stacks.Coherent.CoherentAdicSystems J :=
  ⟨system i A, hJ ▸ isCoherentAdicSystem_system i A⟩

/-- The formal cover is a finite locally free object of `Coh(X, J)`. -/
public theorem isFiniteLocallyFreeAdic_adicSystemOfKer [IsLocallyNoetherian X]
    (J : X.IdealSheafData) (hJ : i.ker = J) :
    IsFiniteLocallyFreeAdic J (adicSystemOfKer i A J hJ) := by
  subst hJ
  exact isFiniteLocallyFreeAdic_system i A

variable (V : X.Opens) (hV : Set.range i.base ⊆ V)

/-- The structure morphism `Cₙ ⟶ X` factors through the open neighbourhood `V`. -/
public theorem toBase_eq_toOpen_ι (n : ℕ) : toBase i A n = toOpen i A V hV n ≫ V.ι := by
  rw [Category.assoc, nbhdHom_ι]

/-- `(Cₙ ⟶ X)_* 𝒪_{Cₙ}` is the direct image along `V ⟶ X` of `(Cₙ ⟶ V)_* 𝒪_{Cₙ}`. -/
def moduleIsoPushforwardOpenModule (n : ℕ) :
    module i A n ≅ (Scheme.Modules.pushforward V.ι).obj (openModule i A V hV n) :=
  (Scheme.Modules.pushforwardCongr (toBase_eq_toOpen_ι i A V hV n)).app
      (SheafOfModules.unit _) ≪≫
    ((Scheme.Modules.pushforwardComp (toOpen i A V hV n) V.ι).app (SheafOfModules.unit _)).symm

/-- The identification of `moduleIsoPushforwardOpenModule`, for arbitrary schemes over `V`, is
compatible with the maps induced by a morphism over `V`. -/
private theorem underlyingModuleMap_pushforwardAlgebraHomOfEq_comp {C C' : Scheme.{u}}
    (t : C ⟶ C') (p : C ⟶ V.toScheme) (p' : C' ⟶ V.toScheme) (ht : t ≫ p' = p)
    (q : C ⟶ X) (q' : C' ⟶ X) (hq : q = p ≫ V.ι) (hq' : q' = p' ≫ V.ι) (hqt : t ≫ q' = q) :
    AlgebraSheaf.underlyingModuleMap (AdicFiniteAlgebra.pushforwardAlgebraHomOfEq q q' t hqt) ≫
        ((Scheme.Modules.pushforwardCongr hq).app (SheafOfModules.unit _) ≪≫
          ((Scheme.Modules.pushforwardComp p V.ι).app (SheafOfModules.unit _)).symm).hom =
      ((Scheme.Modules.pushforwardCongr hq').app (SheafOfModules.unit _) ≪≫
          ((Scheme.Modules.pushforwardComp p' V.ι).app (SheafOfModules.unit _)).symm).hom ≫
        (Scheme.Modules.pushforward V.ι).map (AlgebraSheaf.underlyingModuleMap
          (AdicFiniteAlgebra.pushforwardAlgebraHomOfEq p p' t ht)) := by
  subst hq hq'
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext x
  have h1 := AdicFiniteAlgebra.pushforwardAlgebraHomOfEq_app (p ≫ V.ι) (p' ≫ V.ι) t hqt U
  have h2 := AdicFiniteAlgebra.pushforwardAlgebraHomOfEq_app p p' t ht (V.ι ⁻¹ᵁ U)
  show ((C.presheaf.map (eqToHom rfl).op) ((AdicFiniteAlgebra.pushforwardAlgebraHomOfEq
      (p ≫ V.ι) (p' ≫ V.ι) t hqt).right.hom.app (op U) x) : Γ(C, p ⁻¹ᵁ V.ι ⁻¹ᵁ U)) =
    (AdicFiniteAlgebra.pushforwardAlgebraHomOfEq p p' t ht).right.hom.app (op (V.ι ⁻¹ᵁ U))
      (C'.presheaf.map (eqToHom rfl).op x)
  rw [h1, h2]
  simp only [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **The restriction of `(Cₙ ⟶ X)_* 𝒪_{Cₙ}` to `V` is `(Cₙ ⟶ V)_* 𝒪_{Cₙ}`.** -/
public def restrictModuleIso (n : ℕ) :
    (Scheme.Modules.restrictFunctor V.ι).obj (module i A n) ≅ openModule i A V hV n :=
  (Scheme.Modules.restrictFunctor V.ι).mapIso (moduleIsoPushforwardOpenModule i A V hV n) ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso V.ι).app _

/-- The identification of `restrictModuleIso` is compatible with the transition maps. -/
public theorem restrictModuleIso_naturality (n : ℕ) :
    (Scheme.Modules.restrictFunctor V.ι).map (moduleStep i A n) ≫
        (restrictModuleIso i A V hV n).hom =
      (restrictModuleIso i A V hV (n + 1)).hom ≫ openModuleStep i A V hV n := by
  have h : moduleStep i A n ≫ (moduleIsoPushforwardOpenModule i A V hV n).hom =
      (moduleIsoPushforwardOpenModule i A V hV (n + 1)).hom ≫
        (Scheme.Modules.pushforward V.ι).map (openModuleStep i A V hV n) :=
    underlyingModuleMap_pushforwardAlgebraHomOfEq_comp V (step i A n)
      (toOpen i A V hV n) (toOpen i A V hV (n + 1)) (step_toOpen i A V hV n)
      (toBase i A n) (toBase i A (n + 1)) (toBase_eq_toOpen_ι i A V hV n)
      (toBase_eq_toOpen_ι i A V hV (n + 1)) (step_toBase i A n)
  let R := Scheme.Modules.restrictFunctor V.ι
  let ε := (Scheme.Modules.restrictFunctorAdjCounitIso V.ι).hom
  show R.map (moduleStep i A n) ≫ R.map (moduleIsoPushforwardOpenModule i A V hV n).hom ≫
      ε.app _ = (R.map (moduleIsoPushforwardOpenModule i A V hV (n + 1)).hom ≫ ε.app _) ≫
        openModuleStep i A V hV n
  calc R.map (moduleStep i A n) ≫ R.map (moduleIsoPushforwardOpenModule i A V hV n).hom ≫
        ε.app _
      = R.map (moduleStep i A n ≫ (moduleIsoPushforwardOpenModule i A V hV n).hom) ≫
          ε.app _ := (R.map_comp_assoc _ _ _).symm
    _ = R.map ((moduleIsoPushforwardOpenModule i A V hV (n + 1)).hom ≫
          (Scheme.Modules.pushforward V.ι).map (openModuleStep i A V hV n)) ≫ ε.app _ :=
        congrArg (fun f => R.map f ≫ ε.app _) h
    _ = R.map (moduleIsoPushforwardOpenModule i A V hV (n + 1)).hom ≫
          (R.map ((Scheme.Modules.pushforward V.ι).map (openModuleStep i A V hV n)) ≫
            ε.app _) := R.map_comp_assoc _ _ _
    _ = R.map (moduleIsoPushforwardOpenModule i A V hV (n + 1)).hom ≫
          (ε.app _ ≫ openModuleStep i A V hV n) :=
        congrArg (R.map (moduleIsoPushforwardOpenModule i A V hV (n + 1)).hom ≫ ·)
          (ε.naturality (openModuleStep i A V hV n))
    _ = _ := (Category.assoc _ _ _).symm

/-- The ideal sheaf of `Zₙ ⊆ V` is the `(n+1)`-st power of the restriction of `J`. -/
public theorem ker_nbhdHom (J : X.IdealSheafData) (hJ : i.ker = J) (n : ℕ) :
    (nbhdHom i V hV n).ker = (J.comap V.ι) ^ (n + 1) := by
  have H : IsPullback (nbhdHom i V hV n) (𝟙 _) V.ι (nthOrderToBase i n) :=
    IsPullback.of_vert_isIso_mono ⟨by rw [nbhdHom_ι, Category.id_comp]⟩
  have hk : (nbhdHom i V hV n).ker = (nthOrderToBase i n).ker.comap V.ι := by
    ext U : 2
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    exact Scheme.ker_ideal_of_isPullback_of_isOpenImmersion _ _ _ _ H U
  rw [hk, ker_nthOrderToBase, hJ, Stacks.IdealSheaf.comap_pow]

/-- **The completion maps of a module whose completion is the formal cover form a formal
datum.** -/
public def formalDatumOfCompletion [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (hJ : i.ker = J)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules V.toScheme.ringCatSheaf)
    (e : ((completionFunctor V.toScheme (J.comap V.ι)).obj G).obj ≅
      ((adicSystemOfKer i A J hJ).obj ⋙ Scheme.Modules.restrictFunctor V.ι)) :
    FormalDatum i A V hV G.obj where
  p n := completionProjection V.toScheme (J.comap V.ι) G n ≫ e.hom.app (op n) ≫
    (restrictModuleIso i A V hV n).hom
  p_step n := by
    let c := completionProjection V.toScheme (J.comap V.ι) G
    let R := Scheme.Modules.restrictFunctor V.ι
    let f : op (n + 1) ⟶ op n := (homOfLE (Nat.le_succ n)).op
    let r := fun k => (restrictModuleIso i A V hV k).hom
    calc (c (n + 1) ≫ e.hom.app (op (n + 1)) ≫ r (n + 1)) ≫ openModuleStep i A V hV n
        = c (n + 1) ≫ e.hom.app (op (n + 1)) ≫ (r (n + 1) ≫ openModuleStep i A V hV n) :=
          (Category.assoc _ _ _).trans (congrArg (c (n + 1) ≫ ·) (Category.assoc _ _ _))
      _ = c (n + 1) ≫ e.hom.app (op (n + 1)) ≫ (R.map (moduleStep i A n) ≫ r n) :=
          congrArg (fun k => c (n + 1) ≫ e.hom.app (op (n + 1)) ≫ k)
            (restrictModuleIso_naturality i A V hV n).symm
      _ = c (n + 1) ≫ ((e.hom.app (op (n + 1)) ≫ R.map (moduleStep i A n)) ≫ r n) :=
          congrArg (c (n + 1) ≫ ·) (Category.assoc _ _ _).symm
      _ = c (n + 1) ≫ ((((completionFunctor V.toScheme (J.comap V.ι)).obj G).obj.map f ≫
            e.hom.app (op n)) ≫ r n) :=
          congrArg (fun k => c (n + 1) ≫ (k ≫ r n)) ((e.hom.naturality f).trans
            (congrArg (e.hom.app (op (n + 1)) ≫ R.map ·) (system_map_succ i A n))).symm
      _ = (c (n + 1) ≫ ((completionFunctor V.toScheme (J.comap V.ι)).obj G).obj.map f) ≫
            e.hom.app (op n) ≫ r n :=
          (congrArg (c (n + 1) ≫ ·) (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm
      _ = c n ≫ e.hom.app (op n) ≫ r n :=
          congrArg (· ≫ e.hom.app (op n) ≫ r n)
            (completionProjection_transition V.toScheme (J.comap V.ι) G n)
  surjective n U := by
    have hG : G.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent G.obj
    have hc : Epi (completionProjection V.toScheme (J.comap V.ι) G n) :=
      epi_completionProjection _ _ _ n
    have hψ : Epi (e.app (op n) ≪≫ restrictModuleIso i A V hV n).hom :=
      IsIso.epi_of_iso _
    exact @surjective_app_of_epi_of_isAffineOpen V.toScheme G.obj (openModule i A V hV n) hG
      (isQuasicoherent_openModule i A V hV n) _ (@epi_comp _ _ _ _ _ _ hc _ hψ) U.1 U.2
  mem_of_eq_zero n U s hs := by
    have hG : G.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent G.obj
    let P := idealPowerMultiple (J.comap V.ι) (n + 1) G.obj
    let ψ := eqToIso (completionFunctor_obj V.toScheme (J.comap V.ι) G n).symm ≪≫
      e.app (op n) ≪≫ restrictModuleIso i A V hV n
    have hb := (bijective_app_of_isIso ψ.hom U.1).1
    have hπ : (cokernel.π (C := V.toScheme.Modules) P.ι).app U.1 s = 0 :=
      hb (hs.trans (map_zero _).symm)
    have hP := (cokernel_π_app_eq_zero_iff G.obj P U.1 s).1 hπ
    rw [ker_nbhdHom i V hV J hJ n]
    rwa [@idealPowerMultiple_toSubmodule_obj_affine V.toScheme (J.comap V.ι) (n + 1) G.obj hG U]
      at hP

end Stacks.FundamentalGroup.InfinitesimalLift

end
