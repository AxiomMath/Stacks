module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.InfinitesimalFiniteEtaleLift
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerPushforwardPullback
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.NeighbourhoodModules
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic

/-!
# The formal finite étale cover read over an open neighbourhood

Let `i : Z ⟶ X` be a closed immersion, `A ⟶ Z` a finite étale cover with lifts `Cₙ ⟶ Zₙ` to the
infinitesimal neighbourhoods (`Stacks.FundamentalGroup.InfinitesimalLift.cover`), and `V` an open
neighbourhood of `Z`. A *formal datum* on `V` for a quasi-coherent `𝒪_V`-module `𝒢` is a
compatible system of maps `pₙ : 𝒢 ⟶ (Cₙ ⟶ V)_* 𝒪_{Cₙ}` exhibiting `(Cₙ ⟶ V)_* 𝒪_{Cₙ}` as the
quotient of `𝒢` by the ideal of `Zₙ`; in other words, an identification of the completion of `𝒢`
with the formal finite étale cover. This is what the essential surjectivity half of the hypothesis
of [Stacks, Tag 0EK1] produces from the formal cover.

## Main definitions

* `Stacks.FundamentalGroup.InfinitesimalLift.openModule` — the `𝒪_V`-module `(Cₙ ⟶ V)_* 𝒪_{Cₙ}`,
  with transitions `openModuleStep` and composites `openModuleTrans`.
* `Stacks.FundamentalGroup.InfinitesimalLift.FormalDatum` — the datum.
* `Stacks.FundamentalGroup.InfinitesimalLift.FormalDatum.φ` — the identification
  `𝒢|_{Zₙ} ≅ (Cₙ ⟶ Zₙ)_* 𝒪_{Cₙ}` it induces on the infinitesimal neighbourhoods.

## Main results

* `Stacks.FundamentalGroup.InfinitesimalLift.FormalDatum.p_eq` — `pₙ` is the adjunction unit
  `𝒢 ⟶ zₙ_* zₙ^* 𝒢` followed by the direct image of `φₙ`, where `zₙ : Zₙ ⟶ V`.
* `Stacks.FundamentalGroup.InfinitesimalLift.FormalDatum.compIso_inv_pushforwardPullbackRestriction`
  — read through the `φₙ`, the restriction maps of the direct images of pullbacks of `𝒢` are the
  transitions of the formal cover. This is the compatibility condition (4) of
  [Stacks, Tag 0EK2] asks of a system of morphisms
  (`Stacks.Algebraization.InfinitesimalTower.exists_hom_pushforward`).

## Implementation notes

The quotient property makes `pₙ` the adjunction unit followed by an isomorphism
(`Stacks.FundamentalGroup.InfinitesimalLift.FormalDatum.exists_factor`): the quotient of `𝒢` by
the ideal of `Zₙ` is that direct image of a pullback by [Stacks, Tag 0EL1]
(`Stacks.Algebraization.idealQuotientPushforwardIso`), and the direct image along a closed
immersion is fully faithful ([Stacks, Tag 08KS]).

## References

* [Stacks Project, Tag 0EK1](https://stacks.math.columbia.edu/tag/0EK1)
* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec (AlgebraSheaf)
open Stacks.Thickenings
open Stacks.AlgebraicGeometry.HigherDirectImageCoherent
  (idealPowerMultiple_eq_bot_of_forall_smul_eq_zero)

universe u

namespace Stacks.Algebraization

/-- The morphism of pullbacks attached to the adjunction unit is the identity. -/
public theorem pullbackHomEquivPushforward_unit {S G : Scheme.{u}} (g : G ⟶ S) (P : S.Modules) :
    pullbackHomEquivPushforward g P _
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app P) = 𝟙 _ := by
  rw [pullbackHomEquivPushforward, Equiv.symm_apply_eq, Adjunction.homEquiv_unit,
    CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

/-- Restricting the identity of a pullback gives the identity. -/
public theorem pullbackHomMap_id {Z : Scheme.{u}} (G : Z.Modules) {A B : Scheme.{u}}
    {a : A ⟶ Z} {b : B ⟶ Z} (g : A ⟶ B) (hg : g ≫ b = a) :
    pullbackHomMap G G g hg (𝟙 _) = 𝟙 _ := by
  simp [pullbackHomMap]

/-- **The adjunction units are compatible with the restriction maps of direct images of
pullbacks.** -/
public theorem unit_comp_pushforwardPullbackRestriction {S G G' : Scheme.{u}} (g : G ⟶ S)
    (h : G' ⟶ G) (g' : G' ⟶ S) (hh : h ≫ g = g') (Q : S.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app Q ≫
        pushforwardPullbackRestriction g h g' hh Q =
      (Scheme.Modules.pullbackPushforwardAdjunction g').unit.app Q := by
  apply (pullbackHomEquivPushforward g' Q _).injective
  rw [pullbackHomEquivPushforward_pushforwardPullbackRestriction,
    pullbackHomEquivPushforward_unit, pullbackHomMap_id, pullbackHomEquivPushforward_unit]

/-- Naturality of `pullbackHomEquivPushforward` in the source. -/
public theorem pullbackHomEquivPushforward_comp_left {S G : Scheme.{u}} (g : G ⟶ S)
    {P P' : S.Modules} (M : G.Modules) (f : P ⟶ P')
    (β : P' ⟶ (Scheme.Modules.pushforward g).obj M) :
    pullbackHomEquivPushforward g P M (f ≫ β) =
      (Scheme.Modules.pullback g).map f ≫ pullbackHomEquivPushforward g P' M β :=
  Adjunction.homEquiv_naturality_left_symm _ _ _

/-- Naturality of `pullbackHomEquivPushforward` in the target. -/
public theorem pullbackHomEquivPushforward_comp_right {S G : Scheme.{u}} (g : G ⟶ S)
    (P : S.Modules) {M M' : G.Modules} (β : P ⟶ (Scheme.Modules.pushforward g).obj M)
    (ψ : M ⟶ M') :
    pullbackHomEquivPushforward g P M' (β ≫ (Scheme.Modules.pushforward g).map ψ) =
      pullbackHomEquivPushforward g P M β ≫ ψ :=
  Adjunction.homEquiv_naturality_right_symm _ _ _

/-- `pullbackHomEquivPushforward` is the pullback followed by the counit. -/
public theorem pullbackHomEquivPushforward_eq {S G : Scheme.{u}} (g : G ⟶ S) (P : S.Modules)
    (M : G.Modules) (β : P ⟶ (Scheme.Modules.pushforward g).obj M) :
    pullbackHomEquivPushforward g P M β =
      (Scheme.Modules.pullback g).map β ≫
        (Scheme.Modules.pullbackPushforwardAdjunction g).counit.app M :=
  Adjunction.homEquiv_counit _ _ _ _


end Stacks.Algebraization

namespace Stacks.FundamentalGroup.InfinitesimalLift

open Stacks.Algebraization

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (A : FiniteEtaleOver Z)
  (V : X.Opens) (hV : Set.range i.base ⊆ V)

/-! ### The formal cover read over an open neighbourhood -/

/-- The structure morphism `Zₙ ⟶ V` of the `n`-th infinitesimal neighbourhood, read over an open
neighbourhood `V`. -/
public abbrev nbhdHom (n : ℕ) : nthOrderInfinitesimalNeighbourhood i n ⟶ V.toScheme :=
  ((nbhdTower i V hV).obj n).hom

/-- `Zₙ ⟶ V ⟶ X` is the structure morphism of `Zₙ`. -/
@[reassoc]
public theorem nbhdHom_ι (n : ℕ) : nbhdHom i V hV n ≫ V.ι = nthOrderToBase i n :=
  nbhdOver_hom_ι i V hV n

/-- The structure morphism `Zₙ ⟶ V` is a closed immersion. -/
public instance isClosedImmersion_nbhdHom (n : ℕ) : IsClosedImmersion (nbhdHom i V hV n) := by
  have : IsClosedImmersion (nbhdHom i V hV n ≫ V.ι) := by
    rw [nbhdHom_ι]
    infer_instance
  exact IsClosedImmersion.of_comp (nbhdHom i V hV n) V.ι

/-- The successive inclusions of the infinitesimal neighbourhoods are morphisms over `V`. -/
@[reassoc]
public theorem nthOrderSucc_nbhdHom (n : ℕ) :
    nthOrderSucc i n ≫ nbhdHom i V hV (n + 1) = nbhdHom i V hV n :=
  (cancel_mono V.ι).1 (by rw [Category.assoc, nbhdHom_ι, nbhdHom_ι, nthOrderSucc_toBase])

/-- The composite `Cₙ ⟶ Zₙ ⟶ V`. -/
public abbrev toOpen (n : ℕ) : (cover i A n).left ⟶ V.toScheme :=
  (cover i A n).hom ≫ nbhdHom i V hV n

/-- The transition `Cₙ ⟶ Cₙ₊₁` is a morphism over `V`. -/
@[reassoc]
public theorem step_toOpen (n : ℕ) : step i A n ≫ toOpen i A V hV (n + 1) = toOpen i A V hV n := by
  rw [toOpen, ← Category.assoc, (isPullback_step i A n).w, Category.assoc, nthOrderSucc_nbhdHom]

/-- The structure morphism `Cₙ ⟶ V` is finite. -/
public instance isFinite_toOpen (n : ℕ) : IsFinite (toOpen i A V hV n) := by
  have : IsFinite (cover i A n).hom := (cover i A n).prop.1
  infer_instance

/-- The `𝒪_V`-module `(Cₙ ⟶ V)_* 𝒪_{Cₙ}`. -/
public abbrev openModule (n : ℕ) : V.toScheme.Modules :=
  AlgebraSheaf.underlyingModule (pushforwardAlgebra (toOpen i A V hV n))

/-- The transition morphism `(Cₙ₊₁ ⟶ V)_* 𝒪 ⟶ (Cₙ ⟶ V)_* 𝒪`. -/
public abbrev openModuleStep (n : ℕ) : openModule i A V hV (n + 1) ⟶ openModule i A V hV n :=
  AlgebraSheaf.underlyingModuleMap
    (AdicFiniteAlgebra.pushforwardAlgebraHomOfEq (toOpen i A V hV n) (toOpen i A V hV (n + 1))
      (step i A n) (step_toOpen i A V hV n))

/-- The module `(Cₙ ⟶ V)_* 𝒪_{Cₙ}` is quasi-coherent. -/
public instance isQuasicoherent_openModule (n : ℕ) : (openModule i A V hV n).IsQuasicoherent :=
  isQuasicoherent_pushforwardAlgebra (toOpen i A V hV n)

/-- The identification of the sections of `Cₙ` over the preimage of `U` with the sections of
`(Cₙ ⟶ V)_* 𝒪_{Cₙ}` over `U`, as an additive map. -/
public def openModuleAddHom (n : ℕ) (U : V.toScheme.Opens) :
    Γ((cover i A n).left, toOpen i A V hV n ⁻¹ᵁ U) →+ Γ(openModule i A V hV n, U) where
  toFun s := s
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The scalar action on the sections of `(Cₙ ⟶ V)_* 𝒪_{Cₙ}` is multiplication through the
structure morphism. -/
public theorem openModule_smul (n : ℕ) (U : V.toScheme.Opens) (r : Γ(V.toScheme, U))
    (s : Γ((cover i A n).left, toOpen i A V hV n ⁻¹ᵁ U)) :
    r • openModuleAddHom i A V hV n U s =
      openModuleAddHom i A V hV n U (((toOpen i A V hV n).app U).hom r * s) :=
  rfl

/-- The ideal of `Zₙ` in `V` annihilates `(Cₙ ⟶ V)_* 𝒪_{Cₙ}`. -/
public theorem idealPowerMultiple_openModule_eq_bot (n : ℕ) :
    idealPowerMultiple (nbhdHom i V hV n).ker 1 (openModule i A V hV n) = ⊥ := by
  refine idealPowerMultiple_eq_bot_of_forall_smul_eq_zero _ _ _ fun U a ha m => ?_
  rw [pow_one, Scheme.Hom.ker_apply] at ha
  obtain ⟨m', rfl⟩ : ∃ m', openModuleAddHom i A V hV n U.1 m' = m := ⟨m, rfl⟩
  rw [openModule_smul]
  have h1 : ((toOpen i A V hV n).app U.1).hom a = 0 := by
    have hc : ((toOpen i A V hV n).app U.1).hom a = ((cover i A n).hom.app _).hom
        (((nbhdHom i V hV n).app U.1).hom a) := rfl
    rw [hc, ha, map_zero]
    rfl
  rw [h1, zero_mul, map_zero]

/-- The identification `(Cₙ ⟶ V)_* 𝒪 ≅ zₙ_* (Cₙ ⟶ Zₙ)_* 𝒪`. -/
public abbrev compIso (n : ℕ) :
    (Scheme.Modules.pushforward (nbhdHom i V hV n)).obj
        ((Scheme.Modules.pushforward (cover i A n).hom).obj (SheafOfModules.unit _)) ≅
      openModule i A V hV n :=
  (Scheme.Modules.pushforwardComp (cover i A n).hom (nbhdHom i V hV n)).app _

/-! ### Formal data -/

/-- **A formal datum on `V` for a quasi-coherent `𝒪_V`-module `𝒢`:** compatible maps
`pₙ : 𝒢 ⟶ (Cₙ ⟶ V)_* 𝒪_{Cₙ}` which on every affine open are surjective with kernel generated by
the ideal of `Zₙ`. -/
public structure FormalDatum (G : V.toScheme.Modules) where
  /-- The maps to the direct images of the covers. -/
  p : ∀ n : ℕ, G ⟶ openModule i A V hV n
  p_step : ∀ n : ℕ, p (n + 1) ≫ openModuleStep i A V hV n = p n
  surjective : ∀ (n : ℕ) (U : V.toScheme.affineOpens), Function.Surjective ((p n).app U.1)
  mem_of_eq_zero : ∀ (n : ℕ) (U : V.toScheme.affineOpens) (s : Γ(G, U.1)),
    (p n).app U.1 s = 0 →
      s ∈ (nbhdHom i V hV n).ker.ideal U • (⊤ : Submodule Γ(V.toScheme, U.1) Γ(G, U.1))

namespace FormalDatum

variable {i A V hV} {G : V.toScheme.Modules} [G.IsQuasicoherent] (D : FormalDatum i A V hV G)

/-- **The maps of a formal datum are adjunction units followed by isomorphisms:**
`pₙ = (𝒢 ⟶ zₙ_* zₙ^* 𝒢) ≫ zₙ_* φₙ` for an isomorphism `φₙ : zₙ^* 𝒢 ≅ (Cₙ ⟶ Zₙ)_* 𝒪_{Cₙ}`, where
`zₙ : Zₙ ⟶ V`. -/
public theorem exists_factor (n : ℕ) :
    ∃ φ : (Scheme.Modules.pullback (nbhdHom i V hV n)).obj G ≅
        (Scheme.Modules.pushforward (cover i A n).hom).obj (SheafOfModules.unit _),
      D.p n = (Scheme.Modules.pullbackPushforwardAdjunction (nbhdHom i V hV n)).unit.app G ≫
        (Scheme.Modules.pushforward (nbhdHom i V hV n)).map φ.hom ≫
        (Scheme.Modules.pushforwardComp (cover i A n).hom (nbhdHom i V hV n)).hom.app _ := by
  let z := nbhdHom i V hV n
  let c := (cover i A n).hom
  let K := z.ker
  have hK : z.ker = K ^ 1 := (pow_one K).symm
  let comp := (Scheme.Modules.pushforwardComp c z).app (SheafOfModules.unit _)
  let d : idealPowerQuotient K 1 G ⟶ openModule i A V hV n :=
    cokernel.desc (C := V.toScheme.Modules) _ (D.p n)
      (comp_eq_zero_of_idealPowerMultiple_eq_bot _ _ _
        (idealPowerMultiple_openModule_eq_bot i A V hV n))
  have hd : cokernel.π (C := V.toScheme.Modules) (idealPowerMultiple K 1 G).ι ≫ d = D.p n :=
    cokernel.π_desc (C := V.toScheme.Modules) _ _ _
  have hdiso : IsIso d :=
    AdicFiniteAlgebra.isIso_cokernelDesc_of_affine K 1 G (openModule i A V hV n) (D.p n) d hd
      (D.surjective n) (fun U s hs => by simpa only [pow_one] using D.mem_of_eq_zero n U s hs)
  let Qi := idealQuotientPushforwardIso K 1 G z hK
  have hQi : cokernel.π (C := V.toScheme.Modules) (idealPowerMultiple K 1 G).ι ≫ Qi.hom =
      (Scheme.Modules.pullbackPushforwardAdjunction z).unit.app G :=
    idealQuotientPushforwardMap_π K 1 G z hK
  let ψ : (Scheme.Modules.pushforward z).obj ((Scheme.Modules.pullback z).obj G) ≅
      (Scheme.Modules.pushforward z).obj ((Scheme.Modules.pushforward c).obj
        (SheafOfModules.unit _)) :=
    Qi.symm ≪≫ asIso d ≪≫ comp.symm
  let φ := (Stacks.ClosedImmersion.fullyFaithfulPushforward z).preimageIso ψ
  refine ⟨φ, ?_⟩
  have hφ : (Scheme.Modules.pushforward z).map φ.hom = ψ.hom :=
    (Stacks.ClosedImmersion.fullyFaithfulPushforward z).map_preimage ψ.hom
  rw [hφ, ← hQi]
  show D.p n = cokernel.π (C := V.toScheme.Modules) (idealPowerMultiple K 1 G).ι ≫ Qi.hom ≫
    (Qi.inv ≫ d ≫ comp.inv) ≫ comp.hom
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact hd.symm

/-- The isomorphism `φₙ : zₙ^* 𝒢 ≅ (Cₙ ⟶ Zₙ)_* 𝒪_{Cₙ}` of `exists_factor`. -/
public def φ (n : ℕ) : (Scheme.Modules.pullback (nbhdHom i V hV n)).obj G ≅
    (Scheme.Modules.pushforward (cover i A n).hom).obj (SheafOfModules.unit _) :=
  (D.exists_factor n).choose

public theorem p_eq (n : ℕ) :
    D.p n = (Scheme.Modules.pullbackPushforwardAdjunction (nbhdHom i V hV n)).unit.app G ≫
      (Scheme.Modules.pushforward (nbhdHom i V hV n)).map (D.φ n).hom ≫ (compIso i A V hV n).hom :=
  (D.exists_factor n).choose_spec

/-- `pₙ` followed by the inverse of `zₙ_* φₙ` is the adjunction unit. -/
public theorem p_comp_inv (n : ℕ) :
    D.p n ≫ (compIso i A V hV n).inv ≫ (Scheme.Modules.pushforward (nbhdHom i V hV n)).map
        (D.φ n).inv =
      (Scheme.Modules.pullbackPushforwardAdjunction (nbhdHom i V hV n)).unit.app G := by
  rw [p_eq]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- The maps of a formal datum are epimorphisms. -/
public theorem epi_p (n : ℕ) : Epi (D.p n) := by
  rw [p_eq]
  have := Stacks.ClosedImmersion.epi_unit_app (nbhdHom i V hV n) G
  infer_instance

end FormalDatum

/-- The transition `(C_{n+k} ⟶ V)_* 𝒪 ⟶ (Cₙ ⟶ V)_* 𝒪`. -/
public def openModuleTrans (n : ℕ) : (k : ℕ) → openModule i A V hV (n + k) ⟶ openModule i A V hV n
  | 0 => 𝟙 _
  | k + 1 => openModuleStep i A V hV (n + k) ≫ openModuleTrans n k

/-- A system of maps compatible with the successive transitions is compatible with all of
them. -/
public theorem comp_openModuleTrans {E : V.toScheme.Modules}
    (q : ∀ n : ℕ, E ⟶ openModule i A V hV n)
    (hq : ∀ n : ℕ, q (n + 1) ≫ openModuleStep i A V hV n = q n) (n : ℕ) :
    ∀ k : ℕ, q (n + k) ≫ openModuleTrans i A V hV n k = q n
  | 0 => Category.comp_id _
  | k + 1 => by
    show q (n + k + 1) ≫ openModuleStep i A V hV (n + k) ≫ openModuleTrans i A V hV n k = _
    rw [← Category.assoc, hq, comp_openModuleTrans q hq n k]

namespace FormalDatum

variable {i A V hV} {G : V.toScheme.Modules} [G.IsQuasicoherent] (D : FormalDatum i A V hV G)

/-- **The restriction maps of direct images of pullbacks, read through the `φₙ`, are the
transitions of the formal cover.** -/
public theorem compIso_inv_pushforwardPullbackRestriction (n k : ℕ) (h : n ≤ n + k) :
    (compIso i A V hV (n + k)).inv ≫ (Scheme.Modules.pushforward (nbhdHom i V hV (n + k))).map
        (D.φ (n + k)).inv ≫
      pushforwardPullbackRestriction (nbhdHom i V hV (n + k))
        ((nbhdTower i V hV).trans n (n + k) h).left (nbhdHom i V hV n)
        (Over.w ((nbhdTower i V hV).trans n (n + k) h)) G =
    openModuleTrans i A V hV n k ≫ (compIso i A V hV n).inv ≫
      (Scheme.Modules.pushforward (nbhdHom i V hV n)).map (D.φ n).inv := by
  have := D.epi_p (n + k)
  apply (cancel_epi (D.p (n + k))).1
  have h1 : D.p (n + k) ≫ (compIso i A V hV (n + k)).inv ≫
      (Scheme.Modules.pushforward (nbhdHom i V hV (n + k))).map (D.φ (n + k)).inv ≫
        pushforwardPullbackRestriction (nbhdHom i V hV (n + k))
          ((nbhdTower i V hV).trans n (n + k) h).left (nbhdHom i V hV n)
          (Over.w ((nbhdTower i V hV).trans n (n + k) h)) G =
      (Scheme.Modules.pullbackPushforwardAdjunction (nbhdHom i V hV n)).unit.app G := by
    rw [reassoc_of% D.p_comp_inv (n + k)]
    exact unit_comp_pushforwardPullbackRestriction _ _ _ _ _
  have h2 : D.p (n + k) ≫ openModuleTrans i A V hV n k ≫ (compIso i A V hV n).inv ≫
      (Scheme.Modules.pushforward (nbhdHom i V hV n)).map (D.φ n).inv =
      (Scheme.Modules.pullbackPushforwardAdjunction (nbhdHom i V hV n)).unit.app G := by
    rw [← Category.assoc, comp_openModuleTrans i A V hV D.p D.p_step n k, D.p_comp_inv]
  exact h1.trans h2.symm



end FormalDatum

end Stacks.FundamentalGroup.InfinitesimalLift

end
