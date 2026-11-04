module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.LiftedQuotientTower

/-!
# The tower of reductions of a coherent adic system modulo the powers of a second ideal

Let `X` be a locally Noetherian scheme and let `ℐ, 𝒦 ⊆ 𝒪_X` be quasi-coherent ideal sheaves.
Dividing a coherent adic system along `ℐ` by a fixed power `𝒦 ʳ` is the endofunctor
`Stacks.Coherent.idealPowerQuotientAdicFunctor` of `Coh(X, ℐ)`. The proof of
[Stacks, Tag 088A] uses all of these endofunctors at once, as a tower

`… ⟶ (−) / 𝒦 ³ ⟶ (−) / 𝒦 ² ⟶ (−) / 𝒦 ¹`

indexed by `ℕᵒᵖ` and equipped with the projection from the identity functor. This file builds
that tower.

The transition is the descent of the projection onto the smaller quotient through the projection
onto the larger one, which is `Stacks.Algebraization.idealPowerQuotientDrop'`; it is natural in
the module because both sides are normalized by the quotient projection, which is an
epimorphism.

## Main definitions

* `Stacks.Coherent.idealPowerQuotientAdicProjection` — the projection
  `𝟭 ⟶ (−) / 𝒦 ʳ` on `Coh(X, ℐ)`.
* `Stacks.Coherent.idealPowerQuotientAdicDrop` — the transition `(−) / 𝒦 ˢ ⟶ (−) / 𝒦 ʳ` for
  `r ≤ s`.
* `Stacks.Coherent.idealPowerQuotientAdicTower` — the tower `e ↦ (−) / 𝒦 ᵉ⁺¹`, as a functor
  `ℕᵒᵖ ⥤ (Coh(X, ℐ) ⥤ Coh(X, ℐ))`.
* `Stacks.Coherent.coherentAdicTerms` — the terms of a coherent adic system, as a tower of
  coherent modules.
* `Stacks.Coherent.completionTermTower` — the terms of the `𝒦`-completion of a coherent module
  `H`, as a tower of coherent modules.
* `Stacks.Coherent.completionQuotientTowerIso` — **completion along `ℐ` exchanges the two
  towers**: the tower of `𝒦`-power reductions of `H ^∧_ℐ` is the tower of `ℐ`-completions of the
  terms of `H ^∧_𝒦`.

## Main results

* `Stacks.Coherent.idealPowerQuotientAdicProjection_drop` — the projections are compatible with
  the transitions, so they assemble into
  `Stacks.Coherent.idealPowerQuotientAdicTowerProjection`.
* `Stacks.Coherent.coherentAdicTermsFullyFaithful` — passing to the terms is fully faithful: a
  morphism of coherent adic systems is a morphism of the underlying towers of coherent modules.
* `Stacks.Coherent.idealPowerQuotientAdicProjection_comp_completionQuotientTowerTermIso` — the
  exchange is normalized by the projections, which is what forces its naturality.

## References

* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

variable {X : Scheme.{u}}

/-- **The drop between nested quotients is normalized by the projection.** -/
public theorem idealPowerQuotientDrop'_π (K : X.IdealSheafData) {r s : ℕ} (hrs : r ≤ s)
    (M : X.Modules) [M.IsQuasicoherent] :
    cokernel.π (C := X.Modules) (idealPowerMultiple K s M).ι ≫
        idealPowerQuotientDrop' K hrs M =
      cokernel.π (C := X.Modules) (idealPowerMultiple K r M).ι :=
  idealPowerQuotientDesc_π K s _ _

/-- **The drop between nested quotients is natural.** For `r ≤ s` the square comparing
`M / 𝒦 ˢ M ⟶ M / 𝒦 ʳ M` with the maps induced by `f : M ⟶ N` commutes; both composites are
normalized by the projection `M ⟶ M / 𝒦 ˢ M`, which is an epimorphism. -/
public theorem idealPowerQuotientDrop'_naturality (K : X.IdealSheafData) {r s : ℕ} (hrs : r ≤ s)
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    idealPowerQuotientMap K K s s le_rfl f ≫ idealPowerQuotientDrop' K hrs N =
      idealPowerQuotientDrop' K hrs M ≫ idealPowerQuotientMap K K r r le_rfl f := by
  refine (epi_cokernel_π_submodule_ι (idealPowerMultiple K s M)).left_cancellation _ _ ?_
  have hleft : cokernel.π (C := X.Modules) (idealPowerMultiple K s M).ι ≫
      idealPowerQuotientMap K K s s le_rfl f ≫ idealPowerQuotientDrop' K hrs N =
      f ≫ cokernel.π (C := X.Modules) (idealPowerMultiple K r N).ι :=
    (Category.assoc (obj := X.Modules) _ _ _).symm.trans
      ((congrArg (fun z => z ≫ idealPowerQuotientDrop' K hrs N)
          (idealPowerQuotientMap_π K K s s le_rfl f)).trans
        ((Category.assoc (obj := X.Modules) _ _ _).trans
          (congrArg (fun z => f ≫ z) (idealPowerQuotientDrop'_π K hrs N))))
  have hright : cokernel.π (C := X.Modules) (idealPowerMultiple K s M).ι ≫
      idealPowerQuotientDrop' K hrs M ≫ idealPowerQuotientMap K K r r le_rfl f =
      f ≫ cokernel.π (C := X.Modules) (idealPowerMultiple K r N).ι :=
    (Category.assoc (obj := X.Modules) _ _ _).symm.trans
      ((congrArg (fun z => z ≫ idealPowerQuotientMap K K r r le_rfl f)
          (idealPowerQuotientDrop'_π K hrs M)).trans
        (idealPowerQuotientMap_π K K r r le_rfl f))
  exact hleft.trans hright.symm

end Stacks.Algebraization

namespace Stacks.Coherent

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I K : X.IdealSheafData)

/-! ### The projection and the transitions -/

/-- **The projection of a coherent adic system onto its `𝒦 ʳ`-reduction.** -/
public def idealPowerQuotientAdicProjection (r : ℕ) :
    𝟭 (CoherentAdicSystems I) ⟶ idealPowerQuotientAdicFunctor I K r where
  app F := ObjectProperty.homMk
    { app n := cokernel.π (C := X.Modules) (idealPowerMultiple K r (F.obj.obj n)).ι
      naturality _ _ g := (idealPowerQuotientMap_π K K r r le_rfl (F.obj.map g)).symm }
  naturality _ _ g := ObjectProperty.hom_ext (IsCoherentAdicSystem I)
    (NatTrans.ext (funext fun n =>
      (idealPowerQuotientMap_π K K r r le_rfl (g.hom.app n)).symm))

/-- The component of the projection at a term is the quotient projection. -/
public theorem idealPowerQuotientAdicProjection_app_hom_app (r : ℕ)
    (F : CoherentAdicSystems I) (n : ℕᵒᵖ) :
    ((idealPowerQuotientAdicProjection I K r).app F).hom.app n =
      cokernel.π (C := X.Modules) (idealPowerMultiple K r (F.obj.obj n)).ι := rfl

/-- **The transition of the tower of reductions.** For `r ≤ s` the `𝒦 ˢ`-reduction of a coherent
adic system maps onto its `𝒦 ʳ`-reduction. -/
public def idealPowerQuotientAdicDrop {r s : ℕ} (hrs : r ≤ s) :
    idealPowerQuotientAdicFunctor I K s ⟶ idealPowerQuotientAdicFunctor I K r where
  app F := ObjectProperty.homMk
    { app n :=
        have := F.property.isQuasicoherent n.unop
        idealPowerQuotientDrop' K hrs (F.obj.obj n)
      naturality m n g := by
        have := F.property.isQuasicoherent m.unop
        have := F.property.isQuasicoherent n.unop
        exact idealPowerQuotientDrop'_naturality K hrs (F.obj.map g) }
  naturality F G g := by
    refine ObjectProperty.hom_ext (IsCoherentAdicSystem I) (NatTrans.ext (funext fun n => ?_))
    have := F.property.isQuasicoherent n.unop
    have := G.property.isQuasicoherent n.unop
    exact idealPowerQuotientDrop'_naturality K hrs (g.hom.app n)

/-- **The projections are compatible with the transitions.** -/
public theorem idealPowerQuotientAdicProjection_drop {r s : ℕ} (hrs : r ≤ s)
    (F : CoherentAdicSystems I) :
    (idealPowerQuotientAdicProjection I K s).app F ≫
        (idealPowerQuotientAdicDrop I K hrs).app F =
      (idealPowerQuotientAdicProjection I K r).app F := by
  refine ObjectProperty.hom_ext (IsCoherentAdicSystem I) (NatTrans.ext (funext fun n => ?_))
  have := F.property.isQuasicoherent n.unop
  exact idealPowerQuotientDrop'_π K hrs (F.obj.obj n)

/-- **The tower of reductions modulo the powers of `𝒦`**, as a functor `ℕᵒᵖ ⥤ (Coh(X, ℐ) ⥤
Coh(X, ℐ))`: the term `e` is the `𝒦 ᵉ⁺¹`-reduction, and the transitions drop the exponent. -/
public def idealPowerQuotientAdicTower :
    ℕᵒᵖ ⥤ (CoherentAdicSystems I ⥤ CoherentAdicSystems I) :=
  Functor.ofOpSequence (X := fun e => idealPowerQuotientAdicFunctor I K (e + 1))
    (fun e => idealPowerQuotientAdicDrop I K (Nat.le_succ (e + 1)))

/-- The transition of the tower from the exponent `e + 2` to the exponent `e + 1`. -/
public theorem idealPowerQuotientAdicTower_map_succ (e : ℕ) :
    (idealPowerQuotientAdicTower I K).map (homOfLE (Nat.le_add_right e 1)).op =
      idealPowerQuotientAdicDrop I K (Nat.le_succ (e + 1)) :=
  Functor.ofOpSequence_map_homOfLE_succ _ e

/-- **The projection from the identity functor into the tower.** -/
public def idealPowerQuotientAdicTowerProjection :
    (Functor.const ℕᵒᵖ).obj (𝟭 (CoherentAdicSystems I)) ⟶ idealPowerQuotientAdicTower I K :=
  NatTrans.ofOpSequence (fun e => idealPowerQuotientAdicProjection I K (e + 1)) (by
    intro e
    refine NatTrans.ext (funext fun F => ?_)
    refine Eq.trans (Category.id_comp
      ((idealPowerQuotientAdicProjection I K (e + 1)).app F)) ?_
    refine Eq.trans (idealPowerQuotientAdicProjection_drop I K (Nat.le_succ (e + 1)) F).symm ?_
    exact congrArg (fun φ : idealPowerQuotientAdicFunctor I K (e + 1 + 1) ⟶
        idealPowerQuotientAdicFunctor I K (e + 1) =>
      (idealPowerQuotientAdicProjection I K (e + 1 + 1)).app F ≫ φ.app F)
      (idealPowerQuotientAdicTower_map_succ I K e).symm)

/-! ### The terms of a coherent adic system -/

/-- **The terms of a coherent adic system, as a tower of coherent modules.** A coherent adic
system is an inverse system of sheaves of modules all of whose terms happen to be coherent; this
records that datum as an inverse system in `Coh(𝒪_X)`. -/
public def coherentAdicTerms :
    CoherentAdicSystems I ⥤
      (ℕᵒᵖ ⥤ AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) where
  obj F :=
    { obj n := ⟨F.obj.obj n, F.property.isCoherent n.unop⟩
      map g := ObjectProperty.homMk (F.obj.map g)
      map_id n := ObjectProperty.hom_ext _ (F.obj.map_id n)
      map_comp g g' := ObjectProperty.hom_ext _ (F.obj.map_comp g g') }
  map φ :=
    { app n := ObjectProperty.homMk (φ.hom.app n)
      naturality _ _ g := ObjectProperty.hom_ext _ (φ.hom.naturality g) }

/-- **Passing to the terms is fully faithful.** -/
public def coherentAdicTermsFullyFaithful : (coherentAdicTerms I).FullyFaithful where
  preimage φ := ObjectProperty.homMk
    { app n := (φ.app n).hom
      naturality _ _ g := congrArg (fun ψ => ψ.hom) (φ.naturality g) }
  map_preimage _ := NatTrans.ext (funext fun _ => ObjectProperty.hom_ext _ rfl)
  preimage_map _ := ObjectProperty.hom_ext (IsCoherentAdicSystem I) rfl

/-! ### Completion exchanges the two towers -/

section Exchange

variable (H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- The tower of terms of the `𝒦`-completion of a coherent module `H`, as a tower of coherent
modules: the term `e` is `H / 𝒦 ᵉ⁺¹ H`. -/
public abbrev completionTermTower :
    ℕᵒᵖ ⥤ AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
  (coherentAdicTerms K).obj ((completionFunctor X K).obj H)

/-- The `e`-th term of the `𝒦`-completion of `H` *is* the quotient `H / 𝒦 ᵉ⁺¹ H`, by
`Stacks.Algebraization.completionFunctor_obj`. -/
public def coherentCompletionTermIso (e : ℕ) :
    coherentIdealPowerQuotient K H (e + 1) ≅ (completionTermTower K H).obj (op e) :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (eqToIso (completionFunctor_obj X K H e).symm)

/-- The projection of `H` onto the `e`-th term of its `𝒦`-completion, as a morphism of coherent
modules. -/
public def coherentCompletionProjection (e : ℕ) : H ⟶ (completionTermTower K H).obj (op e) :=
  ObjectProperty.homMk (completionProjection X K H e)

/-- The quotient projection factors the identification of the term with the quotient. -/
public theorem cokernel_π_comp_coherentCompletionTermIso (e : ℕ) :
    cokernel.π (C := X.Modules) (idealPowerMultiple K (e + 1) H.obj).ι ≫
        (coherentCompletionTermIso K H e).hom.hom =
      completionProjection X K H e := rfl

/-- **Completion along `ℐ` exchanges the two towers, termwise.** The `𝒦 ᵉ⁺¹`-reduction of the
`ℐ`-completion of `H` is the `ℐ`-completion of `H / 𝒦 ᵉ⁺¹ H`.

This is `Stacks.Coherent.completionIdealPowerQuotientSystemIso` read backwards, followed by the
identification of `H / 𝒦 ᵉ⁺¹ H` with the `e`-th term of the `𝒦`-completion of `H`. -/
public def completionQuotientTowerTermIso (e : ℕ) :
    (idealPowerQuotientAdicFunctor I K (e + 1)).obj ((completionFunctor X I).obj H) ≅
      (completionFunctor X I).obj ((completionTermTower K H).obj (op e)) :=
  (ObjectProperty.isoMk (IsCoherentAdicSystem I)
      (completionIdealPowerQuotientSystemIso I K H (e + 1))).symm ≪≫
    (completionFunctor X I).mapIso (coherentCompletionTermIso K H e)

/-- **The exchange is normalized by the projections.** -/
public theorem idealPowerQuotientAdicProjection_comp_completionQuotientTowerTermIso (e : ℕ) :
    (idealPowerQuotientAdicProjection I K (e + 1)).app ((completionFunctor X I).obj H) ≫
        (completionQuotientTowerTermIso I K H e).hom =
      (completionFunctor X I).map (coherentCompletionProjection K H e) := by
  refine ObjectProperty.hom_ext (IsCoherentAdicSystem I) (NatTrans.ext (funext fun n => ?_))
  refine (Stacks.Algebraization.epi_completionProjection X I H n.unop).left_cancellation
    _ _ ?_
  have hterm := completionIdealPowerQuotientTermIso_projection I K H (e + 1) n.unop
  have hmapT := completionFunctor_map_quotient X I (coherentCompletionTermIso K H e).hom n.unop
  have hmapP := completionFunctor_map_quotient X I (coherentCompletionProjection K H e) n.unop
  have hcancel : completionProjection X I (coherentIdealPowerQuotient K H (e + 1)) n.unop ≫
      ((completionIdealPowerQuotientTermIso I K H (e + 1) n.unop).hom ≫
        (completionIdealPowerQuotientTermIso I K H (e + 1) n.unop).inv) =
      completionProjection X I (coherentIdealPowerQuotient K H (e + 1)) n.unop :=
    (congrArg (fun z => completionProjection X I
      (coherentIdealPowerQuotient K H (e + 1)) n.unop ≫ z)
        (completionIdealPowerQuotientTermIso I K H (e + 1) n.unop).hom_inv_id).trans
      (Category.comp_id _)
  have hleft : completionProjection X I H n.unop ≫
      (((idealPowerQuotientAdicProjection I K (e + 1)).app
          ((completionFunctor X I).obj H)).hom.app n ≫
        (completionQuotientTowerTermIso I K H e).hom.hom.app n) =
      completionProjection X K H e ≫
        completionProjection X I ((completionTermTower K H).obj (op e)) n.unop := by
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫
      (completionQuotientTowerTermIso I K H e).hom.hom.app n) hterm.symm) ?_
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _) ?_
    refine Eq.trans (congrArg (fun z => cokernel.π (C := X.Modules)
      (idealPowerMultiple K (e + 1) H.obj).ι ≫ z)
        (Category.assoc (obj := X.Modules) _ _ _)) ?_
    refine Eq.trans (congrArg (fun z => cokernel.π (C := X.Modules)
      (idealPowerMultiple K (e + 1) H.obj).ι ≫
        completionProjection X I (coherentIdealPowerQuotient K H (e + 1)) n.unop ≫ z)
      (Category.assoc (obj := X.Modules) _ _ _).symm) ?_
    refine Eq.trans (congrArg (fun z => cokernel.π (C := X.Modules)
      (idealPowerMultiple K (e + 1) H.obj).ι ≫ z)
        (Category.assoc (obj := X.Modules) _ _ _).symm) ?_
    refine Eq.trans (congrArg (fun z => cokernel.π (C := X.Modules)
      (idealPowerMultiple K (e + 1) H.obj).ι ≫ z ≫
        ((completionFunctor X I).map
          (coherentCompletionTermIso K H e).hom).hom.app n) hcancel) ?_
    refine Eq.trans (congrArg (fun z => cokernel.π (C := X.Modules)
      (idealPowerMultiple K (e + 1) H.obj).ι ≫ z) hmapT) ?_
    exact (Category.assoc (obj := X.Modules) _ _ _).symm
  refine hleft.trans ?_
  exact hmapP.symm

/-- The projections onto the terms of the `𝒦`-completion are compatible with its transitions. -/
public theorem coherentCompletionProjection_transition (e : ℕ) :
    coherentCompletionProjection K H (e + 1) ≫
        (completionTermTower K H).map (homOfLE (Nat.le_add_right e 1)).op =
      coherentCompletionProjection K H e :=
  ObjectProperty.hom_ext _ (completionProjection_transition X K H e)

/-- **Completion along `ℐ` exchanges the two towers.** The tower of `𝒦`-power reductions of the
`ℐ`-completion of `H` is the tower of `ℐ`-completions of the terms of the `𝒦`-completion of `H`.

The terms are `Stacks.Coherent.completionQuotientTowerTermIso`; naturality is forced by the
normalization of both sides by the quotient projections, which are epimorphisms, together with
the compatibility of the completion projections with the transitions. -/
public def completionQuotientTowerIso :
    idealPowerQuotientAdicTower I K ⋙
        (evaluation _ _).obj ((completionFunctor X I).obj H) ≅
      completionTermTower K H ⋙ completionFunctor X I := by
  have hnat : ∀ e : ℕ,
      (idealPowerQuotientAdicTower I K ⋙
            (evaluation _ _).obj ((completionFunctor X I).obj H)).map
          (homOfLE (Nat.le_add_right e 1)).op ≫
            (completionQuotientTowerTermIso I K H e).hom =
        (completionQuotientTowerTermIso I K H (e + 1)).hom ≫
          (completionTermTower K H ⋙ completionFunctor X I).map
            (homOfLE (Nat.le_add_right e 1)).op := by
    intro e
    have hdrop : (idealPowerQuotientAdicProjection I K (e + 1 + 1)).app
          ((completionFunctor X I).obj H) ≫
        ((idealPowerQuotientAdicTower I K).map
          (homOfLE (Nat.le_add_right e 1)).op).app ((completionFunctor X I).obj H) =
        (idealPowerQuotientAdicProjection I K (e + 1)).app
          ((completionFunctor X I).obj H) :=
      (congrArg (fun φ : idealPowerQuotientAdicFunctor I K (e + 1 + 1) ⟶
            idealPowerQuotientAdicFunctor I K (e + 1) =>
          (idealPowerQuotientAdicProjection I K (e + 1 + 1)).app
              ((completionFunctor X I).obj H) ≫ φ.app ((completionFunctor X I).obj H))
        (idealPowerQuotientAdicTower_map_succ I K e)).trans
        (idealPowerQuotientAdicProjection_drop I K (Nat.le_succ (e + 1))
          ((completionFunctor X I).obj H))
    have hleft : (idealPowerQuotientAdicProjection I K (e + 1 + 1)).app
          ((completionFunctor X I).obj H) ≫
        ((idealPowerQuotientAdicTower I K ⋙
              (evaluation _ _).obj ((completionFunctor X I).obj H)).map
            (homOfLE (Nat.le_add_right e 1)).op ≫
          (completionQuotientTowerTermIso I K H e).hom) =
        (completionFunctor X I).map (coherentCompletionProjection K H e) :=
      (Category.assoc (obj := CoherentAdicSystems I) _ _ _).symm.trans
        ((congrArg (fun z => z ≫ (completionQuotientTowerTermIso I K H e).hom) hdrop).trans
          (idealPowerQuotientAdicProjection_comp_completionQuotientTowerTermIso I K H e))
    have hright : (idealPowerQuotientAdicProjection I K (e + 1 + 1)).app
          ((completionFunctor X I).obj H) ≫
        ((completionQuotientTowerTermIso I K H (e + 1)).hom ≫
          (completionTermTower K H ⋙ completionFunctor X I).map
            (homOfLE (Nat.le_add_right e 1)).op) =
        (completionFunctor X I).map (coherentCompletionProjection K H e) :=
      (Category.assoc (obj := CoherentAdicSystems I) _ _ _).symm.trans
        ((congrArg (fun z => z ≫ (completionTermTower K H ⋙ completionFunctor X I).map
              (homOfLE (Nat.le_add_right e 1)).op)
            (idealPowerQuotientAdicProjection_comp_completionQuotientTowerTermIso
              I K H (e + 1))).trans
          (((completionFunctor X I).map_comp _ _).symm.trans
            (congrArg (completionFunctor X I).map
              (coherentCompletionProjection_transition K H e))))
    have hepi : Epi ((idealPowerQuotientAdicProjection I K (e + 1 + 1)).app
        ((completionFunctor X I).obj H)) := by
      have : ∀ n : ℕᵒᵖ, Epi (((ObjectProperty.ι (IsCoherentAdicSystem I)).map
          ((idealPowerQuotientAdicProjection I K (e + 1 + 1)).app
            ((completionFunctor X I).obj H))).app n) := fun n =>
        epi_cokernel_π_submodule_ι
          (idealPowerMultiple K (e + 1 + 1)
            (((completionFunctor X I).obj H).obj.obj n))
      exact (ObjectProperty.ι (IsCoherentAdicSystem I)).epi_of_epi_map
        (NatTrans.epi_of_epi_app _)
    exact hepi.left_cancellation _ _ (hleft.trans hright.symm)
  exact NatIso.ofComponents (fun e => completionQuotientTowerTermIso I K H e.unop)
    (fun g => (NatTrans.ofOpSequence
      (F := idealPowerQuotientAdicTower I K ⋙
        (evaluation _ _).obj ((completionFunctor X I).obj H))
      (G := completionTermTower K H ⋙ completionFunctor X I)
      (fun e => (completionQuotientTowerTermIso I K H e).hom) hnat).naturality g)

end Exchange


end Stacks.Coherent

end
