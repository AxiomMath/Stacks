module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapHelpers
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.BaseChangeEquivalence
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.ExistenceData

/-!
# Functoriality of specialization maps in a commutative square

Let
```
Y ⟶ X
↓     ↓
T ⟶ S
```
be a commutative square of schemes in which both vertical morphisms are proper with
geometrically connected fibres, and let `t' ⇝ t` be a specialization of points of `T`. A
geometric point `t̄` of `T` has an image `s̄ = t̄ ∘ (T ⟶ S)` in `S`, and the square induces a
morphism `Y_{t̄} ⟶ X_{s̄}` of geometric fibres. Then every specialization map
`π₁(Y_{t̄'}) → π₁(Y_{t̄})` is accompanied by a specialization map `π₁(X_{s̄'}) → π₁(X_{s̄})`
making the square of fundamental groups commute.

The strict henselization `B` of `𝒪_{T,t}` used to build the upper specialization map, and the
strict henselization `A` of `𝒪_{S,s}`, are related by a ring map `A → B` over `𝒪_{S,s} → 𝒪_{T,t}`
because the residue field of `A` is a separable closure of `κ(s)` and that of `B` is a separably
closed field over it; this is the functoriality of the strict henselization, Stacks 04GU. The
geometric point `s̄'` is factored through `Spec A` as the composite `t̄' ⟶ Spec B ⟶ Spec A`, and
base change then produces the commuting square of geometric fibres from which the square of
fundamental groups follows.

## Main definitions

* `AlgebraicGeometry.fiberOverGeometricPointSquareMap` — the morphism of geometric fibres
  determined by a commutative square of schemes.

## Main results

* `AlgebraicGeometry.exists_isSpecializationMap_of_square` — the induced specialization map on
  the bottom row, together with the commutativity of the resulting square of étale fundamental
  groups.

## Implementation notes

As in `StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMap`, geometric base points
are explicit: the base points of the lower fibres are the images of those of the upper fibres,
and the base-point change needed to compare the two descriptions of a fundamental group is
carried by a fibre-functor isomorphism inside
`AlgebraicGeometry.IsSpecializationMap`.

One input is taken as a hypothesis rather than proved, because this library cannot prove it:
that base change along the inclusion of the closed geometric fibre `X_{s̄} ⟶ X ×_S Spec C` is an
equivalence on finite étale covers, for a strictly henselian local ring `C` over `S` through
whose closed point the geometric point `s̄` factors. That is Stacks 0A48 together with Stacks
0A49 and 0BTW, and
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.ClosedGeometricFibre` reduces it to the
essential-surjectivity half of Stacks 0GS2, which
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperEquivalence` leaves open. It is
an input to the *construction* of a specialization map (Stacks 0BUP), and the corresponding
datum on the upper row is already part of `AlgebraicGeometry.IsSpecializationMap`, so it
constrains none of the data this lemma quantifies over.

## References

* [Stacks Project, Tag 0C0K](https://stacks.math.columbia.edu/tag/0C0K)
* [Stacks Project, Tag 04GU](https://stacks.math.columbia.edu/tag/04GU)
* [Stacks Project, Tag 0BUP](https://stacks.math.columbia.edu/tag/0BUP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### Connectedness of a proper family over a local ring -/

/-! ### Functoriality of the strict henselization, in algebra -/

/-- A local ring map `R → T` sends `r` to the image of `r` in the residue field of `T`, computed
by the induced map of residue fields. -/
private theorem algebraMap_residue_algebraMap_eq_map {R T : Type u} [CommRing R] [CommRing T]
    [IsLocalRing R] [IsLocalRing T] [Algebra R T] [IsLocalHom (algebraMap R T)] (r : R) :
    algebraMap (ResidueField T) (maximalIdeal T).ResidueField (residue T (algebraMap R T r))
      = Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal T) (algebraMap R T)
          (IsLocalRing.maximalIdeal_comap (algebraMap R T)).symm
          (algebraMap R (maximalIdeal R).ResidueField r) := by
  rw [← IsLocalRing.ResidueField.algebraMap_eq (R := T),
    ← IsScalarTower.algebraMap_apply T (ResidueField T) (maximalIdeal T).ResidueField
      (algebraMap R T r)]
  exact (Ideal.ResidueField.map_algebraMap (maximalIdeal R) (maximalIdeal T)
    (algebraMap R T) (IsLocalRing.maximalIdeal_comap (algebraMap R T)).symm r).symm

/-- **Functoriality of the strict henselization** (Stacks 04GU), between strict henselizations
taken with respect to the chosen separable closures of the two residue fields: a local
homomorphism `R → S` of local rings induces a local `R`-algebra map `Rsh → Ssh`. The residue
field map is the lift of the separable closure of `κ(R)` into the separably closed field
`κ(Ssh)`, and the algebra map is then
`HenselianLocalRing.indEtaleAlgHomOfResidue`. -/
private theorem exists_algHom_isLocalHom_of_isStrictHenselization
    {R S Rsh Ssh : Type u} [CommRing R] [CommRing S] [CommRing Rsh] [CommRing Ssh]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing Rsh] [IsLocalRing Ssh]
    (φ : R →+* S) [IsLocalHom φ]
    [Algebra R S] [Algebra R Rsh] [Algebra S Ssh] [Algebra R Ssh]
    [IsScalarTower R S Ssh] (hφ : φ = algebraMap R S)
    (hR : Stacks.StrictHenselization.IsStrictHenselization R
      (SeparableClosure (maximalIdeal R).ResidueField) Rsh)
    (hS : Stacks.StrictHenselization.IsStrictHenselization S
      (SeparableClosure (maximalIdeal S).ResidueField) Ssh) :
    ∃ ψ : Rsh →ₐ[R] Ssh, IsLocalHom ψ := by
  classical
  let κR := (maximalIdeal R).ResidueField
  let κS := (maximalIdeal S).ResidueField
  let KR := SeparableClosure κR
  let KS := SeparableClosure κS
  let _ : IsLocalHom (algebraMap R Rsh) := hR.isLocalHom
  let _ : IsLocalHom (algebraMap S Ssh) := hS.isLocalHom
  let φRes : κR →+* κS := Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) φ
    (IsLocalRing.maximalIdeal_comap φ).symm
  let _ : Algebra κR KS := (RingHom.comp (algebraMap κS KS) φRes).toAlgebra
  let _ : IsSepClosed KS := IsSepClosure.sep_closed κS
  let χ : KR →ₐ[κR] KS := IsSepClosed.lift
  let eR : ResidueField Rsh ≃+* KR :=
    (residueFieldEquivMaximalIdealResidueField Rsh).trans hR.residueFieldEquiv.symm
  let eS : KS ≃+* ResidueField Ssh :=
    hS.residueFieldEquiv.trans (residueFieldEquivMaximalIdealResidueField Ssh).symm
  let δ : ResidueField Rsh →+* ResidueField Ssh :=
    eS.toRingHom.comp (χ.toRingHom.comp eR.toRingHom)
  have hResR (r : R) : algebraMap (ResidueField R) κR (residue R r) = algebraMap R κR r := by
    simpa only [IsLocalRing.ResidueField.algebraMap_eq] using
      (IsScalarTower.algebraMap_apply R (ResidueField R) κR r).symm
  have hResS (s : S) : algebraMap (ResidueField S) κS (residue S s) = algebraMap S κS s := by
    simpa only [IsLocalRing.ResidueField.algebraMap_eq] using
      (IsScalarTower.algebraMap_apply S (ResidueField S) κS s).symm
  have hδ : δ.comp ((residue Rsh).comp (algebraMap R Rsh))
      = (residue Ssh).comp (algebraMap R Ssh) := by
    let upR := residueFieldEquivMaximalIdealResidueField Rsh
    let upS := residueFieldEquivMaximalIdealResidueField Ssh
    have hRbase (r : R) : eR (residue Rsh (algebraMap R Rsh r))
        = algebraMap κR KR (algebraMap (ResidueField R) κR (residue R r)) := by
      have hcompat := DFunLike.congr_fun hR.residueFieldEquiv_comp
        (algebraMap (ResidueField R) κR (residue R r))
      rw [hResR] at hcompat
      apply hR.residueFieldEquiv.injective
      calc hR.residueFieldEquiv (eR (residue Rsh (algebraMap R Rsh r)))
          = upR (residue Rsh (algebraMap R Rsh r)) := by
            change hR.residueFieldEquiv (hR.residueFieldEquiv.symm
              (upR (residue Rsh (algebraMap R Rsh r)))) = _
            exact RingEquiv.apply_symm_apply _ _
        _ = Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Rsh) (algebraMap R Rsh)
              (IsLocalRing.maximalIdeal_comap (algebraMap R Rsh)).symm
                (algebraMap R κR r) := algebraMap_residue_algebraMap_eq_map r
        _ = hR.residueFieldEquiv (algebraMap κR KR
              (algebraMap (ResidueField R) κR (residue R r))) := hcompat.symm
    have hSbase (s : S) :
        eS (algebraMap κS KS (algebraMap (ResidueField S) κS (residue S s)))
          = residue Ssh (algebraMap S Ssh s) := by
      have hcompat := DFunLike.congr_fun hS.residueFieldEquiv_comp
        (algebraMap (ResidueField S) κS (residue S s))
      rw [hResS] at hcompat
      apply upS.injective
      calc upS (eS (algebraMap κS KS (algebraMap (ResidueField S) κS (residue S s))))
          = hS.residueFieldEquiv
              (algebraMap κS KS (algebraMap (ResidueField S) κS (residue S s))) := by
            simp [eS, upS]
        _ = Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal Ssh) (algebraMap S Ssh)
              (IsLocalRing.maximalIdeal_comap (algebraMap S Ssh)).symm
                (algebraMap S κS s) := hcompat
        _ = upS (residue Ssh (algebraMap S Ssh s)) :=
            (algebraMap_residue_algebraMap_eq_map s).symm
    ext r
    change eS (χ (eR (residue Rsh (algebraMap R Rsh r)))) = residue Ssh (algebraMap R Ssh r)
    rw [hRbase, χ.commutes]
    have hfr : φRes (algebraMap (ResidueField R) κR (residue R r))
        = algebraMap (ResidueField S) κS (residue S (φ r)) := by
      rw [hResR, Ideal.ResidueField.map_algebraMap, ← hResS]
    rw [show algebraMap κR KS (algebraMap (ResidueField R) κR (residue R r))
      = algebraMap κS KS (φRes (algebraMap (ResidueField R) κR (residue R r))) from rfl,
      hfr, hSbase]
    congr 1
    rw [IsScalarTower.algebraMap_apply R S Ssh r, hφ]
  let _ : HenselianLocalRing Ssh := hS.henselian
  exact ⟨HenselianLocalRing.indEtaleAlgHomOfResidue hR.isFilteredColimitEtale δ hδ,
    HenselianLocalRing.isLocalHom_indEtaleAlgHomOfResidue hR.isFilteredColimitEtale δ hδ⟩

/-! ### The morphism of geometric fibres determined by a commutative square -/

variable {Y X T S : Scheme.{u}}

/-- The morphism of geometric fibres determined by a commutative square: for a commutative
square with `a : Y ⟶ X` on top, `g : Y ⟶ T` and `f : X ⟶ S` vertical and `b : T ⟶ S` on the
bottom, and a geometric point `t` of `T`, the morphism `Y_t ⟶ X_{t ∘ b}`. -/
def fiberOverGeometricPointSquareMap (a : Y ⟶ X) (g : Y ⟶ T) (f : X ⟶ S) (b : T ⟶ S)
    (hab : a ≫ f = g ≫ b) (t : GeometricPoint T) :
    fiberOverGeometricPoint g t ⟶ fiberOverGeometricPoint f (t.map b) :=
  pullback.lift (pullback.fst g t.hom ≫ a) (pullback.snd g t.hom) (by
    calc (pullback.fst g t.hom ≫ a) ≫ f
        = (pullback.fst g t.hom ≫ g) ≫ b := by rw [Category.assoc, hab, ← Category.assoc]
      _ = (pullback.snd g t.hom ≫ t.hom) ≫ b := by rw [pullback.condition]
      _ = pullback.snd g t.hom ≫ (t.map b).hom := by
          rw [Category.assoc]; rfl)

/-! ### Base-point bookkeeping across a commutative square -/

/-- The identification of the two geometric fibre functors attached to the two ways around a
commutative square. -/
private def fiberFunctorSquareIso {A B : Scheme.{u}} (α : Y ⟶ A) (k : Y ⟶ X) (l : A ⟶ B)
    (β : X ⟶ B) (e : α ≫ l = k ≫ β) (y : GeometricPoint Y) :
    finiteEtaleFiberFunctor ((y.map α).map l) ≅ finiteEtaleFiberFunctor ((y.map k).map β) :=
  (fiberFunctorMapCompIso α l y).symm ≪≫
    eqToIso (congrArg finiteEtaleFiberFunctor (congrArg (y.map ·) e)) ≪≫
      fiberFunctorMapCompIso k β y

/-- Transport along the identification of two equal morphisms carries one induced map to the
other. -/
private theorem etaleFundamentalGroupMulEquiv_eqToIso_congr [ConnectedSpace X]
    [ConnectedSpace S] {u v : X ⟶ S} (e : u = v) (x : GeometricPoint X)
    (σ : EtaleFundamentalGroup X x) :
    etaleFundamentalGroupMulEquiv
        (eqToIso (congrArg finiteEtaleFiberFunctor (congrArg (x.map ·) e)))
        (etaleFundamentalGroupMap u x σ)
      = etaleFundamentalGroupMap v x σ := by
  subst e
  exact etaleFundamentalGroupMulEquiv_refl _

/-- Going around a commutative square either way induces the same map on fundamental groups,
compared through `AlgebraicGeometry.fiberFunctorSquareIso`. -/
private theorem etaleFundamentalGroupMulEquiv_squareIso {A B : Scheme.{u}} [ConnectedSpace Y]
    [ConnectedSpace X] [ConnectedSpace A] [ConnectedSpace B] (α : Y ⟶ A) (k : Y ⟶ X)
    (l : A ⟶ B) (β : X ⟶ B) (e : α ≫ l = k ≫ β) (y : GeometricPoint Y)
    (σ : EtaleFundamentalGroup Y y) :
    etaleFundamentalGroupMulEquiv (fiberFunctorSquareIso α k l β e y)
        (etaleFundamentalGroupMap l (y.map α) (etaleFundamentalGroupMap α y σ))
      = etaleFundamentalGroupMap β (y.map k) (etaleFundamentalGroupMap k y σ) := by
  rw [fiberFunctorSquareIso, etaleFundamentalGroupMulEquiv_trans,
    etaleFundamentalGroupMulEquiv_trans, ← etaleFundamentalGroupMulEquiv_mapCompIso,
    etaleFundamentalGroupMulEquiv_symm_apply_apply,
    etaleFundamentalGroupMulEquiv_eqToIso_congr e,
    etaleFundamentalGroupMulEquiv_mapCompIso]

/-- The square of fundamental groups, in the form needed for the specialization maps: given the
defining equation of a specialization map on the upper row of a commutative square of base
changes, there is a continuous homomorphism on the lower row satisfying the corresponding
defining equation and making the square of induced maps commute. -/
private theorem exists_fiberFunctorIso_square {Y₀ Y₁ X₀ X₁ A B : Scheme.{u}}
    [ConnectedSpace Y₀] [ConnectedSpace Y₁] [ConnectedSpace X₀] [ConnectedSpace X₁]
    [ConnectedSpace A] [ConnectedSpace B]
    (α₀ : Y₀ ⟶ A) (α₁ : Y₁ ⟶ A) (β₀ : X₀ ⟶ B) (β₁ : X₁ ⟶ B)
    (k₀ : Y₀ ⟶ X₀) (k₁ : Y₁ ⟶ X₁) (l : A ⟶ B)
    (e₀ : α₀ ≫ l = k₀ ≫ β₀) (e₁ : α₁ ≫ l = k₁ ≫ β₁)
    (y₀ : GeometricPoint Y₀) (y₁ : GeometricPoint Y₁)
    [(finiteEtaleBaseChange α₁).IsEquivalence] [(finiteEtaleBaseChange β₁).IsEquivalence]
    (t : finiteEtaleFiberFunctor (y₀.map α₀) ≅ finiteEtaleFiberFunctor (y₁.map α₁))
    (h : EtaleFundamentalGroup Y₀ y₀ →ₜ* EtaleFundamentalGroup Y₁ y₁)
    (hh : ∀ σ, etaleFundamentalGroupMap α₁ y₁ (h σ)
      = etaleFundamentalGroupMulEquiv t (etaleFundamentalGroupMap α₀ y₀ σ)) :
    ∃ (tB : finiteEtaleFiberFunctor ((y₀.map k₀).map β₀) ≅
        finiteEtaleFiberFunctor ((y₁.map k₁).map β₁))
      (h' : EtaleFundamentalGroup X₀ (y₀.map k₀) →ₜ* EtaleFundamentalGroup X₁ (y₁.map k₁)),
      (∀ σ, etaleFundamentalGroupMap β₁ (y₁.map k₁) (h' σ)
        = etaleFundamentalGroupMulEquiv tB (etaleFundamentalGroupMap β₀ (y₀.map k₀) σ)) ∧
      ∀ γ, etaleFundamentalGroupMap k₁ y₁ (h γ) = h' (etaleFundamentalGroupMap k₀ y₀ γ) := by
  obtain ⟨tB, htB⟩ : ∃ tB : finiteEtaleFiberFunctor ((y₀.map k₀).map β₀) ≅
      finiteEtaleFiberFunctor ((y₁.map k₁).map β₁),
      tB = (fiberFunctorSquareIso α₀ k₀ l β₀ e₀ y₀).symm ≪≫ fiberFunctorTransportIso l t ≪≫
        fiberFunctorSquareIso α₁ k₁ l β₁ e₁ y₁ := ⟨_, rfl⟩
  have hprop : ∀ σ, etaleFundamentalGroupMap β₁ (y₁.map k₁)
      (((ContinuousMonoidHom.toContinuousMonoidHom
          (etaleFundamentalGroupContinuousMulEquivOfIsEquivalence β₁ (y₁.map k₁)).symm).comp
        ((ContinuousMonoidHom.toContinuousMonoidHom
          (etaleFundamentalGroupContinuousMulEquiv tB)).comp
            (etaleFundamentalGroupMap β₀ (y₀.map k₀)))) σ)
      = etaleFundamentalGroupMulEquiv tB (etaleFundamentalGroupMap β₀ (y₀.map k₀) σ) := by
    intro σ
    change etaleFundamentalGroupMap β₁ (y₁.map k₁)
      ((etaleFundamentalGroupMulEquivOfIsEquivalence β₁ (y₁.map k₁)).symm
        (etaleFundamentalGroupMulEquiv tB (etaleFundamentalGroupMap β₀ (y₀.map k₀) σ))) = _
    rw [← etaleFundamentalGroupMulEquivOfIsEquivalence_apply]
    exact (etaleFundamentalGroupMulEquivOfIsEquivalence β₁ (y₁.map k₁)).apply_symm_apply _
  refine ⟨tB, _, hprop, fun γ ↦ ?_⟩
  apply (etaleFundamentalGroupMulEquivOfIsEquivalence β₁ (y₁.map k₁)).injective
  rw [etaleFundamentalGroupMulEquivOfIsEquivalence_apply,
    etaleFundamentalGroupMulEquivOfIsEquivalence_apply, hprop,
    ← etaleFundamentalGroupMulEquiv_squareIso α₁ k₁ l β₁ e₁ y₁ (h γ), hh,
    ← etaleFundamentalGroupMulEquiv_transportIso l t,
    ← etaleFundamentalGroupMulEquiv_squareIso α₀ k₀ l β₀ e₀ y₀ γ, htB,
    etaleFundamentalGroupMulEquiv_trans, etaleFundamentalGroupMulEquiv_trans,
    etaleFundamentalGroupMulEquiv_symm_apply_apply]

/-! ### Specialization maps in a commutative square -/

/-- **Stacks Project, Tag 0C0K.** Consider a commutative square of schemes with `a : Y ⟶ X` on
top, `g : Y ⟶ T` and `f : X ⟶ S` vertical and `b : T ⟶ S` on the bottom, where `f` and `g` are
proper with geometrically connected fibres. Let `t'` and `t` be geometric points of `T` and let
`sp : π₁(Y_{t'}) → π₁(Y_t)` be a specialization map. Then there is a specialization map
`π₁(X_{s'}) → π₁(X_s)`, where `s'` and `s` are the images of `t'` and `t` in `S`, making the
square of maps induced by the morphisms `Y_{t'} ⟶ X_{s'}` and `Y_t ⟶ X_s` of geometric fibres
commute. -/
@[stacks 0C0K "the whole statement — the specialization map on the bottom row and the \
commutativity of the square of fundamental groups — granted the one input this library cannot \
prove, carried as the hypothesis `hclosedFibre`: that base change along the inclusion of the \
closed geometric fibre `X_s ⟶ X ×_S Spec C` is an equivalence on finite étale covers, for a \
strictly henselian local ring `C` over `S` through whose closed point `s` factors. That is \
Stacks 0A48 with 0A49 and 0BTW; \
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.ClosedGeometricFibre` reduces it to the \
essential-surjectivity half of Stacks 0GS2, left open by \
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperEquivalence`. It is an input to \
the construction of a specialization map (Stacks 0BUP) — the same datum for the upper row is \
part of `AlgebraicGeometry.IsSpecializationMap` — and it restricts nothing about `a`, `b`, the \
specialization `t' ⤳ t` or the schemes. Everything else is proved here: the strict \
henselization `A` of the stalk at the image of `t`, the ring map `A → B` of Stacks 04GU, the \
factorizations of the two geometric points of `S` through `Spec A`, connectedness of `X_A`, and \
the base-point bookkeeping."]
theorem exists_isSpecializationMap_of_square (a : Y ⟶ X) (g : Y ⟶ T) (f : X ⟶ S) (b : T ⟶ S)
    (hab : a ≫ f = g ≫ b) [IsProper f] [GeometricallyConnected f] [IsProper g]
    [GeometricallyConnected g] (t' t : GeometricPoint T)
    (y' : GeometricPoint (fiberOverGeometricPoint g t'))
    (y : GeometricPoint (fiberOverGeometricPoint g t))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint g t') y' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint g t) y)
    (hsp : IsSpecializationMap g t' t y' y sp)
    (hclosedFibre : ∀ (C : Type u) (_ : CommRing C) (_ : HenselianLocalRing C),
      ∀ (_ : IsSepClosed (ResidueField C)) (r : Spec (.of C) ⟶ S)
        (p : (t.map b).source ⟶ Spec (.of C)) (hp : p ≫ r = (t.map b).hom),
      p (closedPoint (t.map b).residueField) = closedPoint C →
      (finiteEtaleBaseChange
        (fiberOverGeometricPointMap f (t.map b) r p hp)).IsEquivalence) :
    ∃ sp' : EtaleFundamentalGroup (fiberOverGeometricPoint f (t'.map b))
          (y'.map (fiberOverGeometricPointSquareMap a g f b hab t')) →ₜ*
        EtaleFundamentalGroup (fiberOverGeometricPoint f (t.map b))
          (y.map (fiberOverGeometricPointSquareMap a g f b hab t)),
      IsSpecializationMap f (t'.map b) (t.map b)
          (y'.map (fiberOverGeometricPointSquareMap a g f b hab t'))
          (y.map (fiberOverGeometricPointSquareMap a g f b hab t)) sp' ∧
        ∀ γ, etaleFundamentalGroupMap
              (fiberOverGeometricPointSquareMap a g f b hab t) y (sp γ)
          = sp' (etaleFundamentalGroupMap
              (fiberOverGeometricPointSquareMap a g f b hab t') y' γ) := by
  classical
  simp only [IsSpecializationMap] at hsp ⊢
  obtain ⟨B, hBring, hBloc, hBalg, hBsh, q', hq', q, hq, hqclosed, hYBconn, hYBequiv, tf,
    hform⟩ := hsp
  let _ : CommRing B := hBring
  let _ : IsLocalRing B := hBloc
  -- `zT` is the image of the closed point of `t`, `zS` its image in `S`
  let zT : T := t.hom (closedPoint t.residueField)
  let _ : Algebra (T.presheaf.stalk zT) B := hBalg
  let RS := S.presheaf.stalk (b zT)
  let RT := T.presheaf.stalk zT
  let φ : RS →+* RT := (b.stalkMap zT).hom
  let _ : IsLocalHom φ := b.toLRSHom.prop zT
  let _ : Algebra RS RT := φ.toAlgebra
  let _ : Algebra RS B := (RingHom.comp (algebraMap RT B) φ).toAlgebra
  let _ : IsScalarTower RS RT B := .of_algebraMap_eq' (by
    ext r; simp [RingHom.algebraMap_toAlgebra, RingHom.comp_apply])
  -- the strict henselization `A` of the stalk of `S`
  obtain ⟨A, hAring, hAloc, hAalg, hAsh⟩ := Stacks.StrictHenselization.exists_isStrictHenselization
    RS (SeparableClosure (maximalIdeal RS).ResidueField)
  let _ : CommRing A := hAring
  let _ : IsLocalRing A := hAloc
  let _ : Algebra RS A := hAalg
  obtain ⟨hAsh⟩ := hAsh
  obtain ⟨hBsh⟩ := hBsh
  -- the functoriality map `A → B` of Stacks 04GU
  obtain ⟨α, hαloc⟩ := exists_algHom_isLocalHom_of_isStrictHenselization φ rfl hAsh hBsh
  let _ : IsLocalHom α := hαloc
  let _ : IsLocalHom α.toRingHom := isLocalHom_toRingHom α
  let gA : Spec (.of A) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap RS A)) ≫ S.fromSpecStalk (b zT)
  let gB : Spec (.of B) ⟶ T :=
    Spec.map (CommRingCat.ofHom (algebraMap RT B)) ≫ T.fromSpecStalk zT
  let c : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom α.toRingHom)
  have hstalk : Spec.map (CommRingCat.ofHom φ) ≫ S.fromSpecStalk (b zT)
      = T.fromSpecStalk zT ≫ b := Scheme.SpecMap_stalkMap_fromSpecStalk b (x := zT)
  have hbaseA : α.toRingHom.comp (algebraMap RS A) = algebraMap RS B := by
    ext r; exact α.commutes r
  have hbaseB : (algebraMap RT B).comp φ = algebraMap RS B := by
    ext r; simp [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  have htriangle : c ≫ gA = gB ≫ b := by
    have h₁ : Spec.map (CommRingCat.ofHom α.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap RS A))
          = Spec.map (CommRingCat.ofHom (α.toRingHom.comp (algebraMap RS A))) := by
      rw [← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext (by ext r; rfl))
    have h₂ : Spec.map (CommRingCat.ofHom ((algebraMap RT B).comp φ))
        = Spec.map (CommRingCat.ofHom (algebraMap RT B)) ≫ Spec.map (CommRingCat.ofHom φ) := by
      rw [← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext (by ext r; rfl))
    calc c ≫ gA
        = Spec.map (CommRingCat.ofHom (α.toRingHom.comp (algebraMap RS A))) ≫
            S.fromSpecStalk (b zT) := by rw [← Category.assoc, h₁]
      _ = Spec.map (CommRingCat.ofHom ((algebraMap RT B).comp φ)) ≫
            S.fromSpecStalk (b zT) := by rw [hbaseA, hbaseB]
      _ = Spec.map (CommRingCat.ofHom (algebraMap RT B)) ≫
            Spec.map (CommRingCat.ofHom φ) ≫ S.fromSpecStalk (b zT) := by
            rw [h₂, Category.assoc]
      _ = gB ≫ b := by rw [hstalk, ← Category.assoc]
  have hpt (u : GeometricPoint T) (w : u.source ⟶ Spec (.of B)) (hw : w ≫ gB = u.hom) :
      (w ≫ c) ≫ gA = (u.map b).hom := by
    rw [Category.assoc, htriangle, ← Category.assoc, hw]; rfl
  have hp' := hpt t' q' hq'
  have hp := hpt t q hq
  have hpclosed : (q ≫ c) (closedPoint (t.map b).residueField) = closedPoint A := by
    change c (q (closedPoint t.residueField)) = closedPoint A
    rw [hqclosed]
    exact IsLocalRing.comap_closedPoint α.toRingHom
  have hXAconn : ConnectedSpace (pullback f gA : Scheme.{u}) :=
    connectedSpace_pullback_spec_of_isProper f A gA
  let _ : ConnectedSpace (pullback g gB : Scheme.{u}) := hYBconn
  let _ : ConnectedSpace (pullback f gA : Scheme.{u}) := hXAconn
  let _ : HenselianLocalRing A := hAsh.henselian
  let _ : IsSepClosed (maximalIdeal A).ResidueField := hAsh.sepClosed
  let _ : IsSepClosed (ResidueField A) := isSepClosed_residueField_of_maximalIdeal A
  let α₀ := fiberOverGeometricPointMap g t' gB q' hq'
  let α₁ := fiberOverGeometricPointMap g t gB q hq
  let β₀ := fiberOverGeometricPointMap f (t'.map b) gA (q' ≫ c) hp'
  let β₁ := fiberOverGeometricPointMap f (t.map b) gA (q ≫ c) hp
  have hβ₁ : (finiteEtaleBaseChange β₁).IsEquivalence :=
    hclosedFibre A hAring inferInstance inferInstance gA (q ≫ c) hp hpclosed
  let _ := hβ₁
  let _ := hYBequiv
  -- the morphism of base changes induced by the square
  let l : (pullback g gB : Scheme.{u}) ⟶ (pullback f gA : Scheme.{u}) :=
    pullback.lift (pullback.fst g gB ≫ a) (pullback.snd g gB ≫ c) (by
      calc (pullback.fst g gB ≫ a) ≫ f
          = (pullback.fst g gB ≫ g) ≫ b := by rw [Category.assoc, hab, ← Category.assoc]
        _ = (pullback.snd g gB ≫ gB) ≫ b := by rw [pullback.condition]
        _ = pullback.snd g gB ≫ gB ≫ b := Category.assoc _ _ _
        _ = pullback.snd g gB ≫ c ≫ gA :=
            congrArg (pullback.snd g gB ≫ ·) htriangle.symm
        _ = (pullback.snd g gB ≫ c) ≫ gA := (Category.assoc _ _ _).symm)
  have het (u : GeometricPoint T) (w : u.source ⟶ Spec (.of B)) (hw : w ≫ gB = u.hom) :
      fiberOverGeometricPointMap g u gB w hw ≫ l
        = fiberOverGeometricPointSquareMap a g f b hab u ≫
          fiberOverGeometricPointMap f (u.map b) gA (w ≫ c) (hpt u w hw) := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp only [l, fiberOverGeometricPointSquareMap, fiberOverGeometricPointMap,
        Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc]
  obtain ⟨tB, sp', hform', hcomm⟩ := exists_fiberFunctorIso_square α₀ α₁ β₀ β₁
    (fiberOverGeometricPointSquareMap a g f b hab t')
    (fiberOverGeometricPointSquareMap a g f b hab t) l (het t' q' hq') (het t q hq) y' y tf sp hform
  exact ⟨sp', ⟨A, hAring, hAloc, hAalg, ⟨hAsh⟩, q' ≫ c, hp', q ≫ c, hp, hpclosed, hXAconn,
    hβ₁, tB, hform'⟩, hcomm⟩

end AlgebraicGeometry

end
