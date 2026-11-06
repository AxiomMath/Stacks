module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAdicThickeningsBase
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.SpaceTower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChangeConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence

/-!
# Flatness over an affine Noetherian base from flatness along the adic fibres

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal and let `X` be an algebraic space locally
of finite presentation over `S = Spec A`.  For `n ≥ 1` put `S_n = Spec (A / Iⁿ)` and
`X_n = S_n ×_S X`, and let `F` be a coherent `𝒪_X`-module with pullback `F_n` to `X_n`.
Stacks 08VP says that if `F_n` is flat over `S_n` for every `n ≥ 1`, then the locus where `F` is
flat over `S` — which is open by Stacks 05WV — contains the inverse image of `V(I)` under
`X → S`.

The source's proof reduces to `X` affine, which here means reading everything on an étale scheme
chart `U` of `X`.  The chart `U_n = U ×_S S_n` of `X_n` is the base change of `U`, and the
restriction of `F_n` to it is the pullback of the restriction `F|_U` (Stacks 03LU with the base
change of the chart restriction).  At a point of `U_n` over `u ∈ U` the local ring of `U_n` is
`𝒪_{U, u} / Iⁿ 𝒪_{U, u}`, so the stalk of `F_n` there is `M / IⁿM` for `M = (F|_U)_u`, and
flatness over `S_n` there is flatness of `M / IⁿM` over `A / Iⁿ`.  That is the hypothesis of
the chartwise statement `AlgebraicGeometry.Space.preimage_zeroLocus_subset_flatLocus`, where
Stacks 0523 concludes.

## Main definitions

* `AlgebraicGeometry.Space.adicFibreSpace`: the adic fibre `X_n` as an algebraic space, with its
  projection `AlgebraicGeometry.Space.adicFibreFst` to `X` and its structure morphism
  `AlgebraicGeometry.Space.adicFibreSnd` to `S_n`.

## Main results

* `AlgebraicGeometry.ker_stalkMap_pullback_fst_specQuotient`: for `g : X ⟶ Spec A`, the stalk map
  of `X ×_{Spec A} Spec (A / J) ⟶ X` at a point over `x` has kernel `J 𝒪_{X, x}`.
* `AlgebraicGeometry.flat_quotient_of_isFlatOverAt_of_isPullback`: if the pullback of an
  `𝒪_X`-module `F` to `X ×_{Spec A} Spec (A / J)` is flat over `Spec (A / J)` at a point over
  `x`, then `F_x / J F_x` is flat over `A / J`.
* `AlgebraicGeometry.Space.flat_quotient_pow_of_isFlatOver_adicFibre`: the dictionary from
  flatness of `F_n` over `S_n` to the chart stalks.
* `AlgebraicGeometry.Space.preimage_zeroLocus_subset_flatLocus_of_isFlatOver_adicFibre`:
  **Stacks 08VP.**

## Implementation notes

The thickenings are indexed from `0`: for `n : ℕ` the scheme `AlgebraicGeometry.adicThickening`
is `Spec (A / I^{n+1})`, so quantifying over `n : ℕ` is quantifying over the exponents `≥ 1` of
the source.

To form `X_n` the thickenings must be objects of the big fppf site; this is not an extra
hypothesis, `AlgebraicGeometry.Space.contains_adicThickening` deducing it from the membership of
`Spec A`, a closed subscheme being no larger than the scheme containing it.

The fibre product `X_n` is the fibre product of presheaves, which is the fibre product of
algebraic spaces by Stacks 02X2, and the pullback `F_n` is the inverse image of Stacks 03LU,
`AlgebraicGeometry.Space.modulePullback`.  Flatness of `F_n` over `S_n` is
`AlgebraicGeometry.Space.IsFlatOver` of Stacks 05VV, a condition on every commuting square of
étale scheme charts; the proof uses it only on the squares whose chart of `X_n` is the base
change of a chart of `X` and whose chart of `S_n` is `S_n` itself.

Coherence is `AlgebraicGeometry.Space.IsCoherent` of Stacks 07UA.  It gives quasi-coherence and
finite type on the small étale site, hence on the charts, which is what the chartwise statement
and the comparison of chart restrictions with pullbacks consume, and finite presentation on the
charts, which is what the openness of Stacks 05WV consumes.

## References

* [Stacks Project, Tag 08VP](https://stacks.math.columbia.edu/tag/08VP)
* [Stacks Project, Tag 0523](https://stacks.math.columbia.edu/tag/0523)
* [Stacks Project, Tag 05WV](https://stacks.math.columbia.edu/tag/05WV)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe u

namespace AlgebraicGeometry

section Algebra

variable {A O C : Type u} [CommRing A] [CommRing O] [CommRing C]

/-- For an `O`-module `M` on which `A` acts through `ψ : A →+* O`, the submodule `J • M` is
the restriction of scalars of `(J O) • M`. -/
theorem restrictScalars_map_smul_top (ψ : A →+* O) (J : Ideal A) (M : Type*)
    [AddCommGroup M] [Module O M] :
    letI : Algebra A O := ψ.toAlgebra
    letI : Module A M := Module.compHom M ψ
    letI : IsScalarTower A O M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    ((J.map ψ) • (⊤ : Submodule O M)).restrictScalars A = J • (⊤ : Submodule A M) := by
  let : Algebra A O := ψ.toAlgebra
  let : Module A M := Module.compHom M ψ
  let : IsScalarTower A O M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  refine le_antisymm ?_ ?_
  · intro x hx
    change x ∈ (J.map ψ) • (⊤ : Submodule O M) at hx
    refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) fun x y hx hy => add_mem hx hy
    induction hr using Submodule.span_induction generalizing m with
    | mem r hr =>
      obtain ⟨a, ha, rfl⟩ := hr
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    | zero => simp
    | add r s _ _ hr hs =>
      rw [add_smul]
      exact add_mem (hr m trivial) (hs m trivial)
    | smul o r _ hr =>
      rw [smul_eq_mul, mul_comm, mul_smul]
      exact hr (o • m) trivial
  · refine Submodule.smul_le.mpr fun a ha m _ => ?_
    show ψ a • m ∈ (J.map ψ) • (⊤ : Submodule O M)
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem ψ ha) Submodule.mem_top

/-- **Flatness of `M / J M` from flatness of a base change along a quotient.**  Let
`ψ : A →+* O` and let `θ : O →+* C` be surjective with kernel `J O`, so that `C = O / J O`.  For
an `O`-module `M`, if the base change `C ⊗_O M` is flat over `A / J` — through a ring map
`ρ : A / J →+* C` lifting `θ ∘ ψ` — then `M / J M` is flat over `A / J`.

The two modules are the same: `C ⊗_O M = (O / J O) ⊗_O M = M / (J O) M = M / J M`. -/
theorem flat_quotient_smul_top_of_flat_extendScalars (ψ : A →+* O) (θ : O →+* C) (J : Ideal A)
    (hsurj : Function.Surjective θ) (hker : RingHom.ker θ = J.map ψ)
    (ρ : A ⧸ J →+* C) (hρ : ρ.comp (Ideal.Quotient.mk J) = θ.comp ψ) (M : ModuleCat.{u} O)
    (hflat : letI : Module (A ⧸ J) ((ModuleCat.extendScalars θ).obj M) := Module.compHom _ ρ
      Module.Flat (A ⧸ J) ((ModuleCat.extendScalars θ).obj M)) :
    letI : Module A M := Module.compHom M ψ
    Module.Flat (A ⧸ J) (M ⧸ (J • ⊤ : Submodule A M)) := by
  let : Algebra A O := ψ.toAlgebra
  let : Module A M := Module.compHom M ψ
  let : IsScalarTower A O M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module (A ⧸ J) ((ModuleCat.extendScalars θ).obj M) := Module.compHom _ ρ
  let K : Ideal O := J.map ψ
  let r : (O ⧸ K) ≃+* C :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have hr : ∀ o, r (Ideal.Quotient.mk K o) = θ o := fun o => rfl
  let Cr := (ModuleCat.restrictScalars θ).obj (ModuleCat.of C C)
  let e₀ : (O ⧸ K) ≃ₗ[O] Cr :=
    { r.toAddEquiv with
      map_smul' := fun o q => by
        obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective q
        show r (Ideal.Quotient.mk K (o * q)) = θ o * r (Ideal.Quotient.mk K q)
        rw [hr, hr, map_mul] }
  let E : TensorProduct O Cr M ≃ₗ[O] M ⧸ (K • ⊤ : Submodule O M) :=
    TensorProduct.congr e₀.symm (LinearEquiv.refl O M) ≪≫ₗ
      TensorProduct.quotTensorEquivQuotSMul M K
  let G : (M ⧸ (K • ⊤ : Submodule O M)) ≃ₗ[A] M ⧸ (J • ⊤ : Submodule A M) :=
    (Submodule.Quotient.restrictScalarsEquiv A (K • ⊤)).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (restrictScalars_map_smul_top ψ J M)
  have hact : ∀ (o : O) (t : TensorProduct O Cr M),
      (o • t : TensorProduct O Cr M) =
        (θ o • (show ↑((ModuleCat.extendScalars θ).obj M) from t) :
          ↑((ModuleCat.extendScalars θ).obj M)) := by
    intro o t
    induction t using TensorProduct.induction_on with
    | zero =>
      exact (smul_zero o).trans
        (smul_zero (A := ↑((ModuleCat.extendScalars θ).obj M)) (θ o)).symm
    | tmul c m => rfl
    | add x y hx hy =>
      exact (smul_add o x y).trans ((congrArg₂ (· + ·) hx hy).trans
        (smul_add (θ o) (show ↑((ModuleCat.extendScalars θ).obj M) from x) y).symm)
  have hGsmul : ∀ (a : A) (y : M ⧸ (K • ⊤ : Submodule O M)),
      G (ψ a • y) = Ideal.Quotient.mk J a • G y := by
    intro a y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rfl
  let Φ : (ModuleCat.extendScalars θ).obj M ≃ₗ[A ⧸ J] M ⧸ (J • ⊤ : Submodule A M) :=
    { toFun := fun t => G (E t)
      invFun := fun x => E.symm (G.symm x)
      map_add' := fun x y =>
        (congrArg G (E.map_add (show TensorProduct O Cr M from x) y)).trans (G.map_add _ _)
      map_smul' := fun q t => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
        let t' : TensorProduct O Cr M := t
        have h1 : ρ (Ideal.Quotient.mk J a) = θ (ψ a) := RingHom.congr_fun hρ a
        have h2 : (ρ (Ideal.Quotient.mk J a) • t : ↑((ModuleCat.extendScalars θ).obj M)) =
            (ψ a • t' : TensorProduct O Cr M) := by
          rw [h1]
          exact (hact (ψ a) t').symm
        show G (E (ρ (Ideal.Quotient.mk J a) • t)) = Ideal.Quotient.mk J a • G (E t')
        calc G (E (ρ (Ideal.Quotient.mk J a) • t)) = G (E (ψ a • t')) :=
              congrArg (fun z => G (E z)) h2
          _ = G (ψ a • E t') := by rw [E.map_smul]
          _ = Ideal.Quotient.mk J a • G (E t') := hGsmul a (E t')
      left_inv := fun t =>
        (congrArg E.symm (G.symm_apply_apply _)).trans
          (E.symm_apply_apply (show TensorProduct O Cr M from t))
      right_inv := fun x => (congrArg G (E.apply_symm_apply _)).trans (G.apply_symm_apply x) }
  exact Module.Flat.of_linearEquiv Φ.symm

end Algebra

section Scheme

open CategoryTheory.Limits

variable {A : Type u} [CommRing A] (J : Ideal A) {X : Scheme.{u}} (g : X ⟶ Spec (.of A))

/-- The closed immersion `Spec (A / J) ⟶ Spec A`, written `ι[J]`. -/
local notation3 "ι[" J' "]" => Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))

/-- The `R`-algebra structure on the stalk of `Spec R` at a point. -/
private instance stalkAlgebraSpec (R : Type u) [CommRing R] (p : ↥(Spec (.of R))) :
    Algebra R ((Spec (.of R)).presheaf.stalk p) :=
  StructureSheaf.stalkAlgebra R p

/-- The ideal of a point of `Spec R` is prime. -/
private instance isPrime_asIdeal_spec (R : Type u) [CommRing R] (p : ↥(Spec (.of R))) :
    p.asIdeal.IsPrime :=
  p.isPrime

/-- The stalk of `Spec R` at a point is the localization of `R` at that prime. -/
private instance isLocalization_stalkAlgebraSpec (R : Type u) [CommRing R] (p : ↥(Spec (.of R))) :
    IsLocalization.AtPrime ((Spec (.of R)).presheaf.stalk p) p.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk R p

/-- Moving a germ of the structure sheaf of `Spec A` along an equality of points. -/
lemma toStalk_eqToHom_apply {p q : ↥(Spec (.of A))} (h : p = q) (a : A) :
    (eqToHom (congrArg (Spec (.of A)).presheaf.stalk h)).hom
        ((StructureSheaf.toStalk A p).hom a) = (StructureSheaf.toStalk A q).hom a := by
  subst h
  rfl

/-- **The square of local rings of the base change to `Spec (A / J)`.**  At a point `w` of
`X ×_{Spec A} Spec (A / J)`, the two composites `A → A / J → 𝒪_{Spec (A/J), y} → 𝒪_w` and
`A → 𝒪_{X, x} → 𝒪_w` agree, where `x` and `y` are the images of `w`. -/
lemma stalkMap_pullback_snd_toStalk_mk (w : ↑(pullback g ι[J])) (a : A) :
    ((pullback.snd g ι[J]).stalkMap w).hom
        ((StructureSheaf.toStalk (A ⧸ J) ((pullback.snd g ι[J]).base w)).hom
          (Ideal.Quotient.mk J a)) =
      ((pullback.fst g ι[J]).stalkMap w).hom
        ((baseRingStalkHom g ((pullback.fst g ι[J]).base w)).hom a) := by
  have e1 : (StructureSheaf.toStalk (A ⧸ J) ((pullback.snd g ι[J]).base w)).hom
      (Ideal.Quotient.mk J a) = ((ι[J]).stalkMap ((pullback.snd g ι[J]).base w)).hom
        ((StructureSheaf.toStalk A ((ι[J]).base ((pullback.snd g ι[J]).base w))).hom a) :=
    (stalkMap_toStalk_apply (CommRingCat.ofHom (Ideal.Quotient.mk J)) _ a).symm
  have e := Scheme.Hom.stalkMap_congr_hom (pullback.snd g ι[J] ≫ ι[J]) (pullback.fst g ι[J] ≫ g)
    pullback.condition.symm w
  have h0 : (pullback.snd g ι[J] ≫ ι[J]).base w = (pullback.fst g ι[J] ≫ g).base w :=
    congrArg (fun k : pullback g ι[J] ⟶ Spec (.of A) => k.base w)
      (pullback.condition (f := g) (g := ι[J])).symm
  rw [stalkCongr_of_eq _ h0, Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at e
  have e' := congrArg (fun k => k.hom
    ((StructureSheaf.toStalk A ((ι[J]).base ((pullback.snd g ι[J]).base w))).hom a)) e
  rw [e1]
  refine e'.trans ?_
  exact congrArg (fun z => ((pullback.fst g ι[J]).stalkMap w).hom
    ((g.stalkMap ((pullback.fst g ι[J]).base w)).hom z)) (toStalk_eqToHom_apply h0 a)

/-- **The local ring of the base change to `Spec (A / J)` is `𝒪_{X, x} / J 𝒪_{X, x}`**, on the
side of the kernel: the stalk map of the projection to `X` at a point `w` over `x` has kernel
`J 𝒪_{X, x}`. -/
lemma ker_stalkMap_pullback_fst_specQuotient (w : ↑(pullback g ι[J])) :
    RingHom.ker ((pullback.fst g ι[J]).stalkMap w).hom =
      J.map (baseRingStalkHom g ((pullback.fst g ι[J]).base w)).hom := by
  refine le_antisymm ?_ ?_
  · intro o ho
    rw [RingHom.mem_ker] at ho
    let x := (pullback.fst g ι[J]).base w
    let y := (pullback.snd g ι[J]).base w
    let K : Ideal (X.presheaf.stalk x) := J.map (baseRingStalkHom g x).hom
    have h0 : (pullback.fst g ι[J] ≫ g).base w = (pullback.snd g ι[J] ≫ ι[J]).base w :=
      congrArg (fun k : pullback g ι[J] ⟶ Spec (.of A) => k.base w)
        (pullback.condition (f := g) (g := ι[J]))
    let : Algebra ((Spec (.of A)).presheaf.stalk ((pullback.fst g ι[J] ≫ g).base w))
        (X.presheaf.stalk x) := (g.stalkMap x).hom.toAlgebra
    let : Algebra ((Spec (.of A)).presheaf.stalk ((pullback.fst g ι[J] ≫ g).base w))
        ((Spec (.of (A ⧸ J))).presheaf.stalk y) :=
      ((eqToHom (congrArg (Spec (.of A)).presheaf.stalk h0)) ≫ (ι[J]).stalkMap y).hom.toAlgebra
    obtain ⟨φ, hφl, -, Msub, hloc⟩ := BaseChangeStalk.pullback_stalk_isLocalization g ι[J] w
    let : Algebra (TensorProduct ((Spec (.of A)).presheaf.stalk ((pullback.fst g ι[J] ≫ g).base w))
        (X.presheaf.stalk x) ((Spec (.of (A ⧸ J))).presheaf.stalk y))
        ((pullback g ι[J]).presheaf.stalk w) := φ.toAlgebra
    have h1 : algebraMap (TensorProduct
        ((Spec (.of A)).presheaf.stalk ((pullback.fst g ι[J] ≫ g).base w))
        (X.presheaf.stalk x) ((Spec (.of (A ⧸ J))).presheaf.stalk y))
        ((pullback g ι[J]).presheaf.stalk w) (Algebra.TensorProduct.includeLeftRingHom o) = 0 := by
      show φ (Algebra.TensorProduct.includeLeftRingHom o) = 0
      rw [← RingHom.comp_apply, hφl]
      exact ho
    obtain ⟨m, hm0⟩ := (IsLocalization.map_eq_zero_iff Msub _ _).mp h1
    have : IsClosedImmersion (ι[J]) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hsurjRB : Function.Surjective
        (algebraMap ((Spec (.of A)).presheaf.stalk ((pullback.fst g ι[J] ≫ g).base w))
          ((Spec (.of (A ⧸ J))).presheaf.stalk y)) :=
      ((ι[J]).stalkMap_surjective y).comp
        (eqToIso (congrArg (Spec (.of A)).presheaf.stalk h0)).commRingCatIsoToRingEquiv.surjective
    obtain ⟨o', hmo⟩ := Algebra.TensorProduct.includeLeft_surjective
      ((Spec (.of A)).presheaf.stalk ((pullback.fst g ι[J] ≫ g).base w)) (X.presheaf.stalk x)
      hsurjRB m.1
    have hmu := IsLocalization.map_units ((pullback g ι[J]).presheaf.stalk w) m
    rw [← hmo] at hmu hm0
    have hu : IsUnit (((pullback.fst g ι[J]).stalkMap w).hom o') := by
      rw [← hφl]
      exact hmu
    have hu' : IsUnit o' := (isUnit_map_iff ((pullback.fst g ι[J]).stalkMap w).hom o').mp hu
    have h2 : (Algebra.TensorProduct.includeLeftRingHom o :
        TensorProduct ((Spec (.of A)).presheaf.stalk ((pullback.fst g ι[J] ≫ g).base w))
          (X.presheaf.stalk x) ((Spec (.of (A ⧸ J))).presheaf.stalk y)) = 0 :=
      (IsUnit.mul_right_eq_zero (hu'.map Algebra.TensorProduct.includeLeftRingHom)).mp hm0
    let f₁ : X.presheaf.stalk x →ₐ[(Spec (.of A)).presheaf.stalk ((pullback.fst g ι[J] ≫ g).base w)]
        X.presheaf.stalk x ⧸ K := Ideal.Quotient.mkₐ _ K
    let β₀ : A ⧸ J →+* X.presheaf.stalk x ⧸ K :=
      Ideal.Quotient.lift J ((Ideal.Quotient.mk K).comp (baseRingStalkHom g x).hom)
        (fun a ha => (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_map_of_mem _ ha))
    have hunit : ∀ t : y.asIdeal.primeCompl, IsUnit (β₀ t) := by
      rintro ⟨t, ht⟩
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
      have ha : a ∉ (g.base x).asIdeal := by
        intro ha'
        apply ht
        have hgx : g.base x = (ι[J]).base y := h0
        rw [hgx] at ha'
        exact ha'
      have hu1 : IsUnit ((StructureSheaf.toStalk A (g.base x)).hom a) :=
        IsLocalization.map_units ((Spec (.of A)).presheaf.stalk (g.base x))
          (⟨a, ha⟩ : (g.base x).asIdeal.primeCompl)
      exact (hu1.map (g.stalkMap x).hom).map (Ideal.Quotient.mk K)
    let f₂₀ : (Spec (.of (A ⧸ J))).presheaf.stalk y →+* X.presheaf.stalk x ⧸ K :=
      IsLocalization.lift hunit
    have hf₂ : f₂₀.comp (algebraMap
        ((Spec (.of A)).presheaf.stalk ((pullback.fst g ι[J] ≫ g).base w))
          ((Spec (.of (A ⧸ J))).presheaf.stalk y)) =
        algebraMap ((Spec (.of A)).presheaf.stalk ((pullback.fst g ι[J] ≫ g).base w))
          (X.presheaf.stalk x ⧸ K) := by
      refine IsLocalization.ringHom_ext ((pullback.fst g ι[J] ≫ g).base w).asIdeal.primeCompl
        (RingHom.ext fun a => ?_)
      have e1 : ((ι[J]).stalkMap y).hom ((StructureSheaf.toStalk A ((ι[J]).base y)).hom a) =
          (StructureSheaf.toStalk (A ⧸ J) y).hom (Ideal.Quotient.mk J a) :=
        stalkMap_toStalk_apply (CommRingCat.ofHom (Ideal.Quotient.mk J)) y a
      have e2 : algebraMap ((Spec (.of A)).presheaf.stalk ((pullback.fst g ι[J] ≫ g).base w))
          ((Spec (.of (A ⧸ J))).presheaf.stalk y)
            ((StructureSheaf.toStalk A ((pullback.fst g ι[J] ≫ g).base w)).hom a) =
          algebraMap (A ⧸ J) ((Spec (.of (A ⧸ J))).presheaf.stalk y) (Ideal.Quotient.mk J a) :=
        (congrArg ((ι[J]).stalkMap y).hom (toStalk_eqToHom_apply h0 a)).trans e1
      show f₂₀ (algebraMap ((Spec (.of A)).presheaf.stalk ((pullback.fst g ι[J] ≫ g).base w))
        ((Spec (.of (A ⧸ J))).presheaf.stalk y)
          ((StructureSheaf.toStalk A ((pullback.fst g ι[J] ≫ g).base w)).hom a)) = _
      rw [e2, IsLocalization.lift_eq]
      rfl
    let f₂ : (Spec (.of (A ⧸ J))).presheaf.stalk y →ₐ[
        (Spec (.of A)).presheaf.stalk ((pullback.fst g ι[J] ≫ g).base w)] X.presheaf.stalk x ⧸ K :=
      { f₂₀ with commutes' := fun r => RingHom.congr_fun hf₂ r }
    have h3 : Algebra.TensorProduct.lift f₁ f₂ (fun _ _ => Commute.all _ _)
        (Algebra.TensorProduct.includeLeftRingHom o) = Ideal.Quotient.mk K o := by
      show Algebra.TensorProduct.lift f₁ f₂ (fun _ _ => Commute.all _ _) (o ⊗ₜ 1) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      rfl
    rw [h2, map_zero] at h3
    exact (Ideal.Quotient.eq_zero_iff_mem).mp h3.symm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, ← stalkMap_pullback_snd_toStalk_mk,
      (Ideal.Quotient.eq_zero_iff_mem).mpr ha]
    exact (congrArg _ (map_zero _)).trans (map_zero _)

/-- **The affine dictionary of Stacks 08VP on a scheme.**  Let `g : X ⟶ Spec A`, let `J ⊆ A`
be an ideal, and let `F` be an `𝒪_X`-module.  If at a point `w` of
`X ×_{Spec A} Spec (A / J)` the pullback of `F` is flat over `Spec (A / J)`, then, writing `x`
for the image of `w` in `X` and `M = F_x`, the module `M / J M` is flat over `A / J`.

The stalk of the pullback at `w` is `𝒪_w ⊗_{𝒪_{X, x}} M` by Stacks 0098, and
`𝒪_w = 𝒪_{X, x} / J 𝒪_{X, x}` by
`AlgebraicGeometry.ker_stalkMap_pullback_fst_specQuotient`, so that stalk is
`M / J M`; flatness over the local ring of `Spec (A / J)` gives flatness over `A / J` because
that local ring is a localization of `A / J`. -/
theorem flat_quotient_of_isFlatOverAt_pullback (F : X.Modules) (w : ↑(pullback g ι[J]))
    (hw : IsFlatOverAt (pullback.snd g ι[J]).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst g ι[J])).obj F) w) :
    letI : Module A (F.presheaf.stalk ((pullback.fst g ι[J]).base w)) :=
      Module.compHom _ (baseRingStalkHom g ((pullback.fst g ι[J]).base w)).hom
    Module.Flat (A ⧸ J) (F.presheaf.stalk ((pullback.fst g ι[J]).base w) ⧸
      (J • ⊤ : Submodule A (F.presheaf.stalk ((pullback.fst g ι[J]).base w)))) := by
  let σ := ((pullback.snd g ι[J]).stalkMap w).hom
  let ρ : A ⧸ J →+* (pullback g ι[J]).presheaf.stalk w := σ.comp
    (algebraMap (A ⧸ J) ((Spec (.of (A ⧸ J))).presheaf.stalk ((pullback.snd g ι[J]).base w)))
  have hρ : ρ.comp (Ideal.Quotient.mk J) =
      ((pullback.fst g ι[J]).stalkMap w).hom.comp
        (baseRingStalkHom g ((pullback.fst g ι[J]).base w)).hom :=
    RingHom.ext (stalkMap_pullback_snd_toStalk_mk J g w)
  have : IsClosedImmersion (ι[J]) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  let N := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
    ((Scheme.Modules.pullback (pullback.fst g ι[J])).obj F).val.presheaf w
  let : Module ((Spec (.of (A ⧸ J))).presheaf.stalk ((pullback.snd g ι[J]).base w)) N :=
    Module.compHom N σ
  have : Module.Flat ((Spec (.of (A ⧸ J))).presheaf.stalk ((pullback.snd g ι[J]).base w)) N :=
    hw
  let : Module (A ⧸ J) N := Module.compHom N ρ
  have : IsScalarTower (A ⧸ J)
      ((Spec (.of (A ⧸ J))).presheaf.stalk ((pullback.snd g ι[J]).base w)) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat (A ⧸ J)
      ((Spec (.of (A ⧸ J))).presheaf.stalk ((pullback.snd g ι[J]).base w)) :=
    IsLocalization.flat _ ((pullback.snd g ι[J]).base w).asIdeal.primeCompl
  have : Module.Flat (A ⧸ J) N :=
    Module.Flat.trans (A ⧸ J)
      ((Spec (.of (A ⧸ J))).presheaf.stalk ((pullback.snd g ι[J]).base w)) N
  let e := Stacks.ModuleSkyscraper.pullbackStalkLinearEquiv (pullback.fst g ι[J]) w F
  let : Module ((pullback g ι[J]).presheaf.stalk w) (Stacks.ModuleSkyscraper.stalkObj
      ((Scheme.Modules.pullback (pullback.fst g ι[J])).obj F).val w) :=
    (Stacks.ModuleSkyscraper.stalkObj
      ((Scheme.Modules.pullback (pullback.fst g ι[J])).obj F).val w).isModule
  refine flat_quotient_smul_top_of_flat_extendScalars _ _ J
    ((pullback.fst g ι[J]).stalkMap_surjective w)
    (ker_stalkMap_pullback_fst_specQuotient J g w) ρ hρ
    (Stacks.ModuleSkyscraper.stalkObj F.val ((pullback.fst g ι[J]).base w)) ?_
  let : Module (A ⧸ J) ((ModuleCat.extendScalars ((pullback.fst g ι[J]).stalkMap w).hom).obj
      (Stacks.ModuleSkyscraper.stalkObj F.val ((pullback.fst g ι[J]).base w))) :=
    Module.compHom _ ρ
  let e' : ((ModuleCat.extendScalars ((pullback.fst g ι[J]).stalkMap w).hom).obj
      (Stacks.ModuleSkyscraper.stalkObj F.val ((pullback.fst g ι[J]).base w))) ≃ₗ[A ⧸ J] N :=
    { e.toAddEquiv with map_smul' := fun r t => e.map_smul' (ρ r) t }
  exact Module.Flat.of_linearEquiv e'

/-- **The affine dictionary of Stacks 08VP on any cartesian square.**  The statement of
`AlgebraicGeometry.flat_quotient_of_isFlatOverAt_pullback`, for a square
`P = X ×_{Spec A} Spec (A / J)` which is cartesian but not necessarily the chosen fibre
product. -/
theorem flat_quotient_of_isFlatOverAt_of_isPullback {P : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Spec (.of (A ⧸ J))} (h : IsPullback fst snd g (ι[J])) (F : X.Modules) (w : P)
    (hw : IsFlatOverAt snd.toLRSHom.toShHom ((Scheme.Modules.pullback fst).obj F) w) :
    letI : Module A (F.presheaf.stalk (fst.base w)) :=
      Module.compHom _ (baseRingStalkHom g (fst.base w)).hom
    Module.Flat (A ⧸ J) (F.presheaf.stalk (fst.base w) ⧸
      (J • ⊤ : Submodule A (F.presheaf.stalk (fst.base w)))) := by
  have hfst : h.isoPullback.hom ≫ pullback.fst g ι[J] = fst := h.isoPullback_hom_fst
  have hsnd : h.isoPullback.hom ≫ pullback.snd g ι[J] = snd := h.isoPullback_hom_snd
  have hw2 : IsFlatOverAt (h.isoPullback.hom ≫ pullback.snd g ι[J]).toLRSHom.toShHom
      ((Scheme.Modules.pullback fst).obj F) w := by
    rwa [hsnd]
  have hw3 := (isFlatOverAt_iff_of_moduleIso _
    (((Scheme.Modules.pullbackCongr hfst).app F).symm ≪≫
      ((Scheme.Modules.pullbackComp h.isoPullback.hom (pullback.fst g ι[J])).app F).symm) w).mp hw2
  have hw' : IsFlatOverAt (pullback.snd g ι[J]).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst g ι[J])).obj F) (h.isoPullback.hom.base w) :=
    (isFlatOverAt_iff_modulePullback_isFlatOverAt h.isoPullback.hom (pullback.snd g ι[J])
      ((Scheme.Modules.pullback (pullback.fst g ι[J])).obj F) w
      (Flat.stalkMap h.isoPullback.hom w)).mpr hw3
  have hx : (pullback.fst g ι[J]).base (h.isoPullback.hom.base w) = fst.base w :=
    congrArg (fun k : P ⟶ X => k.base w) hfst
  exact hx ▸ flat_quotient_of_isFlatOverAt_pullback J g F (h.isoPullback.hom.base w) hw'

end Scheme

namespace Space

open CategoryTheory.Limits

attribute [local instance] pointTopology

/-- Pullbacks of presheaves on the big fppf site over `Spec A` (instance search times out
without this shortcut). -/
local instance (priority := high) hasPullback_presheaf_FlatModuleAdicThickeningsFibre
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hA : B.Contains (Spec (.of A)))

variable {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B (Spec (.of A)) hA X) (f : X ⟶ yoneda.obj (baseObject A B hA))

/-- The `n`-th adic fibre `X_n = X ×_{Spec A} Spec (A / I^{n+1})` of an algebraic space over
`Spec A`, as an object of the category of algebraic spaces. -/
abbrev adicFibreSpace (n : ℕ) : AlgebraicSpaces B (Spec (.of A)) hA :=
  ⟨adicFibre A I B hA (contains_adicThickening A I B hA) f n,
    isAlgebraicSpace_adicFibre A I B hA (contains_adicThickening A I B hA) hX f n⟩

/-- The projection `X_n ⟶ X` from the `n`-th adic fibre, as a morphism of algebraic spaces. -/
abbrev adicFibreFst (n : ℕ) :
    adicFibreSpace A I B hA hX f n ⟶ (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hA) :=
  ObjectProperty.homMk (pullback.fst f
    (yoneda.map (adicThickeningMap A I B hA (contains_adicThickening A I B hA) n)))

/-- The structure morphism `X_n ⟶ Spec (A / I^{n+1})` of the `n`-th adic fibre. -/
abbrev adicFibreSnd (n : ℕ) :
    adicFibre A I B hA (contains_adicThickening A I B hA) f n ⟶
      yoneda.obj (adicThickeningObject A I B hA (contains_adicThickening A I B hA) n) :=
  pullback.snd f (yoneda.map (adicThickeningMap A I B hA (contains_adicThickening A I B hA) n))

/-- **The dictionary of Stacks 08VP.**  Let `F` be a quasi-coherent `𝒪_X`-module whose pullback
`F_n` to the `n`-th adic fibre `X_n` is flat over `Spec (A / I^{n+1})`.  Then at every point `u`
of an étale scheme chart `U` of `X` lying over `V(I)`, the module stalk `M = (F|_U)_u` has
`M / I^{n+1} M` flat over `A / I^{n+1}`.

The chart `U_n = U ×_{Spec A} Spec (A / I^{n+1})` of `X_n` is the base change of `U`, a point of
it lies over `u`, the restriction of `F_n` to `U_n` is the pullback of `F|_U` by
`AlgebraicGeometry.Space.chartRestrictionBaseChangeIso`, and
`AlgebraicGeometry.flat_quotient_of_isFlatOverAt_of_isPullback` reads flatness of that pullback
as flatness of `M / I^{n+1} M`. -/
theorem flat_quotient_pow_of_isFlatOver_adicFibre (F : Modules.{u, u} B (Spec (.of A)) hA X hX)
    (hF : F.IsQuasicoherentOnSite) (n : ℕ)
    (hflat : IsFlatOver B (Spec (.of A)) hA (adicFibreSpace A I B hA hX f n).2
      (adicFibreSnd A I B hA f n)
      ((modulePullback B (Spec (.of A)) hA (adicFibreFst A I B hA hX f n)).obj F))
    (U : SmallEtale B (Spec (.of A)) hA X) (u : etaleChartScheme B (Spec (.of A)) hA U)
    (hu : I ≤ ((chartToAffineBase A B hA U).base u).asIdeal) :
    letI : Module A ((chartModule B (Spec (.of A)) hA hX F U).presheaf.stalk u) :=
      Module.compHom _ (baseRingStalkHom (chartToAffineBase A B hA U) u).hom
    Module.Flat (A ⧸ I ^ (n + 1))
      ((chartModule B (Spec (.of A)) hA hX F U).presheaf.stalk u ⧸
        (I ^ (n + 1) • (⊤ : Submodule A
          ((chartModule B (Spec (.of A)) hA hX F U).presheaf.stalk u)))) := by
  let a : U.obj.left ⟶ baseObject A B hA := Over.homMk U.obj.left.hom
  let t := adicThickeningMap A I B hA (contains_adicThickening A I B hA) n
  have hUa : U.obj.hom ≫ f = yoneda.map a :=
    (affineBaseChartDiagram A B hA f U).comm.trans (Category.comp_id _)
  have hcond : (yoneda.map (pullback.fst a t) ≫ U.obj.hom) ≫ f =
      yoneda.map (pullback.snd a t) ≫ yoneda.map t := by
    rw [Category.assoc, hUa, ← yoneda.map_comp, ← yoneda.map_comp, pullback.condition]
  let Wh : yoneda.obj (pullback a t) ⟶ adicFibre A I B hA (contains_adicThickening A I B hA) f n :=
    pullback.lift _ _ hcond
  have hWfst : Wh ≫ pullback.fst f (yoneda.map t) = yoneda.map (pullback.fst a t) ≫ U.obj.hom :=
    pullback.lift_fst _ _ _
  have hWsnd : Wh ≫ pullback.snd f (yoneda.map t) = yoneda.map (pullback.snd a t) :=
    pullback.lift_snd _ _ _
  have hpb : IsPullback Wh (yoneda.map (pullback.fst a t)) (pullback.fst f (yoneda.map t))
      U.obj.hom := by
    refine IsPullback.of_right ?_ hWfst (IsPullback.of_hasPullback f (yoneda.map t)).flip
    rw [hWsnd, hUa]
    exact ((IsPullback.of_hasPullback a t).map yoneda).flip
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  let W : SmallEtale B (Spec (.of A)) hA
      (adicFibre A I B hA (contains_adicThickening A I B hA) f n) :=
    ⟨CostructuredArrow.mk Wh, MorphismProperty.of_isPullback hpb.flip U.property⟩
  -- the scheme of `W` is `U ×_{Spec A} Spec (A / I^{n+1})`
  have hsq : IsPullback ((BigFppfOver.toScheme B (Spec (.of A)) hA).map (pullback.fst a t))
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).map (pullback.snd a t))
      (chartToAffineBase A B hA U)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) :=
    (IsPullback.of_hasPullback a t).map (BigFppfOver.toScheme B (Spec (.of A)) hA)
  obtain ⟨y, hy⟩ : ∃ y : PrimeSpectrum (A ⧸ I ^ (n + 1)),
      PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (n + 1))) y =
        (chartToAffineBase A B hA U).base u := by
    have : (chartToAffineBase A B hA U).base u ∈
        Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (n + 1)))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
      exact (PrimeSpectrum.mem_zeroLocus _ _).mpr
        fun x hx => hu (Ideal.pow_le_self (Nat.succ_ne_zero n) hx)
    exact this
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := chartToAffineBase A B hA U)
    (g := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) u y hy.symm
  let w : etaleChartScheme B (Spec (.of A)) hA W := hsq.isoPullback.inv.base z
  have hw : ((BigFppfOver.toScheme B (Spec (.of A)) hA).map (pullback.fst a t)).base w = u :=
    (congrArg (fun k => k.base z) hsq.isoPullback_inv_fst).trans hz
  -- flatness of `F_n` on the chart `W`, read over the base `Spec (A / I^{n+1})` itself
  let dn : ChartDiagram B (Spec (.of A)) hA
      (adicFibre A I B hA (contains_adicThickening A I B hA) f n)
      (yoneda.obj (adicThickeningObject A I B hA (contains_adicThickening A I B hA) n))
      (adicFibreSnd A I B hA f n) :=
    { U := W
      V := selfChart B (Spec (.of A)) hA _
      g := pullback.snd a t
      comm := hWsnd.trans (Category.comp_id _).symm }
  have hg : yoneda.map (pullback.fst a t) ≫ U.obj.hom =
      W.obj.hom ≫ (adicFibreFst A I B hA hX f n).hom := hWfst.symm
  have h2 := (isFlatOverAt_iff_of_moduleIso _
    (chartRestrictionBaseChangeIso B (Spec (.of A)) hA (adicFibreFst A I B hA hX f n) F hF U W
      (pullback.fst a t) hg) w).mpr (hflat dn w)
  exact hw ▸ flat_quotient_of_isFlatOverAt_of_isPullback (I ^ (n + 1))
    (chartToAffineBase A B hA U) hsq (chartModule B (Spec (.of A)) hA hX F U) w h2

/-- **Stacks 08VP.**  Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal and let `X` be an
algebraic space locally of finite presentation over `S = Spec A`.  For `n ≥ 1` set
`S_n = Spec (A / Iⁿ)` and `X_n = S_n ×_S X`, and let `F` be a coherent `𝒪_X`-module.  If for
every `n ≥ 1` the pullback `F_n` of `F` to `X_n` is flat over `S_n`, then the locus where `F` is
flat over `S` is open and contains the inverse image of `V(I)` under `X → S`.

The openness is Stacks 05WV,
`AlgebraicGeometry.Space.isOpen_flatLocus_of_isFinitePresentationOnCharts`, a coherent module
being of finite presentation.  Here `X_n` is `AlgebraicGeometry.Space.adicFibreSpace`, the fibre
product of algebraic spaces `X ×_S S_n` with `S_n = Spec (A / I^{n+1})` for `n : ℕ`, so that `n`
runs over the exponents `≥ 1`; `F_n` is the pullback of modules
`AlgebraicGeometry.Space.modulePullback` along the projection
`AlgebraicGeometry.Space.adicFibreFst`; flatness over `S_n` is `AlgebraicGeometry.Space.IsFlatOver`
of Stacks 05VV along `AlgebraicGeometry.Space.adicFibreSnd`; coherence is
`AlgebraicGeometry.Space.IsCoherent` of Stacks 07UA; and the locus is
`AlgebraicGeometry.Space.flatLocus`. -/
@[stacks 08VP]
theorem preimage_zeroLocus_subset_flatLocus_of_isFlatOver_adicFibre [IsNoetherianRing A]
    (hf : IsLocallyOfFinitePresentation B (Spec (.of A)) hA f)
    (F : Modules.{u, u} B (Spec (.of A)) hA X hX) [IsCoherent B (Spec (.of A)) hA X hX F]
    (hflat : ∀ n : ℕ, IsFlatOver B (Spec (.of A)) hA (adicFibreSpace A I B hA hX f n).2
      (adicFibreSnd A I B hA f n)
      ((modulePullback B (Spec (.of A)) hA (adicFibreFst A I B hA hX f n)).obj F)) :
    IsOpen (flatLocus B (Spec (.of A)) hA hX f F) ∧
      (fun x => pointsToScheme B (Spec (.of A)) hA (baseObject A B hA)
          (pointsMap B (Spec (.of A)) hA X f x)) ⁻¹'
        PrimeSpectrum.zeroLocus (I : Set A) ⊆
        flatLocus B (Spec (.of A)) hA hX f F := by
  have hqc : F.IsQuasicoherentOnSite := inferInstance
  refine ⟨isOpen_flatLocus_of_isFinitePresentationOnCharts B (Spec (.of A)) hA hX f F hf
    (isQuasicoherentOnCharts_of_isQuasicoherentOnSite B (Spec (.of A)) hA ⟨X, hX⟩ F hqc)
    (isFinitePresentationOnCharts_of_isFinitePresentationOnSite B (Spec (.of A)) hA ⟨X, hX⟩ F
      hqc (SheafOfModules.isFinitePresentationOnSite_of_isCoherentOnSite F inferInstance)), ?_⟩
  exact preimage_zeroLocus_subset_flatLocus A I B hA hX f hf F
    (isQuasicoherentOnCharts_of_isQuasicoherentOnSite B (Spec (.of A)) hA ⟨X, hX⟩ F hqc)
    (isFiniteTypeOnCharts_of_isFiniteTypeOnSite B (Spec (.of A)) hA ⟨X, hX⟩ F hqc
      (isFiniteTypeOnSite_of_isCoherentOnSite B (Spec (.of A)) hA ⟨X, hX⟩ F))
    (fun U u hu n =>
      flat_quotient_pow_of_isFlatOver_adicFibre A I B hA hX f F hqc n (hflat n) U u hu)

end Space

end AlgebraicGeometry

end
