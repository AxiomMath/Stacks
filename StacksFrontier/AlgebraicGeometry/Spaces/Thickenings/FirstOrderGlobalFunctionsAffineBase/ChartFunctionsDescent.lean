module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas

/-!
# Descending a regular function on an étale chart to all scheme charts

Let `w : h_W ⟶ U` be a surjective étale chart of a presheaf `U` on the big fppf site of `S`, and
let `s, t : R ⟶ W` be its kernel pair, so that `h_R = h_W ×_U h_W`.  A regular function `a` on
`W` with `s^*a = t^*a` descends to a compatible family of regular functions on all scheme charts
of `U`: on a chart `j : h_V ⟶ U` the value is the unique function on `V` whose pullback along any
`φ : Z ⟶ V` lifting through `w` by some `ψ : Z ⟶ W` is `ψ^*a`.

This is the descent of global regular functions along the surjective étale morphism `V ×_U W ⟶ V`
of the big fppf site, `AlgebraicGeometry.Space.existsUnique_gamma_of_etale_surjection`, applied at
every chart; the kernel pair is what makes the pulled back function match on the two projections.

## Main results

* `AlgebraicGeometry.Space.FirstOrderGlobalFunctions.gamma_eq_of_comp_eq`: two morphisms to `W`
  with the same composite to `U` pull `a` back to the same function.
* `AlgebraicGeometry.Space.FirstOrderGlobalFunctions.exists_chartFunctions_of_kernelPair`: the
  descended compatible family, characterized by its pullbacks along lifts through `w`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.FirstOrderGlobalFunctions

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W R : BigFppfOver B S hS}
  {w : yoneda.obj W ⟶ U} {s t : R ⟶ W}

/-- **Two morphisms to `W` with the same composite to `U` pull an `s,t`-invariant function back
to the same function.**  The pair factors through the kernel pair `R`. -/
theorem gamma_eq_of_comp_eq (hR : IsPullback (yoneda.map s) (yoneda.map t) w w)
    (a : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (ha : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map s).op).hom a =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map t).op).hom a)
    {Z : BigFppfOver B S hS} (g₁ g₂ : Z ⟶ W) (h : yoneda.map g₁ ≫ w = yoneda.map g₂ ≫ w) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g₁).op).hom a =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g₂).op).hom a := by
  obtain ⟨z, hz⟩ := Yoneda.fullyFaithful.map_surjective (hR.lift (yoneda.map g₁) (yoneda.map g₂) h)
  have h₁ : z ≫ s = g₁ := yoneda.map_injective (by
    rw [Functor.map_comp, hz, hR.lift_fst])
  have h₂ : z ≫ t = g₂ := yoneda.map_injective (by
    rw [Functor.map_comp, hz, hR.lift_snd])
  rw [← h₁, ← h₂, Functor.map_comp, Functor.map_comp,
    ← gamma_map_comp, ← gamma_map_comp, ha]

/-- The property characterizing the descended function on a chart `j`. -/
def IsDescent (a : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) (j : CostructuredArrow yoneda U)
    (v : Γ((BigFppfOver.toScheme B S hS).obj j.left, ⊤)) : Prop :=
  ∀ ⦃Z : BigFppfOver B S hS⦄ (φ : Z ⟶ j.left) (ψ : Z ⟶ W),
    yoneda.map ψ ≫ w = yoneda.map φ ≫ j.hom →
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map φ).op).hom v =
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map ψ).op).hom a

variable (hwE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf w)
  (hwS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf w)
include hwE hwS

/-- **The descended function on a chart exists and is unique.** -/
theorem existsUnique_isDescent (hR : IsPullback (yoneda.map s) (yoneda.map t) w w)
    (a : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (ha : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map s).op).hom a =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map t).op).hom a)
    (j : CostructuredArrow yoneda U) :
    ∃! v, IsDescent (w := w) a j v := by
  classical
  let F := BigFppfOver.toScheme B S hS
  have : HasPullbacks (BigFppfOver B S hS) := inferInstance
  let _ := B.hasPullbacks_schemes
  let _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.forget B S hS) := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  obtain ⟨P, α, p, hpb⟩ := hwE.1 j.hom
  have hαE : Etale (F.map α) := hwE.2 j.hom p α hpb
  have hαS : Surjective (F.map α) := hwS.2 j.hom p α hpb
  obtain ⟨pHom, rfl⟩ := Yoneda.fullyFaithful.map_surjective p
  -- the square `hpb` expressed on the level of morphisms of charts
  have key : ∀ {Z : BigFppfOver B S hS} (x : Z ⟶ P),
      yoneda.map (x ≫ pHom) ≫ w = yoneda.map (x ≫ α) ≫ j.hom := fun x => by
    simp [hpb.w]
  -- the descended value along the base change of the chart
  obtain ⟨v, hv, -⟩ := existsUnique_gamma_of_etale_surjection B S hS α hαS hαE
    ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map pHom).op).hom a)
    (by
      intro Z g₁ g₂ h
      rw [gamma_map_comp, gamma_map_comp, ← Functor.map_comp, ← Functor.map_comp]
      exact gamma_eq_of_comp_eq hR a ha _ _ (by rw [key, key, h]))
  -- any function with the descent property restricts along `α` to `pHom^* a`
  have hchar : ∀ v', IsDescent (w := w) a j v' →
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map α).op).hom v' =
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map pHom).op).hom a := fun v' hv' =>
    hv' α pHom hpb.w
  refine ⟨v, ?_, fun v' hv' => gamma_injective_of_etale_surjection B S hS α hαS hαE
    ((hchar v' hv').trans hv.symm)⟩
  -- the descent property of `v`
  intro Z φ ψ hψ
  let qZ : pullback φ α ⟶ Z := pullback.fst φ α
  let qP : pullback φ α ⟶ P := pullback.snd φ α
  have hsq : IsPullback (F.map qZ) (F.map qP) (F.map φ) (F.map α) :=
    (IsPullback.of_hasPullback φ α).map F
  have hcond : qZ ≫ φ = qP ≫ α := pullback.condition
  have hqE : Etale (F.map qZ) := MorphismProperty.of_isPullback hsq.flip hαE
  have hqS : Surjective (F.map qZ) := MorphismProperty.of_isPullback hsq.flip hαS
  refine gamma_injective_of_etale_surjection B S hS qZ hqS hqE ?_
  rw [gamma_map_comp, gamma_map_comp, ← Functor.map_comp, ← Functor.map_comp,
    hcond, Functor.map_comp, ← gamma_map_comp, hv, gamma_map_comp,
    ← Functor.map_comp]
  refine gamma_eq_of_comp_eq hR a ha _ _ ?_
  rw [key, ← hcond]
  simp [hψ]

/-- **Descent of an `s,t`-invariant regular function on a surjective étale chart to a compatible
family on all scheme charts.**  Its value on a chart `j` pulls back along any `φ : Z ⟶ j.left`
lifting through `w` by `ψ : Z ⟶ W` to `ψ^*a`. -/
theorem exists_chartFunctions_of_kernelPair (hR : IsPullback (yoneda.map s) (yoneda.map t) w w)
    (a : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (ha : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map s).op).hom a =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map t).op).hom a) :
    ∃ e : chartFunctions B S hS U, ∀ j : CostructuredArrow yoneda U,
      IsDescent (w := w) a j (e.val (op j)) := by
  classical
  let val : ∀ j : (CostructuredArrow yoneda U)ᵒᵖ, (chartPresheaf B S hS U ⋙ forget _).obj j :=
    fun j => (existsUnique_isDescent hwE hwS hR a ha j.unop).exists.choose
  have hval : ∀ j : CostructuredArrow yoneda U, IsDescent (w := w) a j (val (op j)) := fun j =>
    (existsUnique_isDescent hwE hwS hR a ha j).exists.choose_spec
  refine ⟨⟨val, ?_⟩, fun j => hval j⟩
  intro j k f
  refine (existsUnique_isDescent hwE hwS hR a ha k.unop).unique ?_ (hval k.unop)
  intro Z φ ψ hψ
  show (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map φ).op).hom
    ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map f.unop.left).op).hom (val j)) = _
  rw [gamma_map_comp, ← Functor.map_comp]
  refine hval j.unop _ ψ ?_
  rw [hψ, Functor.map_comp, Category.assoc, CostructuredArrow.w]

end AlgebraicGeometry.Space.FirstOrderGlobalFunctions

end
