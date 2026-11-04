module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleAdicPointLift
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionCofinalColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageCompletionComparison
public import StacksFrontier.RingTheory.Etale.Lifting

/-!
# Lifting an étale chart of a stage to the completion of an étale algebra

Let `S` be a scheme contained in a big fppf site `B`, let `A` be a topological ring carrying the
`I`-adic topology with a quotient system `D` over `S`, and let `φ : E ⟶ Spf A` be a morphism of
fppf sheaves which is representable by algebraic spaces and étale. Given an affine object `V` of
the site, étale over the quotient stage `Spec (A ⧸ Iᵐ⁺¹)`, and a section `e` of `E` over `V` lying
over that stage, there is an étale `A`-algebra `C` and a morphism `Spf C^∧ ⟶ E` over `Spf A`
through which `e` factors.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_lift_formalSpectrum_of_formallyEtale_of_tower`: a lift of
  the restriction of a morphism `Spf W ⟶ Y` to the first stage of a cofinal tower of square-zero
  thickenings extends, along a formally étale `X ⟶ Y`, to a lift `Spf W ⟶ X`.
* `AlgebraicGeometry.FormalSpace.kerProjectionIdeal_sq_le`: the kernels of the projections of a
  relative completion inherit the square-zero relation of the base ideals.
* `AlgebraicGeometry.FormalSpace.exists_completion_lift_of_etale_chart`: the statement above.

## Implementation notes

The chart `V` has coordinate ring `C₁`, an étale `A ⧸ Iᵐ⁺¹`-algebra; Stacks 04D1 lifts it to an
étale `A`-algebra `C` with `C ⧸ Iᵐ⁺¹C ≅ C₁`, and the quotient stage of `C^∧` at `Iᵐ⁺¹` is then
`V`. The section `e` is transported to that stage and lifted, by formal étaleness of `φ`, along
the tower of quotient stages of `C^∧` at the powers `Iᵐ⁺ⁿ⁺¹`, which is cofinal.

## References

* [Stacks Project, Tag 04D1](https://stacks.math.columbia.edu/tag/04D1)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Tower

variable {W : Type u} [CommRing W] [TopologicalSpace W] (D : QuotientSystem B S hS W)
  (K : ℕ → { I : Ideal W // TopologicalRing.IsWeakIdealOfDefinition I })
  (hmono : ∀ n, (K (n + 1)).1 ≤ (K n).1) (hsq : ∀ n, (K n).1 ^ 2 ≤ (K (n + 1)).1)
  (hcofinal : ∀ I : { I : Ideal W // TopologicalRing.IsWeakIdealOfDefinition I },
    ∃ n, (K n).1 ≤ I.1)

include hmono hsq hcofinal in
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **A point of a formal spectrum lifts along a formally étale morphism, extending a given lift
at the first stage of a cofinal tower of square-zero thickenings.** -/
theorem exists_lift_formalSpectrum_of_formallyEtale_of_tower {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : Space.FormallyEtale f.hom) (q : formalSpectrum D ⟶ Y)
    (z₀ : (formalSpectrumDiagram D).obj (OrderDual.toDual (K 0)) ⟶ X)
    (hz₀ : z₀ ≫ f = formalSpectrumInclusion D (OrderDual.toDual (K 0)) ≫ q) :
    ∃ x : formalSpectrum D ⟶ X, x ≫ f = q ∧
      formalSpectrumInclusion D (OrderDual.toDual (K 0)) ≫ x = z₀ := by
  classical
  let Jt := BigFppfOver.topology B S hS
  let T : ℕ → BigFppfOver B S hS := fun n =>
    (BigAffineFppf.inclusion B S hS).obj (D.stage (K n))
  let i : ∀ n, T n ⟶ T (n + 1) := fun n =>
    (BigAffineFppf.inclusion B S hS).map (D.transition (hmono n))
  let ι : ∀ n, (formalSpectrumDiagram D).obj (OrderDual.toDual (K n)) ⟶ formalSpectrum D :=
    fun n => formalSpectrumInclusion D (OrderDual.toDual (K n))
  let g : ∀ n, OrderDual.toDual (K n) ⟶ OrderDual.toDual (K (n + 1)) :=
    fun n => homOfLE (hmono n)
  have hι : ∀ n, (formalSpectrumDiagram D).map (g n) ≫ ι (n + 1) = ι n := fun n =>
    colimit.w (formalSpectrumDiagram D) (g n)
  let y : ∀ n, Y.obj.obj (op (T n)) := fun n => Sheaf.sectionEquiv Jt (ι n ≫ q)
  have hy : ∀ n, Y.obj.map (i n).op (y (n + 1)) = y n := fun n =>
    (Sheaf.sectionEquiv_map_comp Jt (i n) (ι (n + 1) ≫ q)).symm.trans
      (congrArg (Sheaf.sectionEquiv Jt)
        ((Category.assoc _ _ _).symm.trans (congrArg (fun c => c ≫ q) (hι n))))
  obtain ⟨z, hz0, hz, hzy⟩ := Space.exists_compatible_lifts_of_formallyEtale f.hom hf T i
    (fun n => isAffine_stageObj D (K n))
    (fun n => isSquareZeroClosedImmersion_transition D (hmono n) (hsq n)) y hy
    (Sheaf.sectionEquiv Jt z₀)
    ((Sheaf.sectionEquiv_comp Jt z₀ f).symm.trans (congrArg (Sheaf.sectionEquiv Jt) hz₀))
  let zm : ∀ n, (formalSpectrumDiagram D).obj (OrderDual.toDual (K n)) ⟶ X :=
    fun n => (Sheaf.sectionEquiv Jt).symm (z n)
  have hzms : ∀ n, Sheaf.sectionEquiv Jt (zm n) = z n := fun n => Equiv.apply_symm_apply _ _
  have hzm : ∀ n, (formalSpectrumDiagram D).map (g n) ≫ zm (n + 1) = zm n := fun n =>
    (Sheaf.sectionEquiv Jt).injective <|
      (Sheaf.sectionEquiv_map_comp Jt (i n) (zm (n + 1))).trans
        ((congrArg _ (hzms (n + 1))).trans ((hz n).trans (hzms n).symm))
  have hzmf : ∀ n, zm n ≫ f = ι n ≫ q := fun n =>
    (Sheaf.sectionEquiv Jt).injective <|
      (Sheaf.sectionEquiv_comp Jt (zm n) f).trans ((congrArg _ (hzms n)).trans (hzy n))
  obtain ⟨x, hx⟩ := exists_formalSpectrum_hom_of_cofinal D K hmono hcofinal zm hzm
  refine ⟨x, formalSpectrum_hom_ext_of_cofinal D K hcofinal fun n => ?_, ?_⟩
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun c => c ≫ f) (hx n)).trans (hzmf n))
  · exact (hx 0).trans ((Sheaf.sectionEquiv Jt).injective ((hzms 0).trans hz0))

end Tower

section KernelSquare

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] (f : A →+* C)

/-- **The kernels of the projections of a relative completion inherit the square-zero relation
of the base ideals**: if `L ^ 2 ≤ L'` with `L' ≤ L`, then `ker (C^∧ → C ⧸ LC) ^ 2` lies in
`ker (C^∧ → C ⧸ L'C)`. -/
theorem kerProjectionIdeal_sq_le {L L' : TopologicalRing.WeakIdealOfDefinitionIndex A}
    (hle : L'.1 ≤ L.1) (hsq : L.1 ^ 2 ≤ L'.1) :
    (kerProjectionIdeal f L).1 ^ 2 ≤ (kerProjectionIdeal f L').1 := by
  let P : Ideal (C ⧸ TopologicalRing.extendedIdeal f L') :=
    (TopologicalRing.extendedIdeal f L).map (Ideal.Quotient.mk _)
  have hmem : ∀ x ∈ (kerProjectionIdeal f L).1, x.1 L' ∈ P := by
    intro x hx
    change x.1 L = 0 at hx
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (x.1 L')
    have h := x.2 L' L hle
    rw [← hc] at h ⊢
    change Ideal.Quotient.mk (TopologicalRing.extendedIdeal f L) c = x.1 L at h
    exact Ideal.mem_map_of_mem _ (Ideal.Quotient.eq_zero_iff_mem.mp (h.trans hx))
  have hPP : P * P = ⊥ := by
    rw [← Ideal.map_mul, eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.map_mono hsq (by rwa [pow_two, Ideal.map_mul])
  rw [pow_two, Ideal.mul_le]
  intro x hx y hy
  show (x * y).1 L' = 0
  have : x.1 L' * y.1 L' ∈ P * P := Ideal.mul_mem_mul (hmem x hx) (hmem y hy)
  rwa [hPP, Ideal.mem_bot] at this

end KernelSquare


section Chart

attribute [local instance] sheaf_hasColimits

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **An étale chart of a quotient stage, carrying a section of a formally étale sheaf over
`Spf A`, extends to the formal spectrum of the completion of an étale `A`-algebra.** Let `A`
carry the `I`-adic topology and let `φ : E ⟶ Spf A` be formally étale. For an affine object
`V` of the site with an étale morphism `p` to the quotient stage `Spec (A ⧸ Iᵐ⁺¹)` and a
morphism `e : h_V ⟶ E` over that stage, there are an étale ring map `f : A → C`, a quotient
system `Q` on the completion `C^∧` with a continuous map `g` from `D` realising the canonical
map, a morphism `w : Spf C^∧ ⟶ E` over `Spf A`, and a factorization of `e` through `w`.

`C` is an étale lift of the coordinate ring of `V` (Stacks 04D1), so that the quotient stage of
`C^∧` at `Iᵐ⁺¹` is `V`; `w` is the lift of `e` along the tower of quotient stages of `C^∧` at the
powers `Iᵐ⁺ⁿ⁺¹`. -/
theorem exists_completion_lift_of_etale_chart
    (hA : TopologicalRing.IsWeaklyAdmissible A) {I : Ideal A} (hIadic : _root_.IsAdic I)
    (D : QuotientSystem B S hS A) (hD : D.HasLargeSite)
    {E : FppfSheaf B S hS} (φ : E ⟶ formalSpectrum D) (hφ : Space.FormallyEtale φ.hom)
    (m : ℕ) (V : BigFppfOver B S hS)
    (p : V ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage (adicStage hIadic m)))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hp : Etale ((BigFppfOver.toScheme B S hS).map p))
    (e : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ E)
    (he : e ≫ φ = (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p ≫
      formalSpectrumInclusion D (OrderDual.toDual (adicStage hIadic m))) :
    ∃ (C : Type u) (_ : CommRing C) (f : A →+* C) (_ : f.Etale)
      (Q : QuotientSystem B S hS (TopologicalRing.CompletionOver f))
      (g : ContinuousHom D Q) (_ : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f)
      (w : formalSpectrum Q ⟶ E)
      (σ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ formalSpectrum Q),
      w ≫ φ = formalSpectrumMap hA g ∧ σ ≫ w = e := by
  classical
  let Jt := BigFppfOver.topology B S hS
  let G := BigFppfOver.toScheme B S hS
  let J := adicStage hIadic m
  let X := G.obj V
  let p₀ : X ⟶ Spec (.of (A ⧸ J.1)) := G.map p
  -- the étale coordinate ring of the chart
  let h : A ⧸ J.1 →+* Γ(X, ⊤) :=
    p₀.appTop.hom.comp (Scheme.ΓSpecIso (.of (A ⧸ J.1))).inv.hom
  have hh : h.Etale := RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of (A ⧸ J.1))).inv)) (HasRingHomProperty.appTop @Etale p₀ hp)
  -- Stacks 04D1: an étale `A`-algebra lifting it
  let : Algebra (A ⧸ J.1) Γ(X, ⊤) := h.toAlgebra
  let : Algebra A Γ(X, ⊤) := (h.comp (Ideal.Quotient.mk J.1)).toAlgebra
  have : IsScalarTower A (A ⧸ J.1) Γ(X, ⊤) := .of_algebraMap_eq fun _ => rfl
  have : Algebra.Etale (A ⧸ J.1) Γ(X, ⊤) := hh
  obtain ⟨C, _, _, hCet, ψ, hψ, hker⟩ := etale_lift_along_surjection A (A ⧸ J.1) Γ(X, ⊤)
    Ideal.Quotient.mk_surjective
  let f : A →+* C := algebraMap A C
  have hf : f.Etale := RingHom.etale_algebraMap.mpr hCet
  have hFT : let : Algebra A C := f.toAlgebra; Algebra.FiniteType A C := by
    have halg : f.toAlgebra = ‹Algebra A C› := Algebra.algebra_ext _ _ fun _ => rfl
    rw [halg]
    infer_instance
  obtain ⟨Q, g, hg⟩ := exists_completionOver_quotientSystem B S hS f hFT hA D hD
  have hker' : RingHom.ker (ψ : C →+* Γ(X, ⊤)) = TopologicalRing.extendedIdeal f J := by
    rw [hker]
    show Ideal.map f (RingHom.ker (Ideal.Quotient.mk J.1)) = _
    rw [Ideal.mk_ker]
  -- the tower of kernels of the projections
  let K : ℕ → TopologicalRing.WeakIdealOfDefinitionIndex (TopologicalRing.CompletionOver f) :=
    fun n => kerProjectionIdeal f (adicStage hIadic (m + n))
  have hmono : ∀ n, (K (n + 1)).1 ≤ (K n).1 := fun n =>
    kerProjectionIdeal_mono f (adicStage_le_succ hIadic (m + n))
  have hsq : ∀ n, (K n).1 ^ 2 ≤ (K (n + 1)).1 := fun n =>
    kerProjectionIdeal_sq_le f (adicStage_le_succ hIadic (m + n))
      (adicStage_sq_le_succ hIadic (m + n))
  have hcofinal : ∀ L : TopologicalRing.WeakIdealOfDefinitionIndex
      (TopologicalRing.CompletionOver f), ∃ n, (K n).1 ≤ L.1 := by
    intro L
    obtain ⟨J', hJ'⟩ :=
      TopologicalRing.CompletionOver.exists_ker_projection_le_of_isWeakIdealOfDefinition f hA.1
        L.2
    obtain ⟨N, hN⟩ := exists_adicStage_le hIadic J'
    refine ⟨N, le_trans (kerProjectionIdeal_mono f ?_) hJ'⟩
    exact le_trans (Ideal.pow_le_pow_right (by omega)) hN
  -- the stage of `C^∧` at `J` is the chart
  have hle : J.1 ≤ Ideal.comap g.toRingHom (K 0).1 := le_comap_kerProjectionIdeal f g hg J
  let e₀ : (TopologicalRing.CompletionOver f ⧸ (K 0).1) ≃+* Γ(X, ⊤) :=
    (quotientKerProjectionRingEquiv f J).trans
      ((Ideal.quotEquivOfEq hker'.symm).trans
        (RingHom.quotientKerEquivOfSurjective (f := (ψ : C →+* Γ(X, ⊤))) hψ))
  have he₀ : e₀.toRingHom.comp (Ideal.quotientMap (K 0).1 g.toRingHom hle) = h := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
    show e₀ (Ideal.quotientMap (K 0).1 g.toRingHom hle (Ideal.Quotient.mk _ r)) = _
    rw [Ideal.quotientMap_mk]
    simp only [e₀, RingEquiv.trans_apply, hg]
    exact ψ.commutes r
  -- the chart as the stage of `C^∧` at `J`, over the stage of `A` at `J`
  have _ := hV
  let T₀ : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj (Q.stage (K 0))
  let st : T₀ ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage J) :=
    (BigAffineFppf.inclusion B S hS).map (g.stageMap J (K 0) hle)
  let θs : X ≅ G.obj T₀ :=
    X.isoSpec.trans (Scheme.Spec.mapIso e₀.toCommRingCatIso.op)
  have htri : θs.hom ≫ G.map st = G.map p := Scheme.toSpecΓ_comp_Spec_map p₀ e₀.toRingHom _ he₀
  have htri' : θs.inv ≫ G.map p = G.map st := by
    rw [← htri, Iso.inv_hom_id_assoc]
  let θ : V ≅ T₀ :=
    { hom := BigFppfOver.homOfTriangle B S hS p st θs.hom htri
      inv := BigFppfOver.homOfTriangle B S hS st p θs.inv htri'
      hom_inv_id := G.map_injective (by
        rw [Functor.map_comp, BigFppfOver.toScheme_map_homOfTriangle,
          BigFppfOver.toScheme_map_homOfTriangle, Iso.hom_inv_id,
          CategoryTheory.Functor.map_id])
      inv_hom_id := G.map_injective (by
        rw [Functor.map_comp, BigFppfOver.toScheme_map_homOfTriangle,
          BigFppfOver.toScheme_map_homOfTriangle, Iso.inv_hom_id,
          CategoryTheory.Functor.map_id]) }
  have hθinv : θ.inv ≫ p = st := BigFppfOver.homOfTriangle_comp B S hS st p θs.inv htri'
  -- the section transported to the stage, and its lift
  let z₀ : (Sheaf.sheafifiedYoneda Jt).obj T₀ ⟶ E := (Sheaf.sheafifiedYoneda Jt).map θ.inv ≫ e
  have hz₀ : z₀ ≫ φ = formalSpectrumInclusion Q (OrderDual.toDual (K 0)) ≫
      formalSpectrumMap hA g := by
    rw [formalSpectrumMap_spec hA g J (K 0) hle]
    show ((Sheaf.sheafifiedYoneda Jt).map θ.inv ≫ e) ≫ φ = _
    rw [Category.assoc, he]
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (fun c => c ≫ formalSpectrumInclusion D (OrderDual.toDual J))
      (((Sheaf.sheafifiedYoneda Jt).map_comp θ.inv p).symm.trans
        (congrArg (Sheaf.sheafifiedYoneda Jt).map hθinv))
  obtain ⟨w, hw, hw₀⟩ := exists_lift_formalSpectrum_of_formallyEtale_of_tower Q K hmono hsq
    hcofinal φ hφ (formalSpectrumMap hA g) z₀ hz₀
  refine ⟨C, inferInstance, f, hf, Q, g, hg, w,
    (Sheaf.sheafifiedYoneda Jt).map θ.hom ≫ formalSpectrumInclusion Q (OrderDual.toDual (K 0)),
    hw, ?_⟩
  refine (Category.assoc _ _ _).trans ((congrArg (fun c => _ ≫ c) hw₀).trans ?_)
  exact ((Sheaf.sheafifiedYoneda Jt).mapIso θ).hom_inv_id_assoc e

end Chart

end AlgebraicGeometry.FormalSpace

end
