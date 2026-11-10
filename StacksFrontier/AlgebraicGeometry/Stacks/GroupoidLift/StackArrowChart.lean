module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackArrowAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.SpaceLiftCover

/-!
# A formally étale chart of the arrows near an identity

With the notation of `AlgebraicGeometry.Stack.GroupoidLift.stackGroupoid`, let `𝒳` be an
algebraic stack and `w : P → C` a point. After a surjective étale refinement `C → C₁`, the
identity arrow of `w` factors through a formally étale chart `b : Hom(Q, -) ⟶ Arr` of the arrows
of the groupoid of the chart (`AlgebraicGeometry.Stack.GroupoidLift.exists_arrowChart`).

The space of arrows is an algebraic space
(`AlgebraicGeometry.Stack.GroupoidLift.StackChart.isAlgebraicSpace_arrSpace`); the identity of
`w` is a point of it over `Spec C`. Pulling an étale atlas back along that point and refining
(`GroupoidLift.BigFppfOver.exists_affine_surjective_etale_refinement_factor`) gives an affine `c`
surjective étale over `Spec C` and an affine `U₁` étale over the atlas through which the point
factors over `c`; `C₁ = Γ(c)`, `Q = Γ(U₁)`, and the chart is that of the point of `U₁`, which is
formally étale because `U₁` is étale over the space of arrows.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.exists_arrowChart`.
-/

@[expose] public section

open CategoryTheory Opposite Limits
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} (a : schemeFibredCategory B S hS U₀ ⟶ 𝒳)
  {P : SmallAlg (ringOf B S hS T') B.cutoff} (ι : specOver P ⟶ U₀)

open StackChart

/-- **A formally étale chart of the arrows of the groupoid of a chart near an identity.** For an
algebraic stack `𝒳` and a point `w : P → C`, there are a refinement `f : C ⟶ C₁`, surjective and
étale on spectra, a formally étale chart `b` of the arrows by a small algebra `Q` with source and
target given by `sV, tV : P → Q`, and a point `ε : Q → C₁` at which `b` is the identity of
`f ∘ w`. -/
theorem exists_arrowChart (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    {C : SmallAlg (ringOf B S hS T') B.cutoff} (w : P.obj →ₐ[ringOf B S hS T'] C.obj) :
    ∃ (C₁ : SmallAlg (ringOf B S hS T') B.cutoff) (f : C ⟶ C₁)
      (_ : Surjective ((BigFppfOver.toScheme B S hS).map (specOverMap f)))
      (_ : Etale ((BigFppfOver.toScheme B S hS).map (specOverMap f)))
      (Q : SmallAlg (ringOf B S hS T') B.cutoff) (b : Chart (stackArr a ι) Q.obj)
      (_ : b.IsFormallyEtale) (sV tV : P.obj →ₐ[ringOf B S hS T'] Q.obj)
      (_ : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q.obj →ₐ[ringOf B S hS T'] D.obj),
        (b.app D v).src = v.comp sV)
      (_ : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q.obj →ₐ[ringOf B S hS T'] D.obj),
        (b.app D v).tgt = v.comp tV)
      (ε : Q.obj →ₐ[ringOf B S hS T'] C₁.obj), b.app C₁ ε = Arr.idt (f.hom.hom.comp w) := by
  set X := arrSpace a ι
  set π := arrSpaceToBase a ι
  have hX := isAlgebraicSpace_arrSpace a ι h𝒳
  obtain ⟨r₀, hr₀⟩ := relToArr_surjective a ι (Arr.idt (a := a) (ι := ι) w)
  obtain ⟨U, aU, haS, haE⟩ := hX.exists_atlas
  set g : yoneda.obj (specOver C) ⟶ X := yonedaEquiv.symm r₀.1
  set hrep := haS.rep
  set q : hrep.pullback g ⟶ specOver C := hrep.snd g
  set k : hrep.pullback g ⟶ U := hrep.fst' g
  have hqs : Surjective ((BigFppfOver.toScheme B S hS).map q) := haS.property_snd g
  have hqe : Etale ((BigFppfOver.toScheme B S hS).map q) :=
    haE.2 g (hrep.fst g) q (hrep.isPullback g)
  obtain ⟨c, U₁, r, s, m, hc, hU₁, hrs, hre, hse, hms⟩ :=
    BigFppfOver.exists_affine_surjective_etale_refinement_factor inferInstance q hqs hqe k
  have := hc
  have := hU₁
  set ξ : X.obj (op U₁) := aU.app (op U₁) s
  have hξ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yonedaEquiv.symm ξ) := by
    rw [yonedaEquiv_symm_app_eq]
    exact MorphismProperty.comp_mem _ _ _
      ((Space.presheaf_yoneda_map_iff B S hS (P := @Etale.{u}) inferInstance _).mpr hse) haE
  set j₁ : U₁ ⟶ T' := π.app (op U₁) ξ
  set Q := sectionsAlg U₁ j₁
  set qQ := sectionsPoint π ξ
  have hqQ := formallyEtale_sectionsPoint π ξ hξ
  set jc : c ⟶ T' := r ≫ q ≫ specOverToBase C
  have hk : aU.app _ k = X.map q.op r₀.1 := by
    have h := Space.app_tautological_section_representing B S hS (hrep.isPullback g)
    have hf : (hrep.fst g).app (op (hrep.pullback g)) (𝟙 _) = k := by
      rw [← hrep.map_fst']
      exact Category.id_comp (obj := BigFppfOver B S hS) k
    rwa [hf] at h
  have hm : X.map m.op ξ = X.map (r ≫ q).op r₀.1 := by
    have h1 : X.map m.op ξ = aU.app _ (m ≫ s) := (NatTrans.naturality_apply aU m.op s).symm
    have h2 : aU.app _ (r ≫ k) = X.map r.op (aU.app _ k) := NatTrans.naturality_apply aU r.op k
    rw [h1, hms, h2, hk, ← Functor.map_comp_apply, ← op_comp]
  have hmj : m ≫ j₁ = jc := by
    have h := congrArg (π.app (op c)) hm
    rw [app_map_eq, app_map_eq, r₀.2] at h
    exact h.trans (Category.assoc _ _ _)
  set C₁ := sectionsAlg c jc
  have := hrs
  have := hre
  obtain ⟨f, hf⟩ := exists_specOverMap (T' := T') (C := C) (D := C₁)
    (sectionsHom c jc ≫ r ≫ q) (by
      rw [Category.assoc, Category.assoc]
      exact sectionsHom_comp c jc)
  refine ⟨C₁, f, ?_, ?_, Q, arrChart a ι Q qQ, arrChart_isFormallyEtale a ι Q qQ hqQ, _, _,
    arrChart_src a ι Q qQ, arrChart_tgt a ι Q qQ, (sectionsMap m hmj).hom.hom, ?_⟩
  iterate 2 (rw [hf, Functor.map_comp]; infer_instance)
  · rw [arrChart_app, ← relToArr_map]
    have hpt : (relPoints T' π).map (SmallAlg.homMk (sectionsMap m hmj).hom.hom) qQ =
        (relPoints T' π).map f r₀ := by
      apply Subtype.ext
      change X.map (specOverMap (sectionsMap m hmj)).op (X.map (sectionsHom U₁ j₁).op ξ) =
        X.map (specOverMap f).op r₀.1
      rw [← Functor.map_comp_apply, ← op_comp, specOverMap_sectionsMap, op_comp,
        Functor.map_comp_apply, hm, ← Functor.map_comp_apply, ← op_comp, hf]
    rw [hpt, relToArr_map, hr₀]
    exact Arr.map_idt f w

end AlgebraicGeometry.Stack.GroupoidLift

end
