module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.StrictMajorant
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.ProIsomorphismOfKernelSystems
public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProMorphisms
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MittagLeffler
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimBasic
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimHom
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimTriangle
public import StacksFrontier.CategoryTheory.MittagLefflerSections
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphism.LimAndRlimOne

/-!
# Derived limits of pro-isomorphic inverse systems

Derived limits of pro-isomorphic inverse systems in a pretriangulated category are isomorphic,
non-canonically (Tag 0H9L): the isomorphism is produced from a morphism of the two defining
triangles, and is seen to be an isomorphism by comparing the Milnor sequences of the two systems
for maps out of every object.
-/


section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Opposite Pretriangulated

namespace Rlim.Pro

universe v u w u'

private def mapProIso {C : Type u} [Category.{v} C] {E : Type u'} [Category.{w} E]
    {F G : ℕᵒᵖ ⥤ C} (a : InverseSequence.ProIso F G) (H : C ⥤ E) :
    InverseSequence.ProIso (F ⋙ H) (G ⋙ H) where
  α := a.α
  β := a.β
  αmono := a.αmono
  βmono := a.βmono
  αle := a.αle
  βle := a.βle
  φ n := H.map (a.φ n)
  ψ n := H.map (a.ψ n)
  φnat h := by
    simpa only [InverseSequence.tr, Functor.comp_map, ← H.map_comp] using congrArg H.map (a.φnat h)
  ψnat h := by
    simpa only [InverseSequence.tr, Functor.comp_map, ← H.map_comp] using congrArg H.map (a.ψnat h)
  ψφ n := by
    simpa only [InverseSequence.tr, Functor.comp_map, ← H.map_comp] using congrArg H.map (a.ψφ n)
  φψ n := by
    simpa only [InverseSequence.tr, Functor.comp_map, ← H.map_comp] using congrArg H.map (a.φψ n)

private lemma refined_naturality {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} (a : InverseSequence.ProIso F G) {n m : ℕ} (h : n ≤ m) :
    InverseSequence.tr F (Nat.add_le_add (a.αmono h) h) ≫
        (InverseSequence.tr F (Nat.le_add_right (a.α n) n) ≫ a.φ n) =
      (InverseSequence.tr F (Nat.le_add_right (a.α m) m) ≫ a.φ m) ≫ InverseSequence.tr G h := by
  have e : InverseSequence.tr F (Nat.add_le_add (a.αmono h) h) ≫
      InverseSequence.tr F (Nat.le_add_right (a.α n) n) =
      InverseSequence.tr F (Nat.le_add_right (a.α m) m) ≫ InverseSequence.tr F (a.αmono h) := by
    simp only [InverseSequence.tr, ← F.map_comp]
    rfl
  rw [← Category.assoc, e, Category.assoc, a.φnat, Category.assoc]

private def refinedRep {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} (a : InverseSequence.ProIso F G) (H : C ⥤ Ab.{w}) :
    SequentialRep (F ⋙ H) (G ⋙ H) where
  index n := a.α n + n
  index_strict := fun n m h => Nat.add_lt_add_of_le_of_lt (a.αmono h.le) h
  index_le n := Nat.le_add_left n (a.α n)
  component n := H.map (InverseSequence.tr F (Nat.le_add_right (a.α n) n) ≫ a.φ n)
  naturality h := by
    simpa only [Functor.comp_map, InverseSequence.tr, ← H.map_comp] using
      congrArg H.map (refined_naturality a h)

private lemma refinedRep_represents {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} (a : InverseSequence.ProIso F G) (H : C ⥤ Ab.{w})
    (φ : proYoneda (G ⋙ H) ⟶ proYoneda (F ⋙ H))
    (hφ : proIsoRepresents (mapProIso a H) φ) :
    (refinedRep a H).Represents φ := by
  intro n
  rw [hφ n]
  dsimp [refinedRep, mapProIso]
  have e := congrArg (fun f => f.app (H.obj (G.obj (op n))))
    (colimit.w ((F ⋙ H).op ⋙ coyoneda)
      (show op (op (a.α n)) ⟶ op (op (a.α n + n)) from
        ((homOfLE (Nat.le_add_right (a.α n) n)).op).op))
  have e' := congrArg (fun f => f (H.map (a.φ n))) e
  simpa [InverseSequence.tr, Functor.map_comp] using e'.symm

private def proIsoProductFirst {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} [HasProduct fun n : ℕ => F.obj (op n)]
    [HasProduct fun n : ℕ => G.obj (op n)] (a : InverseSequence.ProIso F G) :
    (∏ᶜ fun n : ℕ => F.obj (op n)) ⟶ ∏ᶜ fun n : ℕ => G.obj (op n) :=
  Pi.lift fun n => Pi.π _ (a.α n + n) ≫
    InverseSequence.tr F (Nat.le_add_right (a.α n) n) ≫ a.φ n

private def proIsoProductSecond {C : Type u} [Category.{v} C] [Preadditive C]
    {F G : ℕᵒᵖ ⥤ C} [HasProduct fun n : ℕ => F.obj (op n)]
    [HasProduct fun n : ℕ => G.obj (op n)] (a : InverseSequence.ProIso F G) :
    (∏ᶜ fun n : ℕ => F.obj (op n)) ⟶ ∏ᶜ fun n : ℕ => G.obj (op n) :=
  Pi.lift fun n => ∑ k ∈ Finset.Ico (a.α n + n) (a.α (n + 1) + (n + 1)),
    if h : a.α n + n ≤ k then
      Pi.π _ k ≫ InverseSequence.tr F h ≫ InverseSequence.tr F (Nat.le_add_right (a.α n) n) ≫ a.φ n
    else 0

private lemma comparison_productFirst {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} [HasProduct fun n : ℕ => F.obj (op n)]
    [HasProduct fun n : ℕ => G.obj (op n)] (a : InverseSequence.ProIso F G) (H : C ⥤ Ab.{w}) :
    piComparison H (fun n : ℕ => F.obj (op n)) ≫ (refinedRep a H).productFirst =
      H.map (proIsoProductFirst a) ≫ piComparison H (fun n : ℕ => G.obj (op n)) := by
  apply Pi.hom_ext
  intro n
  simp only [SequentialRep.productFirst, refinedRep, proIsoProductFirst,
    Functor.comp_obj, Pi.map', Category.assoc, Pi.lift_comp_π, piComparison_comp_π_assoc,
    ← H.map_comp, map_lift_piComparison_assoc]

private lemma comparison_productSecond {C : Type u} [Category.{v} C] [Preadditive C]
    {F G : ℕᵒᵖ ⥤ C} [HasProduct fun n : ℕ => F.obj (op n)]
    [HasProduct fun n : ℕ => G.obj (op n)] (a : InverseSequence.ProIso F G)
    (H : C ⥤ Ab.{w}) [H.Additive] :
    piComparison H (fun n : ℕ => F.obj (op n)) ≫ (refinedRep a H).productSecond =
      H.map (proIsoProductSecond a) ≫ piComparison H (fun n : ℕ => G.obj (op n)) := by
  apply Pi.hom_ext
  intro n
  simp only [SequentialRep.productSecond, refinedRep, proIsoProductSecond,
    Functor.comp_obj, Functor.comp_map, Category.assoc, Pi.lift_comp_π,
    map_lift_piComparison, Functor.map_sum,
    Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> simp [InverseSequence.tr, Functor.map_comp]


private lemma comparison_delta {D : Type u} [Category.{v} D] [Preadditive D]
    (F : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ => F.obj (op n)]
    (H : D ⥤ Ab.{w}) [H.Additive] :
    piComparison H (fun n : ℕ => F.obj (op n)) ≫ Rlim.delta (F ⋙ H) =
      H.map (Rlim.Hom.systemDelta F) ≫ piComparison H (fun n : ℕ => F.obj (op n)) := by
  apply Pi.hom_ext
  intro n
  simp [Rlim.delta, Rlim.shift, Rlim.product,
    Functor.comp_obj, Rlim.Hom.systemDelta,
    Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc, Functor.map_comp]

private lemma productDelta_comm {D : Type u} [Category.{v} D] [Preadditive D]
    {F G : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ => F.obj (op n)]
    [HasProduct fun n : ℕ => G.obj (op n)] (a : InverseSequence.ProIso F G) :
    Rlim.Hom.systemDelta F ≫ proIsoProductSecond a =
      proIsoProductFirst a ≫ Rlim.Hom.systemDelta G := by
  let H := preadditiveCoyoneda.obj (op (Rlim.Hom.systemProduct F))
  have : PreservesLimitsOfSize.{0, 0} H := preservesSmallestLimits_of_preservesLimits H
  let cF := piComparison H (fun n : ℕ => F.obj (op n))
  let cG := piComparison H (fun n : ℕ => G.obj (op n))
  have : IsIso cG := by dsimp [cG]; infer_instance
  obtain ⟨_, _, _, _, _, _, _, hδ, _⟩ :=
    exists_map_lim_and_cokernel_delta.{v,u}
  have e : H.map (Rlim.Hom.systemDelta F ≫ proIsoProductSecond a) ≫ cG =
      H.map (proIsoProductFirst a ≫ Rlim.Hom.systemDelta G) ≫ cG := by
    calc
      _ = cF ≫ (Rlim.delta (F ⋙ H) ≫ (refinedRep a H).productSecond) := by
        simp only [Functor.map_comp, Category.assoc]
        rw [← comparison_productSecond, ← Category.assoc, ← comparison_delta]
        rfl
      _ = cF ≫ ((refinedRep a H).productFirst ≫ Rlim.delta (G ⋙ H)) := by
        rw [hδ (F ⋙ H) (G ⋙ H) (refinedRep a H)]
      _ = _ := by
        simp only [Functor.map_comp, ← Category.assoc]
        rw [comparison_productFirst]
        simp only [Category.assoc]
        rw [comparison_delta]
  have e' := (cancel_mono cG).mp e
  have e'' := congrArg (fun f => f.hom (𝟙 (Rlim.Hom.systemProduct F))) e'
  change (𝟙 _ ≫ _) = (𝟙 _ ≫ _) at e''
  simpa only [Category.id_comp] using e''

/-- The first product map of `refinedRep a H` is the conjugate of `H.map (proIsoProductFirst a)`
by the product comparison isomorphisms. -/
private lemma productFirst_eq_inv_comp {C : Type u} [Category.{v} C]
    {F G : ℕᵒᵖ ⥤ C} [HasProduct fun n : ℕ => F.obj (op n)]
    [HasProduct fun n : ℕ => G.obj (op n)] (a : InverseSequence.ProIso F G) (H : C ⥤ Ab.{w})
    [IsIso (piComparison H (fun n : ℕ => F.obj (op n)))] :
    (refinedRep a H).productFirst = inv (piComparison H (fun n : ℕ => F.obj (op n))) ≫
      H.map (proIsoProductFirst a) ≫ piComparison H (fun n : ℕ => G.obj (op n)) := by
  rw [← comparison_productFirst, IsIso.inv_hom_id_assoc]

/-- The second product map of `refinedRep a H` is the conjugate of `H.map (proIsoProductSecond a)`
by the product comparison isomorphisms. -/
private lemma productSecond_eq_inv_comp {C : Type u} [Category.{v} C] [Preadditive C]
    {F G : ℕᵒᵖ ⥤ C} [HasProduct fun n : ℕ => F.obj (op n)]
    [HasProduct fun n : ℕ => G.obj (op n)] (a : InverseSequence.ProIso F G) (H : C ⥤ Ab.{w})
    [H.Additive] [IsIso (piComparison H (fun n : ℕ => F.obj (op n)))] :
    (refinedRep a H).productSecond = inv (piComparison H (fun n : ℕ => F.obj (op n))) ≫
      H.map (proIsoProductSecond a) ≫ piComparison H (fun n : ℕ => G.obj (op n)) := by
  rw [← comparison_productSecond, IsIso.inv_hom_id_assoc]

private lemma exists_milnor_maps {D : Type u} [Category.{v} D]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {F G : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ => F.obj (op n)]
    [HasProduct fun n : ℕ => G.obj (op n)] (a : InverseSequence.ProIso F G) (L : D) :
    ∃ (b : limit (Rlim.Hom.homSystem L F) ⟶ limit (Rlim.Hom.homSystem L G))
      (hδ : Rlim.delta (Rlim.Hom.shiftedHomSystem L F) ≫
          Rlim.Hom.shiftedHomProductMap L F G (proIsoProductSecond a) =
        Rlim.Hom.shiftedHomProductMap L F G (proIsoProductFirst a) ≫
          Rlim.delta (Rlim.Hom.shiftedHomSystem L G)),
      IsIso b ∧
      IsIso (cokernel.map (Rlim.delta (Rlim.Hom.shiftedHomSystem L F))
        (Rlim.delta (Rlim.Hom.shiftedHomSystem L G))
        (Rlim.Hom.shiftedHomProductMap L F G (proIsoProductFirst a))
        (Rlim.Hom.shiftedHomProductMap L F G (proIsoProductSecond a)) hδ) ∧
      Rlim.limitToProduct (Rlim.Hom.homSystem L F) ≫
          Rlim.Hom.homProductMap L F G (proIsoProductFirst a) =
        b ≫ Rlim.limitToProduct (Rlim.Hom.homSystem L G) := by
  let H := preadditiveCoyoneda.obj (op L)
  let J := shiftFunctor D (-1 : ℤ) ⋙ H
  have : PreservesLimitsOfSize.{0, 0} H := preservesSmallestLimits_of_preservesLimits H
  have : PreservesLimitsOfSize.{0, 0} J := preservesSmallestLimits_of_preservesLimits J
  have : IsIso (piComparison H (fun n : ℕ => F.obj (op n))) := inferInstance
  have : IsIso (piComparison J (fun n : ℕ => F.obj (op n))) := inferInstance
  obtain ⟨mapLim, mapR1lim, _, _, _, _, _, _, _, _, _, _, _, hiso, hcompat⟩ :=
    exists_map_lim_and_cokernel_delta.{v,u}
  have e₀ := productFirst_eq_inv_comp a H
  have e₁ := productFirst_eq_inv_comp a J
  have e₂ := productSecond_eq_inv_comp a J
  obtain ⟨φ₀, hφ₀, _, hb, _⟩ := hiso (F ⋙ H) (G ⋙ H) (mapProIso a H)
  obtain ⟨φ₁, hφ₁, _, _, hc⟩ := hiso (F ⋙ J) (G ⋙ J) (mapProIso a J)
  obtain ⟨hδ, hlim, hcoker⟩ := hcompat F G L (proIsoProductFirst a) (proIsoProductSecond a)
    φ₀ φ₁ (refinedRep a H) (refinedRep a J)
    (refinedRep_represents a H φ₀ hφ₀) (refinedRep_represents a J φ₁ hφ₁) e₀ e₁ e₂
  exact ⟨mapLim _ _ φ₀, hδ, hb, hcoker ▸ hc, hlim⟩

public lemma triangle_morphism {D : Type u} [Category.{v} D]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {T U : Triangle D} (hT : T ∈ distTriang D) (hU : U ∈ distTriang D)
    (f₂ : T.obj₂ ⟶ U.obj₂) (f₃ : T.obj₃ ⟶ U.obj₃)
    (h : T.mor₂ ≫ f₃ = f₂ ≫ U.mor₂) :
    ∃ f : T ⟶ U, f.hom₂ = f₂ ∧ f.hom₃ = f₃ := by
  obtain ⟨f₁, h₁, h₃⟩ := complete_distinguished_triangle_morphism₁ T U hT hU f₂ f₃ h
  exact ⟨⟨f₁, f₂, f₃, h₁, h, h₃⟩, rfl, rfl⟩

/-- **Stacks 0H9L.** Derived limits of pro-isomorphic inverse systems in a pretriangulated
category are non-canonically isomorphic. -/
@[stacks 0H9L]
public theorem nonempty_iso_of_isDerivedLimit_of_pro_isomorphism
    {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F G : CategoryTheory.Functor ℕᵒᵖ D) [HasProduct fun n : ℕ => F.obj (op n)]
    [HasProduct fun n : ℕ => G.obj (op n)] (K M : D)
    (hK : Pretriangulated.IsDerivedLimit F K) (hM : Pretriangulated.IsDerivedLimit G M)
    (a : InverseSequence.ProIso F G) : Nonempty (K ≅ M) := by
  obtain ⟨pK, dK, htK⟩ := hK
  obtain ⟨pM, dM, htM⟩ := hM
  let tK : Rlim.Hom.DerivedLimitTriangle F K := ⟨pK, dK, htK⟩
  let tM : Rlim.Hom.DerivedLimitTriangle G M := ⟨pM, dM, htM⟩
  obtain ⟨f, hf₂, hf₃⟩ := triangle_morphism tK.distinguished tM.distinguished
    (proIsoProductFirst a) (proIsoProductSecond a) (productDelta_comm a)
  have : IsIso f.hom₁ := by
    apply isIso_of_yoneda_map_bijective
    intro L
    let H := preadditiveCoyoneda.obj (op L)
    obtain ⟨s, S, hS⟩ := Rlim.Hom.hom_into_isDerivedLimit_shortExact F K L ⟨pK, dK, htK⟩
    obtain ⟨e, he₂, he₃⟩ := triangle_morphism s.distinguished tK.distinguished
      (𝟙 _) (𝟙 _) (by simp)
    have : IsIso e.hom₁ := isIso₁_of_isIso₂₃ e s.distinguished tK.distinguished
      (he₂ ▸ inferInstance) (he₃ ▸ inferInstance)
    let g : s.triangle ⟶ tM.triangle := e ≫ f
    have hg₂ : g.hom₂ = proIsoProductFirst a := by simp [g, he₂, hf₂]
    have hg₃ : g.hom₃ = proIsoProductSecond a := by simp [g, he₃, hf₃]
    obtain ⟨b, hδ, hb, hc, hlim⟩ := exists_milnor_maps a L
    obtain ⟨SG, hδ', hi, hp⟩ := hS G M tM g b (by simpa only [hg₂] using hlim)
    let c := cokernel.map (Rlim.delta (Rlim.Hom.shiftedHomSystem L F))
      (Rlim.delta (Rlim.Hom.shiftedHomSystem L G))
      (Rlim.Hom.shiftedHomProductMap L F G g.hom₂)
      (Rlim.Hom.shiftedHomProductMap L F G g.hom₃) hδ'
    have hc' : IsIso c := by simpa only [c, hg₂, hg₃] using hc
    let φ : ShortComplex.mk S.inclusion S.projection S.zero ⟶
        ShortComplex.mk SG.inclusion SG.projection SG.zero :=
      ⟨c, H.map g.hom₁, b, hi, hp.symm⟩
    have : IsIso (H.map g.hom₁) :=
      ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' φ S.shortExact SG.shortExact hc' hb
    have : IsIso (H.map f.hom₁) := by
      have : IsIso (H.map e.hom₁ ≫ H.map f.hom₁) := by
        simpa only [g, Pretriangulated.comp_hom₁, Functor.map_comp] using
          (inferInstance : IsIso (H.map g.hom₁))
      exact IsIso.of_isIso_comp_left (H.map e.hom₁) (H.map f.hom₁)
    exact ConcreteCategory.bijective_of_isIso (H.map f.hom₁)
  exact ⟨asIso f.hom₁⟩

end Rlim.Pro

end

end
