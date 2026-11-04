module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.AffineExtensionSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentImpliesCartesian
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationQuasicoherentOnSite
public import StacksFrontier.AlgebraicGeometry.FiniteColimits.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationCokernel
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts

/-!
# A module of finite presentation through a quasi-coherent module on an affine space

Let `X` be an algebraic space with a terminal affine étale chart `T₀` (for instance an affine
algebraic space), `Q` a quasi-coherent `𝒪_X`-module, `W₁` an affine chart over which the sections
of `Q` are finitely presented, and `q` a global section of `Q`.  Then there are an `𝒪_X`-module
`H` of finite presentation, a morphism `ψ : H ⟶ Q` hitting `q`, which is bijective on the sections
over every affine chart mapping to `W₁`
(`AlgebraicGeometry.Space.AffineExtension.exists_isFinitePresentation_bijective_of_isTerminal`).

## The construction

Put `A = 𝒪(T₀)` and `M = Q(T₀)`.  The sections of `Q` over `W₁` are the base change of `M`
(Descent 03DX(2)), and `𝒪(W₁)` is flat over `A`, so by
`AlgebraicGeometry.Space.AffineExtension.exists_finset_generators_relations` there are finitely
many elements `x_i ∈ M`, containing the value of `q`, and finitely many relations `k_j` among
them over `A`, whose restrictions present `Q(W₁)`.  The `x_i` define `free X ⟶ Q`, the `k_j`
define `free R ⟶ free X`, and `H` is the cokernel (Stacks 0H98).  Over an affine chart `W`
mapping to `W₁` the restrictions of the `x_i` still generate `Q(W)` and those of the `k_j` still
generate the relations among them (again 03DX(2)), while the sections of `H` over `W` are the
cokernel of the sections of the two free modules, which gives bijectivity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.AffineExtension

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- Two global sections agreeing at a terminal chart are equal. -/
theorem sections_eq_of_isTerminal {T₀ : SmallEtale B S hS X} (hT₀ : IsTerminal T₀)
    (M : Modules.{u, u} B S hS X hX) {s t : M.val.sections}
    (h : s.val (op T₀) = t.val (op T₀)) : s = t := by
  rw [← sectionsOfTerminal_eval hT₀ M.val s, ← sectionsOfTerminal_eval hT₀ M.val t]
  exact congrArg _ h

/-- The map from the cokernel of a presentation `ρ` of free modules to `Q` is bijective on the
sections over an affine chart `W` on which the generators span and the relations generate. -/
theorem bijective_app_cokernel_desc {Xs Rs : Type u} {Q : Modules.{u, u} B S hS X hX}
    (ρ : SheafOfModules.free
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) Rs ⟶
      SheafOfModules.free
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) Xs)
    (φS : SheafOfModules.free
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) Xs ⟶ Q)
    (hcond : ρ ≫ φS = 0)
    (hF₀qc : (SheafOfModules.free
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)
          Xs).IsQuasicoherentOnSite)
    (hHqc : (cokernel ρ).IsQuasicoherentOnSite) {W : SmallEtale B S hS X}
    (hW : IsAffine ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).obj W))
    (z : Xs → Q.val.obj (op W)) (v : Rs → (Xs →₀ chartRing B S hS X hX W))
    (hφS : ∀ c : Xs →₀ chartRing B S hS X hX W,
      φS.val.app (op W) (Stacks.Sites.freeSectionsMap
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)
          Xs (op W) c) = Finsupp.linearCombination (chartRing B S hS X hX W) z c)
    (hρ : ∀ k : Rs,
      ρ.val.app (op W) (Stacks.Sites.freeSectionsMap
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)
          Rs (op W) (Finsupp.single k 1)) =
        Stacks.Sites.freeSectionsMap
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)
            Xs (op W) (v k))
    (hspan : Submodule.span (chartRing B S hS X hX W) (Set.range z) = ⊤)
    (hrel : ∀ c : Xs →₀ chartRing B S hS X hX W,
      Finsupp.linearCombination (chartRing B S hS X hX W) z c = 0 →
        c ∈ Submodule.span (chartRing B S hS X hX W) (Set.range v)) :
    Function.Bijective ((cokernel.desc ρ φS hcond).val.app (op W)) := by
  have hπψ : cokernel.π ρ ≫ cokernel.desc ρ φS hcond = φS := cokernel.π_desc _ _ _
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨s, rfl⟩ := surjective_val_app_of_epi_of_isQuasicoherentOnSite (cokernel.π ρ)
      inferInstance hF₀qc hHqc W hW t
    obtain ⟨c₀, rfl⟩ := (bijective_freeSectionsMap_of_isAffine B S hS X hX Xs W hW).2 s
    have hc₀ : Finsupp.linearCombination (chartRing B S hS X hX W) z c₀ = 0 := by
      rw [← hφS, ← hπψ]
      exact ht
    let Ψ := ((cokernel.π ρ).val.app (op W)).hom ∘ₗ (Stacks.Sites.freeSectionsMap
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)
        Xs (op W)).hom
    have hle : Submodule.span (chartRing B S hS X hX W) (Set.range v) ≤ LinearMap.ker Ψ := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      show (cokernel.π ρ).val.app (op W) (Stacks.Sites.freeSectionsMap
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)
          Xs (op W) _) = 0
      rw [← hρ]
      show ((ρ ≫ cokernel.π ρ).val.app (op W)) _ = 0
      rw [cokernel.condition]
      rfl
    exact hle (hrel c₀ hc₀)
  · intro y
    obtain ⟨c₀, rfl⟩ :
        y ∈ LinearMap.range (Finsupp.linearCombination (chartRing B S hS X hX W) z) := by
      rw [Finsupp.range_linearCombination, hspan]
      exact Submodule.mem_top
    refine ⟨(cokernel.π ρ).val.app (op W) (Stacks.Sites.freeSectionsMap
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)
        Xs (op W) c₀), ?_⟩
    rw [← hφS]
    show ((cokernel.π ρ ≫ cokernel.desc ρ φS hcond).val.app (op W)) _ = _
    rw [hπψ]

/-- A presentation `ρ` of free modules is killed by `φS` once the relations it encodes vanish at a
terminal chart. -/
theorem comp_eq_zero_of_isTerminal {Xs Rs : Type u} {Q : Modules.{u, u} B S hS X hX}
    {T₀ : SmallEtale B S hS X} (hT₀ : IsTerminal T₀)
    (ρ : SheafOfModules.free
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) Rs ⟶
      SheafOfModules.free
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) Xs)
    (φS : SheafOfModules.free
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) Xs ⟶ Q)
    (z : Xs → Q.val.obj (op T₀)) (v : Rs → (Xs →₀ chartRing B S hS X hX T₀))
    (hφS : ∀ c : Xs →₀ chartRing B S hS X hX T₀,
      φS.val.app (op T₀) (Stacks.Sites.freeSectionsMap
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)
          Xs (op T₀) c) = Finsupp.linearCombination (chartRing B S hS X hX T₀) z c)
    (hρ : ∀ k : Rs,
      ρ.val.app (op T₀) (Stacks.Sites.freeSectionsMap
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)
          Rs (op T₀) (Finsupp.single k 1)) =
        Stacks.Sites.freeSectionsMap
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)
            Xs (op T₀) (v k))
    (hv : ∀ k : Rs, Finsupp.linearCombination (chartRing B S hS X hX T₀) z (v k) = 0) :
    ρ ≫ φS = 0 := by
  refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) Rs) _ _
    fun k => ?_
  refine Eq.trans ?_ comp_zero.symm
  apply Q.unitHomEquiv.injective
  apply sections_eq_of_isTerminal B S hS hX hT₀ Q
  refine (congrArg (fun z => φS.val.app (op T₀) (ρ.val.app (op T₀) z))
    (Stacks.Sites.freeSectionsMap_single
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)
        Rs (op T₀) k 1).symm).trans ?_
  refine (congrArg (φS.val.app (op T₀)) (hρ k)).trans ((hφS _).trans ?_)
  rw [hv k]
  rfl

/-- Finitely many sections of `Q` over a terminal affine chart, containing `x`, and finitely many
relations among them, whose restrictions present `Q` over every affine chart mapping to `W₁`. -/
theorem exists_finset_generators_relations_of_isTerminal
    {T₀ : SmallEtale B S hS X} (hT₀ : IsTerminal T₀)
    (hT₀a : IsAffine ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).obj T₀))
    (Q : Modules.{u, u} B S hS X hX) (hQ : Q.IsQuasicoherentOnSite)
    {W₁ : SmallEtale B S hS X}
    (hW₁ : IsAffine ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).obj W₁))
    (hfp : Module.FinitePresentation (chartRing B S hS X hX W₁) (Q.val.obj (op W₁)))
    (x : Q.val.obj (op T₀)) :
    ∃ Xs : Finset (Q.val.obj (op T₀)), x ∈ Xs ∧ ∃ Rs : Finset (Xs →₀ chartRing B S hS X hX T₀),
      (∀ k ∈ Rs, Finsupp.linearCombination (chartRing B S hS X hX T₀)
        (fun i : Xs => (i : Q.val.obj (op T₀))) k = 0) ∧
      ∀ W : SmallEtale B S hS X,
        IsAffine ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Nonempty (W ⟶ W₁) →
            Submodule.span (chartRing B S hS X hX W)
                (Set.range (α := Q.val.obj (op W))
                  fun i : Xs => Q.val.map (hT₀.from W).op (i : Q.val.obj (op T₀))) = ⊤ ∧
              ∀ c : Xs →₀ chartRing B S hS X hX W,
                Finsupp.linearCombination (chartRing B S hS X hX W) (M := Q.val.obj (op W))
                    (fun i : Xs => Q.val.map (hT₀.from W).op (i : Q.val.obj (op T₀))) c = 0 →
                  c ∈ Submodule.span (chartRing B S hS X hX W) (Set.range fun k : Rs =>
                    Finsupp.mapRange (chartRestrict (hF := hX) (hT₀.from W)) (map_zero _)
                      (k : Xs →₀ chartRing B S hS X hX T₀)) := by
  classical
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X hX Q hQ
  let f₁ : W₁ ⟶ T₀ := hT₀.from W₁
  obtain ⟨Xs, hx, Rs, hR, hspan, hrel⟩ := by
    let := chartAlgebra (hF := hX) f₁
    let := chartSectionsModule Q f₁
    have := chartSections_isScalarTower Q f₁
    have := moduleFlat_chartRing_of_isAffine (hF := hX) f₁ hT₀a hW₁
    exact exists_finset_generators_relations (chartRestrictLinear Q f₁)
      (hcart T₀ W₁ hT₀a hW₁ f₁) x
  refine ⟨Xs, hx, Rs, hR, fun W hW hf => ?_⟩
  obtain ⟨f⟩ := hf
  have hfrom : hT₀.from W = f ≫ f₁ := hT₀.hom_ext _ _
  let := chartAlgebra (hF := hX) f₁
  let := chartSectionsModule Q f₁
  let := chartAlgebra (hF := hX) f
  let := chartSectionsModule Q f
  have := chartSections_isScalarTower Q f
  have hb := hcart W₁ W hW₁ hW f
  have hfun : (chartRestrictLinear Q f ∘ fun i : Xs =>
      chartRestrictLinear Q f₁ (i : Q.val.obj (op T₀))) =
        ((fun i : Xs => Q.val.map (hT₀.from W).op (i : Q.val.obj (op T₀)) :
              Xs → Q.val.obj (op W))) := by
    funext i
    show Q.val.map f.op (Q.val.map f₁.op _) = Q.val.map (hT₀.from W).op _
    rw [hfrom, op_comp]
    exact (PresheafOfModules.map_comp_apply Q.val f₁.op f.op _).symm
  have hv : (fun k : Rs => finsuppAlgebraMap (chartRing B S hS X hX W₁)
      (chartRing B S hS X hX W) Xs (finsuppAlgebraMap (chartRing B S hS X hX T₀)
        (chartRing B S hS X hX W₁) Xs (k : Xs →₀ chartRing B S hS X hX T₀))) =
      fun k : Rs => Finsupp.mapRange (chartRestrict (hF := hX) (hT₀.from W)) (map_zero _)
        (k : Xs →₀ chartRing B S hS X hX T₀) := by
    funext k
    ext i
    simp only [finsuppAlgebraMap, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
      Algebra.linearMap_apply]
    rw [hfrom, chartRestrict_comp]
    rfl
  have h1 := span_range_comp_eq_top (chartRestrictLinear Q f) hb.2 _ hspan
  have h2 := mem_span_of_linearCombination_eq_zero (chartRestrictLinear Q f) hb.1 _ hspan
    (fun k : Rs => finsuppAlgebraMap (chartRing B S hS X hX T₀) (chartRing B S hS X hX W₁) Xs
      (k : Xs →₀ chartRing B S hS X hX T₀))
    fun c hc => by
      have h := hrel c hc
      rwa [Set.image_eq_range] at h
  rw [hfun] at h1
  rw [hfun, hv] at h2
  exact ⟨h1, h2⟩

/-- **A module of finite presentation through a quasi-coherent module, bijective over the
affine charts over a given affine chart.** -/
theorem exists_isFinitePresentation_bijective_of_isTerminal
    {T₀ : SmallEtale B S hS X} (hT₀ : IsTerminal T₀)
    (hT₀a : IsAffine ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).obj T₀))
    (Q : Modules.{u, u} B S hS X hX) (hQ : Q.IsQuasicoherentOnSite)
    {W₁ : SmallEtale B S hS X}
    (hW₁ : IsAffine ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).obj W₁))
    (hfp : Module.FinitePresentation (chartRing B S hS X hX W₁) (Q.val.obj (op W₁)))
    (q : Q.val.sections) :
    ∃ (H : Modules.{u, u} B S hS X hX) (_ : H.IsFinitePresentation) (ψ : H ⟶ Q)
      (h : H.val.sections), PresheafOfModules.sectionsMap ψ.val h = q ∧
        ∀ W : SmallEtale B S hS X,
          IsAffine ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).obj W) →
            Nonempty (W ⟶ W₁) → Function.Bijective (ψ.val.app (op W)) := by
  classical
  let Rg := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O
  obtain ⟨Xs, hqX, Rs, hR, hpres⟩ := exists_finset_generators_relations_of_isTerminal
    B S hS hX hT₀ hT₀a Q hQ hW₁ hfp (q.val (op T₀))
  let sec : Q.val.obj (op T₀) → Q.val.sections := sectionsOfTerminal hT₀ Q.val
  let φS : SheafOfModules.free (R := Rg) Xs ⟶ Q :=
    Q.freeHomEquiv.symm fun i => sec (i : Q.val.obj (op T₀))
  let F₀ := SheafOfModules.free (R := Rg) Xs
  let ρ : SheafOfModules.free (R := Rg) Rs ⟶ F₀ :=
    F₀.freeHomEquiv.symm fun k => sectionsOfTerminal hT₀ F₀.val
      (Stacks.Sites.freeSectionsMap (R := Rg) Xs (op T₀) (k : Xs →₀ chartRing B S hS X hX T₀))
  have hφS : ∀ (W : SmallEtale B S hS X) (c : Xs →₀ chartRing B S hS X hX W),
      φS.val.app (op W) (Stacks.Sites.freeSectionsMap (R := Rg) Xs (op W) c) =
        Finsupp.linearCombination (chartRing B S hS X hX W) (M := Q.val.obj (op W))
          (fun i : Xs => Q.val.map (hT₀.from W).op (i : Q.val.obj (op T₀))) c := fun W c =>
    freeHomEquiv_symm_app_freeSectionsMap Q _ (op W) c
  have hρ : ∀ (W : SmallEtale B S hS X) (k : Rs),
      ρ.val.app (op W) (Stacks.Sites.freeSectionsMap (R := Rg) Rs (op W) (Finsupp.single k 1)) =
        Stacks.Sites.freeSectionsMap (R := Rg) Xs (op W)
          (Finsupp.mapRange (chartRestrict (hF := hX) (hT₀.from W)) (map_zero _)
            (k : Xs →₀ chartRing B S hS X hX T₀)) := fun W k => by
    refine (freeHomEquiv_symm_app_freeSectionsMap F₀ _ (op W) _).trans ?_
    rw [Finsupp.linearCombination_single, one_smul]
    exact map_freeSectionsMap (R := Rg) (hT₀.from W).op _
  have hcond : ρ ≫ φS = 0 := by
    refine comp_eq_zero_of_isTerminal B S hS hX hT₀ ρ φS _ _ (hφS T₀) (hρ T₀) fun k => ?_
    have h00 : hT₀.from T₀ = 𝟙 T₀ := hT₀.hom_ext _ _
    have hmr : Finsupp.mapRange (chartRestrict (hF := hX) (hT₀.from T₀)) (map_zero _)
        (k : Xs →₀ chartRing B S hS X hX T₀) = k := by
      ext i
      rw [Finsupp.mapRange_apply, h00, chartRestrict_id]
      rfl
    have hres0 : ∀ y : Q.val.obj (op T₀), Q.val.map (hT₀.from T₀).op y = y := fun y => by
      rw [h00]
      exact PresheafOfModules.map_id_apply Q.val (op T₀) y
    rw [hmr, funext fun i : Xs => hres0 (i : Q.val.obj (op T₀))]
    exact hR k k.2
  refine ⟨cokernel ρ, Stacks.SheafOfModules.LocalCokernel.isFinitePresentation_cokernel
      (smallEtaleRingedSite B S hS X hX) ρ, cokernel.desc ρ φS hcond,
    SheafOfModules.sectionsMap (cokernel.π ρ)
      (SheafOfModules.freeSection (⟨q.val (op T₀), hqX⟩ : Xs)), ?_, fun W hW h => ?_⟩
  · show SheafOfModules.sectionsMap (cokernel.π ρ ≫ cokernel.desc ρ φS hcond) _ = q
    rw [cokernel.π_desc, SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection]
    exact sectionsOfTerminal_eval hT₀ Q.val q
  · exact bijective_app_cokernel_desc B S hS hX ρ φS hcond
      (Stacks.SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentation F₀)
      (Stacks.SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentation (cokernel ρ)) hW _ _
      (hφS W) (hρ W) (hpres W hW h).1 (hpres W hW h).2

end AlgebraicGeometry.Space.AffineExtension

end
