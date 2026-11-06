module

public import StacksFrontier.AlgebraicGeometry.Spaces.ExcisionPushforwardSection

/-!
# The base change of the presheaf of pairs is the given modification

Keep the data of `StacksFrontier/AlgebraicGeometry/Spaces/ExcisionPushforwardSection.lean`: a
separated étale `f : V ⟶ W` of algebraic spaces over a scheme `S`, a subfunctor `T` of `W`
whose preimage is carried isomorphically onto it, a subfunctor `W₀` containing the open
complement of `T`, and `h : Y ⟶ V` which is an isomorphism over `f^{-1}W₀`.

The presheaf of pairs `X` of
`StacksFrontier/AlgebraicGeometry/Spaces/ExcisionPushforward.lean` carries a canonical morphism
from `Y` over `W`, namely the one whose pair at a section `φ` of `Y` is `(φ ≫ h ≫ f, …)`, and
the induced morphism `Y ⟶ X ×_{g, W} V` over `V` is an isomorphism. This is the step
`X ×_{g, W, f} V = Y` of the proof of Stacks 0BGY.

The second component of the canonical pair is the morphism `Y ×_W V ⟶ Y` over `V` amalgamated
from the identity on the diagonal piece of `V ×_W V` and from the unique lift on the
complementary piece; the amalgamation is
`AlgebraicGeometry.Space.excisionGlue_exists`, and that it restricts to the identity on the
graph of `h` is what makes the induced morphism an isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.excisionDiagLift`: the morphism `Y ×_W V ⟶ Y` over `V` which is the
  identity on the graph of `h`.
* `AlgebraicGeometry.Space.excisionUnit`: the induced morphism `Y ⟶ X` over `W`.
* `AlgebraicGeometry.Space.excisionBaseChangeHom`: the induced morphism
  `Y ⟶ X ×_{g, W} V` over `V`.

## Main results

* `AlgebraicGeometry.Space.isIso_excisionBaseChangeHom`: **the base change of the presheaf of
  pairs along `f` is `Y`.**
* `AlgebraicGeometry.Space.excisionBaseChangeIso`: that isomorphism read in the slice category
  over `V`.

## Implementation notes

Invertibility is checked on sections, through
`CategoryTheory.NatIso.isIso_of_isIso_app`: a section of a presheaf over a scheme is a morphism
out of the representable presheaf of that scheme, and for such a source the second component of
a pair can be *evaluated* at the graph of its first component, which is
`AlgebraicGeometry.Space.pairEval`. Injectivity is then
`AlgebraicGeometry.Space.relativeMorphism_ext_of_pairEval` together with the computation that
the evaluation of the canonical pair at `φ` is `φ`, and surjectivity is the same computation
read backwards.

No universal property of the fibre product `X ×_{g, W} V` for an arbitrary test presheaf is
used, and none is available: the pair attached to a morphism `P ⟶ X` can only be evaluated when
`P` is representable, since the evaluation is the restriction of the second component along a
section.

## References

* [Stacks Project, Tag 05Y1](https://stacks.math.columbia.edu/tag/05Y1)
* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance high] hasPullbacks_presheaf_ExcisionPushforwardGluing
  hasPullback_presheaf_ExcisionPushforwardGluing

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {V W Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ W) (h : Y ⟶ V)
  (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W)
  (hY : IsAlgebraicSpace B S hS Y) (T W₀ : Subfunctor W)
  (hT : IsIso (T.fromPreimage f)) (hcompl : openComplement B S hS T ≤ W₀)
  (hf : IsEtale B S hS f) (hsep : IsSeparated B S hS f)
  (hiso : IsIso (pullback.snd h (W₀.preimage f).ι))

/-- A section of a presheaf is the morphism it names out of a representable presheaf. -/
private theorem app_eq_yonedaEquiv {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ G)
    {A : (BigFppfOver B S hS)ᵒᵖ} (t : F.obj A) :
    p.app A t = yonedaEquiv (yonedaEquiv.symm t ≫ p) := by
  rw [yonedaEquiv_symm_naturality_right, Equiv.apply_symm_apply]

/-! ### The canonical morphism `Y ×_W V ⟶ Y` -/

include hV hW hY hf hsep hT hcompl hiso in
/-- **The morphism `Y ×_W V ⟶ Y` over `V` which is the identity on the graph of `h`.** On the
diagonal piece of `V ×_W V` it is the first projection, and on the complementary piece it is the
unique lift of the second projection. -/
theorem exists_excisionDiagLift :
    ∃ b : pullback (h ≫ f) f ⟶ Y, b ≫ h = pullback.snd (h ≫ f) f ∧
      graphSection B S hS f h ≫ b = 𝟙 Y := by
  have hdiag := diagPreimage_comp_fst_eq_snd B S hS f hV hW hf hsep (graphKappa B S hS f h)
  simp only [graphKappa_fst, graphKappa_snd] at hdiag
  obtain ⟨b, hb₁, hb₂⟩ := excisionGlue_exists B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso
    (graphKappa B S hS f h) (isAlgebraicSpace_pullback B S hS (h ≫ f) f hY hV hW)
    (((diagOpen B S hS f).preimage (graphKappa B S hS f h)).ι ≫ pullback.fst (h ≫ f) f)
    (by simp only [Category.assoc, graphKappa_snd]; exact hdiag)
  refine ⟨b, by rw [hb₁, graphKappa_snd], ?_⟩
  have hkappa : graphSection B S hS f h ≫ graphKappa B S hS f h = h ≫ pullback.diagonal f := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, graphKappa_fst, graphSection_fst_assoc, pullback.diagonal_fst,
        Category.comp_id]
    · simp only [Category.assoc, graphKappa_snd, graphSection_snd, pullback.diagonal_snd,
        Category.comp_id]
  have hrange : Subfunctor.range (graphSection B S hS f h) ≤
      (diagOpen B S hS f).preimage (graphKappa B S hS f h) := by
    rw [← Subfunctor.image_le_iff, ← Subfunctor.range_comp, hkappa,
      diagOpen_eq_range B S hS f hV hW hf hsep]
    exact Subfunctor.range_comp_le _ _
  have hlift : Subfunctor.lift (graphSection B S hS f h) hrange ≫
      ((diagOpen B S hS f).preimage (graphKappa B S hS f h)).ι = graphSection B S hS f h :=
    Subfunctor.lift_ι _ _
  calc graphSection B S hS f h ≫ b
      = Subfunctor.lift (graphSection B S hS f h) hrange ≫
          (((diagOpen B S hS f).preimage (graphKappa B S hS f h)).ι ≫ b) := by
        rw [← Category.assoc, hlift]
    _ = graphSection B S hS f h ≫ pullback.fst (h ≫ f) f := by
        rw [hb₂, ← Category.assoc, hlift]
    _ = 𝟙 Y := graphSection_fst B S hS f h

/-- The morphism `Y ×_W V ⟶ Y` over `V` which is the identity on the graph of `h`. -/
noncomputable def excisionDiagLift : pullback (h ≫ f) f ⟶ Y :=
  (exists_excisionDiagLift B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso).choose

/-- The morphism `Y ×_W V ⟶ Y` is a morphism over `V`. -/
theorem excisionDiagLift_comp :
    excisionDiagLift B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso ≫ h =
      pullback.snd (h ≫ f) f :=
  (exists_excisionDiagLift B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso).choose_spec.1

/-- The morphism `Y ×_W V ⟶ Y` is the identity on the graph of `h`. -/
theorem graphSection_comp_excisionDiagLift :
    graphSection B S hS f h ≫
        excisionDiagLift B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso = 𝟙 Y :=
  (exists_excisionDiagLift B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso).choose_spec.2

/-! ### The induced morphism to the presheaf of pairs -/

/-- The canonical pair attached to `h`. -/
noncomputable abbrev excisionUnitPair : RelativeMorphism B S hS V Y W f (h ≫ f) Y :=
  excisionPairOf B S hS f h (h ≫ f)
    (excisionDiagLift B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso)
    (excisionDiagLift_comp B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso)

/-- **The canonical morphism `Y ⟶ X` over `W`.** -/
noncomputable def excisionUnit : Y ⟶ excisionSpace B S hS f h hV hW hY :=
  excisionDesc B S hS f h hV hW hY (h ≫ f)
    (excisionDiagLift B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso)
    (excisionDiagLift_comp B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso)

/-- The canonical morphism to the presheaf of pairs lies over `h ≫ f`. -/
theorem excisionUnit_comp_excisionProj :
    excisionUnit B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso ≫
        excisionProj B S hS f h hV hW hY = h ≫ f :=
  excisionDesc_comp_excisionProj B S hS f h hV hW hY _ _ _

/-- The pair named by a section of the canonical morphism is the restriction of the canonical
pair. -/
theorem excisionBaseEquiv_excisionUnit {A : (BigFppfOver B S hS)ᵒᵖ} (t : Y.obj A) :
    excisionBaseEquiv B S hS f h hV hW hY A
        ((excisionUnit B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso).app A t).1 =
      RelativeMorphism.restrict (yonedaEquiv.symm t)
        (excisionUnitPair B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso) :=
  excisionBaseEquiv_excisionDesc B S hS f h hV hW hY _ _ _ t

/-- The first component of the restriction of the canonical pair at `φ` factors through
`φ ≫ h`. -/
theorem restrict_excisionUnitPair_base {A : (BigFppfOver B S hS)ᵒᵖ}
    (φ : yoneda.obj A.unop ⟶ Y) :
    (RelativeMorphism.restrict φ
        (excisionUnitPair B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso)).base =
      (φ ≫ h) ≫ f := by
  simp only [RelativeMorphism.restrict_base, excisionPairOf_base, Category.assoc]

set_option synthInstance.maxHeartbeats 400000 in
/-- **The evaluation of the restriction of the canonical pair at `φ` is `φ`.** -/
theorem pairEval_restrict_excisionUnitPair {A : (BigFppfOver B S hS)ᵒᵖ}
    (φ : yoneda.obj A.unop ⟶ Y)
    (hq : (RelativeMorphism.restrict φ
      (excisionUnitPair B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso)).base =
        (φ ≫ h) ≫ f) :
    pairEval B S hS f h (φ ≫ h)
        (RelativeMorphism.restrict φ
          (excisionUnitPair B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso)) hq = φ := by
  have hmap : pullback.lift (𝟙 (yoneda.obj A.unop)) (φ ≫ h)
        (by rw [Category.id_comp]; exact hq) ≫
      pullback.map (φ ≫ (h ≫ f)) f (h ≫ f) f φ (𝟙 V) (𝟙 W) (by simp) (by simp) =
        φ ≫ graphSection B S hS f h := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc]
  rw [pairEval]
  simp only [restrict_excisionPairOf_morphism]
  simpa [graphSection_comp_excisionDiagLift] using
    congrArg (fun k => k ≫
      excisionDiagLift B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso) hmap

/-! ### The base change along `f` -/

/-- The morphism `Y ⟶ X ×_{g, W} V` induced by the canonical morphism and `h`. -/
noncomputable def excisionBaseChangeHom :
    Y ⟶ pullback (excisionProj B S hS f h hV hW hY) f :=
  pullback.lift (excisionUnit B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso) h
    (excisionUnit_comp_excisionProj B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso)

/-- The first component of the morphism to the base change is the canonical morphism. -/
@[reassoc (attr := simp)]
theorem excisionBaseChangeHom_fst :
    excisionBaseChangeHom B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso ≫
        pullback.fst (excisionProj B S hS f h hV hW hY) f =
      excisionUnit B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso :=
  pullback.lift_fst _ _ _

/-- The second component of the morphism to the base change is `h`. -/
@[reassoc (attr := simp)]
theorem excisionBaseChangeHom_snd :
    excisionBaseChangeHom B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso ≫
        pullback.snd (excisionProj B S hS f h hV hW hY) f = h :=
  pullback.lift_snd _ _ _

include hV hW hY hf hsep hT hcompl hiso in
/-- **Injectivity on sections of the morphism to the base change.** -/
theorem excisionBaseChangeHom_injective {A : (BigFppfOver B S hS)ᵒᵖ}
    {φ₁ φ₂ : yoneda.obj A.unop ⟶ Y}
    (hh : φ₁ ≫ h = φ₂ ≫ h)
    (hd : φ₁ ≫ excisionUnit B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso =
      φ₂ ≫ excisionUnit B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso) : φ₁ = φ₂ := by
  have hpair : RelativeMorphism.restrict φ₁
      (excisionUnitPair B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso) =
    RelativeMorphism.restrict φ₂
      (excisionUnitPair B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso) := by
    have e₁ := excisionBaseEquiv_excisionUnit B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso
      (yonedaEquiv φ₁)
    have e₂ := excisionBaseEquiv_excisionUnit B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso
      (yonedaEquiv φ₂)
    rw [Equiv.symm_apply_apply] at e₁ e₂
    rw [← e₁, ← e₂]
    refine congrArg _ (congrArg Subtype.val ?_)
    rw [app_eq_yonedaEquiv, app_eq_yonedaEquiv, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply, hd]
  have hq₁ := restrict_excisionUnitPair_base B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso φ₁
  have hq₂ : (RelativeMorphism.restrict φ₂
      (excisionUnitPair B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso)).base =
        (φ₁ ≫ h) ≫ f := by
    rw [hh]
    exact restrict_excisionUnitPair_base B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso φ₂
  calc φ₁ = pairEval B S hS f h (φ₁ ≫ h) _ hq₁ :=
        (pairEval_restrict_excisionUnitPair B S hS f h hV hW hY T W₀ hT hcompl hf hsep
          hiso φ₁ hq₁).symm
    _ = pairEval B S hS f h (φ₁ ≫ h) _ hq₂ :=
        pairEval_congr B S hS f h (φ₁ ≫ h) hq₁ hq₂ hpair
    _ = pairEval B S hS f h (φ₂ ≫ h) _
        (restrict_excisionUnitPair_base B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso φ₂) :=
        pairEval_congr_beta B S hS f h hh _ hq₂ _
    _ = φ₂ := pairEval_restrict_excisionUnitPair B S hS f h hV hW hY T W₀ hT hcompl hf hsep
          hiso φ₂ _

include hV hW hY hf hsep hT hcompl hiso in
/-- **Surjectivity on sections of the morphism to the base change.** Every pair over a section
of `V` is the restriction of the canonical pair at the evaluation of its second component. -/
theorem excisionBaseChangeHom_surjective {A : (BigFppfOver B S hS)ᵒᵖ}
    (ψ : yoneda.obj A.unop ⟶ pullback (excisionProj B S hS f h hV hW hY) f) :
    ∃ φ : yoneda.obj A.unop ⟶ Y,
      φ ≫ excisionBaseChangeHom B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso = ψ := by
  set α := ψ ≫ pullback.fst (excisionProj B S hS f h hV hW hY) f with hα
  set β := ψ ≫ pullback.snd (excisionProj B S hS f h hV hW hY) f with hβ
  set q := excisionBaseEquiv B S hS f h hV hW hY A (yonedaEquiv α).1 with hqdef
  have hm : q.morphism ≫ h = pullback.snd q.base f :=
    (mem_excisionSub_iff B S hS f h hV hW hY _).1 (yonedaEquiv α).2
  have hq : q.base = β ≫ f := by
    refine yonedaEquiv.injective ?_
    rw [← excisionProj_app B S hS f h hV hW hY (yonedaEquiv α), app_eq_yonedaEquiv,
      Equiv.symm_apply_apply, hα, hβ, Category.assoc, Category.assoc, pullback.condition]
  refine ⟨pairEval B S hS f h β q hq, ?_⟩
  have hφh : pairEval B S hS f h β q hq ≫ h = β := pairEval_comp B S hS f h β q hq hm
  have hpair : RelativeMorphism.restrict (pairEval B S hS f h β q hq)
      (excisionUnitPair B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso) = q := by
    have hq₁ : (RelativeMorphism.restrict (pairEval B S hS f h β q hq)
        (excisionUnitPair B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso)).base = β ≫ f := by
      rw [RelativeMorphism.restrict_base, excisionPairOf_base, ← Category.assoc, hφh]
    refine relativeMorphism_ext_of_pairEval B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso
      β (isAlgebraicSpace_yoneda B S hS A.unop) hq₁ hq ?_ hm ?_
    · exact RelativeMorphism.restrict_morphism_comp h _ _
        (excisionDiagLift_comp B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso)
    · rw [← pairEval_congr_beta B S hS f h hφh _ _ hq₁]
      exact pairEval_restrict_excisionUnitPair B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso
        (pairEval B S hS f h β q hq)
        (restrict_excisionUnitPair_base B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso _)
  have hunit : pairEval B S hS f h β q hq ≫
      excisionUnit B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso = α := by
    refine yonedaEquiv.injective ?_
    rw [yonedaEquiv_comp]
    refine Subtype.ext ((excisionBaseEquiv B S hS f h hV hW hY A).injective ?_)
    rw [excisionBaseEquiv_excisionUnit, Equiv.symm_apply_apply]
    exact hpair
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, excisionBaseChangeHom_fst, hunit]
  · rw [Category.assoc, excisionBaseChangeHom_snd, hφh]

include hV hW hY hf hsep hT hcompl hiso in
/-- **The base change of the presheaf of pairs along `f` is `Y`.** -/
theorem isIso_excisionBaseChangeHom :
    IsIso (excisionBaseChangeHom B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso) := by
  have happ : ∀ A : (BigFppfOver B S hS)ᵒᵖ,
      IsIso ((excisionBaseChangeHom B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso).app A) := by
    intro A
    rw [isIso_iff_bijective]
    refine ⟨fun y₁ y₂ hy => ?_, fun x => ?_⟩
    · have hcomp : yonedaEquiv.symm y₁ ≫
          excisionBaseChangeHom B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso =
        yonedaEquiv.symm y₂ ≫
          excisionBaseChangeHom B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso := by
        refine yonedaEquiv.injective ?_
        rw [← app_eq_yonedaEquiv, ← app_eq_yonedaEquiv]
        exact hy
      have hh : yonedaEquiv.symm y₁ ≫ h = yonedaEquiv.symm y₂ ≫ h := by
        rw [← excisionBaseChangeHom_snd B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso]
        simp only [← Category.assoc, hcomp]
      have hd : yonedaEquiv.symm y₁ ≫
            excisionUnit B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso =
          yonedaEquiv.symm y₂ ≫
            excisionUnit B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso := by
        rw [← excisionBaseChangeHom_fst B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso]
        simp only [← Category.assoc, hcomp]
      have := excisionBaseChangeHom_injective B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso
        hh hd
      rw [← Equiv.apply_symm_apply yonedaEquiv y₁, ← Equiv.apply_symm_apply yonedaEquiv y₂,
        this]
    · obtain ⟨φ, hφ⟩ := excisionBaseChangeHom_surjective B S hS f h hV hW hY T W₀ hT hcompl hf
        hsep hiso (yonedaEquiv.symm x)
      refine ⟨yonedaEquiv φ, ?_⟩
      rw [app_eq_yonedaEquiv, Equiv.symm_apply_apply, hφ, Equiv.apply_symm_apply]
  exact NatIso.isIso_of_isIso_app _

/-- **The base change of the presheaf of pairs along `f`, read in the slice category over
`V`.** -/
noncomputable def excisionBaseChangeIso :
    (Over.pullback f).obj (Over.mk (excisionProj B S hS f h hV hW hY)) ≅ Over.mk h :=
  haveI := isIso_excisionBaseChangeHom B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso
  (Over.isoMk (asIso (excisionBaseChangeHom B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso))
    (excisionBaseChangeHom_snd B S hS f h hV hW hY T W₀ hT hcompl hf hsep hiso)).symm

end AlgebraicGeometry.Space

end
