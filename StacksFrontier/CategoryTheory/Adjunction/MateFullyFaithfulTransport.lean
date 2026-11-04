module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Yoneda
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare

/-!
# Transporting left adjoints and base change maps along fully faithful functors

Consider two adjunctions `L₀ ⊣ R₀` (with `L₀ : C₀ ⥤ D₀`) and `L₁ ⊣ R₁` (with `L₁ : C₁ ⥤ D₁`)
and functors `U_C : C₀ ⥤ C₁`, `U_D : D₀ ⥤ D₁`, for instance the universe lifts of the
coefficients of categories of sheaves. A comparison `ρ : R₀ ⋙ U_C ⟶ U_D ⋙ R₁` of the right
adjoints has a mate `λ : U_C ⋙ L₁ ⟶ L₀ ⋙ U_D` (`CategoryTheory.mateEquiv`). This file proves the
three facts about such mates that are needed to compare base change maps at two coefficient
universes:

* if `U_C`, `U_D` are fully faithful, `ρ` is invertible and `L₁ (U_C M)` lies in the essential
  image of `U_D`, then `λ` is invertible at `M`;
* the mates of the comparisons of the right adjoints of a composite are compatible with any
  identification of the composite left adjoint with the composite of left adjoints which is
  characterized by its unit (such as `CategoryTheory.Adjunction.leftAdjointUniq`);
* the base change maps `Stacks.CategoryTheory.BaseChange.map` of two squares of adjunctions are
  intertwined by the mates, as soon as the mates are compatible with the identifications of the
  composites around the squares.

Everything is stated with all functors as variables, so that an application to concrete
categories of sheaves is a single instantiation.

## Main results

* `Stacks.CategoryTheory.MateTransport.isIso_mateEquiv_symm_app`
* `Stacks.CategoryTheory.MateTransport.mateEquiv_symm_comp`
* `Stacks.CategoryTheory.MateTransport.map_mateEquiv_symm`
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.MateTransport

section Single

variable {C₀ C₁ D₀ D₁ : Type*} [Category* C₀] [Category* C₁] [Category* D₀] [Category* D₁]
  {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
  (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁) {UC : C₀ ⥤ C₁} {UD : D₀ ⥤ D₁}
  (ρ : NatTrans (R₀ ⋙ UC) (UD ⋙ R₁))

/-- The transpose under `L₁ ⊣ R₁` of the mate `λ` of `ρ` followed by `U_D` of a morphism is
`U_C` of the transpose under `L₀ ⊣ R₀` followed by `ρ`. -/
theorem homEquiv_mateEquiv_symm_app_comp (M : C₀) {N : D₀} (y : L₀.obj M ⟶ N) :
    adj₁.homEquiv _ _ (((mateEquiv adj₀ adj₁).symm ρ).app M ≫ UD.map y) =
      UC.map (adj₀.homEquiv _ _ y) ≫ ρ.app N := by
  have hu : UC.map (adj₀.unit.app M) ≫ ρ.app (L₀.obj M) =
      adj₁.unit.app (UC.obj M) ≫ R₁.map (((mateEquiv adj₀ adj₁).symm ρ).app M) :=
    unit_mateEquiv_symm adj₀ adj₁ ρ M
  have hn : UC.map (R₀.map y) ≫ ρ.app N = ρ.app (L₀.obj M) ≫ R₁.map (UD.map y) :=
    ρ.naturality y
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
    ← reassoc_of% hu, Category.assoc, hn]

/-- Postcomposing the mate `λ` of `ρ` at `M` with `U_D` of morphisms out of `L₀ M` is bijective
when `U_C` is fully faithful and `ρ` is invertible at the target. -/
theorem bijective_mateEquiv_symm_app_comp (hC : UC.FullyFaithful) (M : C₀) (N : D₀)
    [IsIso (ρ.app N)] :
    Function.Bijective (fun y : L₀.obj M ⟶ N => ((mateEquiv adj₀ adj₁).symm ρ).app M ≫
      UD.map y) := by
  have h : (fun y : L₀.obj M ⟶ N => ((mateEquiv adj₀ adj₁).symm ρ).app M ≫ UD.map y) =
      (adj₁.homEquiv _ _).symm ∘ (fun z => z ≫ ρ.app N) ∘ UC.map ∘ adj₀.homEquiv _ _ := by
    funext y
    simp only [Function.comp_apply]
    rw [← homEquiv_mateEquiv_symm_app_comp, Equiv.symm_apply_apply]
  rw [h]
  refine (Equiv.bijective _).comp ((?_ : Function.Bijective (fun z => z ≫ ρ.app N)).comp
    ((hC.map_bijective _ _).comp (Equiv.bijective _)))
  exact (asIso (ρ.app N)).homToEquiv.bijective

/-- **The mate of an invertible comparison of right adjoints along fully faithful functors is
invertible** at every object `M` for which `L₁ (U_C M)` lies in the essential image of `U_D`. -/
theorem isIso_mateEquiv_symm_app (hC : UC.FullyFaithful) (hD : UD.FullyFaithful)
    [∀ N, IsIso (ρ.app N)] (M : C₀) {A : D₀} (e : L₁.obj (UC.obj M) ≅ UD.obj A) :
    IsIso (((mateEquiv adj₀ adj₁).symm ρ).app M) := by
  set l := ((mateEquiv adj₀ adj₁).symm ρ).app M
  obtain ⟨ψ, hψ⟩ : ∃ ψ : A ⟶ L₀.obj M, UD.map ψ = e.inv ≫ l := ⟨_, hD.map_preimage _⟩
  have : IsIso ψ := by
    refine isIso_of_coyoneda_map_bijective ψ fun N => ?_
    have h : (fun y : L₀.obj M ⟶ N => ψ ≫ y) =
        hD.preimage ∘ (fun z => e.inv ≫ z) ∘ (fun y : L₀.obj M ⟶ N => l ≫ UD.map y) := by
      funext y
      apply hD.map_injective
      simp only [Function.comp_apply, Functor.FullyFaithful.map_preimage, Functor.map_comp, hψ,
        Category.assoc]
    rw [h]
    refine hD.homEquiv.symm.bijective.comp
      ((?_ : Function.Bijective (fun z : L₁.obj (UC.obj M) ⟶ UD.obj N => e.inv ≫ z)).comp
        (bijective_mateEquiv_symm_app_comp adj₀ adj₁ ρ hC M N))
    exact e.homFromEquiv.bijective
  rw [show l = e.hom ≫ UD.map ψ by rw [hψ, Iso.hom_inv_id_assoc]]
  infer_instance

end Single

section Composite

variable {SP₀ SP₁ SQ₀ SQ₁ SR₀ SR₁ : Type*} [Category* SP₀] [Category* SP₁] [Category* SQ₀]
  [Category* SQ₁] [Category* SR₀] [Category* SR₁]
  {La₀ : SQ₀ ⥤ SP₀} {Ra₀ : SP₀ ⥤ SQ₀} {Lb₀ : SR₀ ⥤ SQ₀} {Rb₀ : SQ₀ ⥤ SR₀}
  {Lab₀ : SR₀ ⥤ SP₀} {Rab₀ : SP₀ ⥤ SR₀}
  {La₁ : SQ₁ ⥤ SP₁} {Ra₁ : SP₁ ⥤ SQ₁} {Lb₁ : SR₁ ⥤ SQ₁} {Rb₁ : SQ₁ ⥤ SR₁}
  {Lab₁ : SR₁ ⥤ SP₁} {Rab₁ : SP₁ ⥤ SR₁}
  (adja₀ : La₀ ⊣ Ra₀) (adjb₀ : Lb₀ ⊣ Rb₀) (adjab₀ : Lab₀ ⊣ Rab₀)
  (adja₁ : La₁ ⊣ Ra₁) (adjb₁ : Lb₁ ⊣ Rb₁) (adjab₁ : Lab₁ ⊣ Rab₁)
  {UP : SP₀ ⥤ SP₁} {UQ : SQ₀ ⥤ SQ₁} {UR : SR₀ ⥤ SR₁}
  (ρa : NatTrans (Ra₀ ⋙ UQ) (UP ⋙ Ra₁)) (ρb : NatTrans (Rb₀ ⋙ UR) (UQ ⋙ Rb₁))
  (ρab : NatTrans (Rab₀ ⋙ UR) (UP ⋙ Rab₁))
  (π₀ : Ra₀ ⋙ Rb₀ ≅ Rab₀) (π₁ : Ra₁ ⋙ Rb₁ ≅ Rab₁)
  (c₀ : Lab₀ ≅ Lb₀ ⋙ La₀) (c₁ : Lab₁ ≅ Lb₁ ⋙ La₁)

/-- **The mates of the comparisons of right adjoints are compatible with composition.** Let
`c_i : L_{ab} ≅ L_b ⋙ L_a` be identifications of a composite left adjoint, each characterized
by its unit (`hc₀`, `hc₁`: the unit of `L_{ab} ⊣ R_{ab}` followed by `R_{ab} c` is the unit of
the composite adjunction read through `π_i : R_a ⋙ R_b ≅ R_{ab}`), and suppose the comparisons
`ρ` of the right adjoints are compatible with the `π_i` (`hρ`). Then the mates of the `ρ` are
compatible with the `c_i`. -/
theorem mateEquiv_symm_comp
    (hc₀ : ∀ M : SR₀, adjab₀.unit.app M ≫ Rab₀.map (c₀.hom.app M) =
      adjb₀.unit.app M ≫ Rb₀.map (adja₀.unit.app (Lb₀.obj M)) ≫ π₀.hom.app _)
    (hc₁ : ∀ M : SR₁, adjab₁.unit.app M ≫ Rab₁.map (c₁.hom.app M) =
      adjb₁.unit.app M ≫ Rb₁.map (adja₁.unit.app (Lb₁.obj M)) ≫ π₁.hom.app _)
    (hρ : ∀ N : SP₀, ρb.app (Ra₀.obj N) ≫ Rb₁.map (ρa.app N) ≫ π₁.hom.app (UP.obj N) =
      UR.map (π₀.hom.app N) ≫ ρab.app N)
    (M : SR₀) :
    c₁.hom.app (UR.obj M) ≫ La₁.map (((mateEquiv adjb₀ adjb₁).symm ρb).app M) ≫
        ((mateEquiv adja₀ adja₁).symm ρa).app (Lb₀.obj M) =
      ((mateEquiv adjab₀ adjab₁).symm ρab).app M ≫ UP.map (c₀.hom.app M) := by
  set la := (mateEquiv adja₀ adja₁).symm ρa
  set lb := (mateEquiv adjb₀ adjb₁).symm ρb
  set N := La₀.obj (Lb₀.obj M)
  -- the common value of the two transposes under `L_{ab} ⊣ R_{ab}` at level `1`
  set T := UR.map (adjb₀.unit.app M) ≫ UR.map (Rb₀.map (adja₀.unit.app (Lb₀.obj M))) ≫
    ρb.app (Ra₀.obj N) ≫ Rb₁.map (ρa.app N) ≫ π₁.hom.app (UP.obj N)
  have hR : adjab₁.homEquiv _ _ (((mateEquiv adjab₀ adjab₁).symm ρab).app M ≫
      UP.map (c₀.hom.app M)) = T := by
    refine (homEquiv_mateEquiv_symm_app_comp adjab₀ adjab₁ ρab M (c₀.hom.app M)).trans ?_
    rw [Adjunction.homEquiv_unit, hc₀]
    simp only [Functor.map_comp, Category.assoc, T]
    exact congrArg (fun t => UR.map (adjb₀.unit.app M) ≫
      UR.map (Rb₀.map (adja₀.unit.app (Lb₀.obj M))) ≫ t) (hρ N).symm
  have hua : adja₁.unit.app (Lb₁.obj (UR.obj M)) ≫ Ra₁.map (La₁.map (lb.app M)) =
      lb.app M ≫ adja₁.unit.app (UQ.obj (Lb₀.obj M)) :=
    (adja₁.unit.naturality (lb.app M)).symm
  have hma : UQ.map (adja₀.unit.app (Lb₀.obj M)) ≫ ρa.app N =
      adja₁.unit.app (UQ.obj (Lb₀.obj M)) ≫ Ra₁.map (la.app (Lb₀.obj M)) :=
    unit_mateEquiv_symm adja₀ adja₁ ρa (Lb₀.obj M)
  have hmb : UR.map (adjb₀.unit.app M) ≫ ρb.app (Lb₀.obj M) =
      adjb₁.unit.app (UR.obj M) ≫ Rb₁.map (lb.app M) :=
    unit_mateEquiv_symm adjb₀ adjb₁ ρb M
  have hnb : UR.map (Rb₀.map (adja₀.unit.app (Lb₀.obj M))) ≫ ρb.app (Ra₀.obj N) =
      ρb.app (Lb₀.obj M) ≫ Rb₁.map (UQ.map (adja₀.unit.app (Lb₀.obj M))) :=
    ρb.naturality (adja₀.unit.app (Lb₀.obj M))
  have hπ : Rb₁.map (Ra₁.map (La₁.map (lb.app M) ≫ la.app (Lb₀.obj M))) ≫
      π₁.hom.app (UP.obj N) =
      π₁.hom.app (La₁.obj (Lb₁.obj (UR.obj M))) ≫
        Rab₁.map (La₁.map (lb.app M) ≫ la.app (Lb₀.obj M)) :=
    π₁.hom.naturality (La₁.map (lb.app M) ≫ la.app (Lb₀.obj M))
  have e₁ : Rb₁.map (adja₁.unit.app (Lb₁.obj (UR.obj M))) ≫
      Rb₁.map (Ra₁.map (La₁.map (lb.app M))) =
      Rb₁.map (lb.app M) ≫ Rb₁.map (adja₁.unit.app (UQ.obj (Lb₀.obj M))) := by
    rw [← Rb₁.map_comp, ← Rb₁.map_comp, hua]
  have e₂ : Rb₁.map (UQ.map (adja₀.unit.app (Lb₀.obj M))) ≫ Rb₁.map (ρa.app N) =
      Rb₁.map (adja₁.unit.app (UQ.obj (Lb₀.obj M))) ≫ Rb₁.map (Ra₁.map (la.app (Lb₀.obj M))) := by
    rw [← Rb₁.map_comp, ← Rb₁.map_comp, hma]
  have hL : adjab₁.homEquiv _ _ (c₁.hom.app (UR.obj M) ≫ La₁.map (lb.app M) ≫
      la.app (Lb₀.obj M)) = T := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp, reassoc_of% (hc₁ (UR.obj M)), ← hπ]
    simp only [T]
    rw [reassoc_of% hnb, reassoc_of% hmb]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% e₁, reassoc_of% e₂]
  exact (adjab₁.homEquiv _ _).injective (hL.trans hR.symm)

end Composite

/-- The base change map followed by the counit of `Lf' ⊣ Rf'` is the comparison of the two
composites around the square followed by `Lg'` of the counit of `Lf ⊣ Rf`. -/
theorem map_comp_counit {A B A' B' : Type*} [Category* A] [Category* B] [Category* A']
    [Category* B'] {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
    {Lg : A ⥤ A'} {Lg' : B ⥤ B'} {Lc : A ⥤ B'} (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) (K : B) :
    Lf'.map (BaseChange.map adjf adjf' eg ef K) ≫ adjf'.counit.app (Lg'.obj K) =
      eg.hom.app (Rf.obj K) ≫ ef.inv.app (Rf.obj K) ≫ Lg'.map (adjf.counit.app K) := by
  simpa only [Adjunction.homEquiv_counit] using BaseChange.homEquiv_symm_map adjf adjf' eg ef K

section Square

universe w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈

variable {A₀ : Type z₁} {A₁ : Type z₂} {B₀ : Type z₃} {B₁ : Type z₄} {A'₀ : Type z₅}
  {A'₁ : Type z₆} {B'₀ : Type z₇} {B'₁ : Type z₈} [Category.{w₁} A₀] [Category.{w₂} A₁]
  [Category.{w₃} B₀] [Category.{w₄} B₁] [Category.{w₅} A'₀] [Category.{w₆} A'₁]
  [Category.{w₇} B'₀] [Category.{w₈} B'₁]
  {Lf₀ : A₀ ⥤ B₀} {Rf₀ : B₀ ⥤ A₀} {Lf'₀ : A'₀ ⥤ B'₀} {Rf'₀ : B'₀ ⥤ A'₀}
  {Lg₀ : A₀ ⥤ A'₀} {Lg'₀ : B₀ ⥤ B'₀} {Lc₀ : A₀ ⥤ B'₀}
  {Lf₁ : A₁ ⥤ B₁} {Rf₁ : B₁ ⥤ A₁} {Lf'₁ : A'₁ ⥤ B'₁} {Rf'₁ : B'₁ ⥤ A'₁}
  {Lg₁ : A₁ ⥤ A'₁} {Lg'₁ : B₁ ⥤ B'₁} {Lc₁ : A₁ ⥤ B'₁}
  (adjf₀ : Lf₀ ⊣ Rf₀) (adjf'₀ : Lf'₀ ⊣ Rf'₀) (eg₀ : Lg₀ ⋙ Lf'₀ ≅ Lc₀) (ef₀ : Lf₀ ⋙ Lg'₀ ≅ Lc₀)
  (adjf₁ : Lf₁ ⊣ Rf₁) (adjf'₁ : Lf'₁ ⊣ Rf'₁) (eg₁ : Lg₁ ⋙ Lf'₁ ≅ Lc₁) (ef₁ : Lf₁ ⋙ Lg'₁ ≅ Lc₁)
  {UA : A₀ ⥤ A₁} {UB : B₀ ⥤ B₁} {UA' : A'₀ ⥤ A'₁} {UB' : B'₀ ⥤ B'₁}
  (ρf : NatTrans (Rf₀ ⋙ UA) (UB ⋙ Rf₁)) (ρf' : NatTrans (Rf'₀ ⋙ UA') (UB' ⋙ Rf'₁))
  (lg : NatTrans (UA ⋙ Lg₁) (Lg₀ ⋙ UA')) (lg' : NatTrans (UB ⋙ Lg'₁) (Lg'₀ ⋙ UB'))
  (lc : NatTrans (UA ⋙ Lc₁) (Lc₀ ⋙ UB'))

/-- **The base change maps of two squares of adjunctions are intertwined by the mates.** Given
comparisons `ρ_f`, `ρ_f'` of the right adjoints along functors `U`, with mates `λ_f`, `λ_f'`,
and comparisons `λ_g`, `λ_g'`, `λ_c` of the other left adjoints compatible with the
identifications `eg_i`, `ef_i` of the composites around the squares (`hg`, `hf`), the base change
map `Lg (Rf K) ⟶ Rf' (Lg' K)` at level `1` evaluated at `U_B K` is the base change map at
level `0` evaluated at `K`, read through these comparisons. -/
theorem map_mateEquiv_symm
    (hg : ∀ M : A₀, eg₁.hom.app (UA.obj M) ≫ lc.app M =
      Lf'₁.map (lg.app M) ≫ ((mateEquiv adjf'₀ adjf'₁).symm ρf').app (Lg₀.obj M) ≫
        UB'.map (eg₀.hom.app M))
    (hf : ∀ M : A₀, ef₁.hom.app (UA.obj M) ≫ lc.app M =
      Lg'₁.map (((mateEquiv adjf₀ adjf₁).symm ρf).app M) ≫ lg'.app (Lf₀.obj M) ≫
        UB'.map (ef₀.hom.app M))
    (K : B₀) :
    Lg₁.map (ρf.app K) ≫ BaseChange.map adjf₁ adjf'₁ eg₁ ef₁ (UB.obj K) ≫ Rf'₁.map (lg'.app K) =
      lg.app (Rf₀.obj K) ≫ UA'.map (BaseChange.map adjf₀ adjf'₀ eg₀ ef₀ K) ≫
        ρf'.app (Lg'₀.obj K) := by
  set lf := (mateEquiv adjf₀ adjf₁).symm ρf
  set lf' := (mateEquiv adjf'₀ adjf'₁).symm ρf'
  set M := Rf₀.obj K
  -- the common value of the two transposes under `Lf' ⊣ Rf'` at level `1`
  set E := Lf'₁.map (lg.app M) ≫ lf'.app (Lg₀.obj M) ≫ UB'.map (eg₀.hom.app M) ≫
    UB'.map (ef₀.inv.app M) ≫ UB'.map (Lg'₀.map (adjf₀.counit.app K))
  have hεf : Lf₁.map (ρf.app K) ≫ adjf₁.counit.app (UB.obj K) =
      lf.app M ≫ UB.map (adjf₀.counit.app K) :=
    mateEquiv_counit_symm adjf₀ adjf₁ ρf K
  have hεf' : Lf'₁.map (ρf'.app (Lg'₀.obj K)) ≫ adjf'₁.counit.app (UB'.obj (Lg'₀.obj K)) =
      lf'.app (Rf'₀.obj (Lg'₀.obj K)) ≫ UB'.map (adjf'₀.counit.app (Lg'₀.obj K)) :=
    mateEquiv_counit_symm adjf'₀ adjf'₁ ρf' (Lg'₀.obj K)
  have hf' : ef₁.inv.app (UA.obj M) ≫ Lg'₁.map (lf.app M) ≫ lg'.app (Lf₀.obj M) =
      lc.app M ≫ UB'.map (ef₀.inv.app M) := by
    rw [← cancel_epi (ef₁.hom.app (UA.obj M)), Iso.hom_inv_id_app_assoc, reassoc_of% (hf M)]
    simp [← UB'.map_comp]
  -- naturality of the identifications around the square along `ρ_f`
  have hng : Lf'₁.map (Lg₁.map (ρf.app K)) ≫ eg₁.hom.app (Rf₁.obj (UB.obj K)) =
      eg₁.hom.app (UA.obj M) ≫ Lc₁.map (ρf.app K) :=
    eg₁.hom.naturality (ρf.app K)
  have hnf : Lc₁.map (ρf.app K) ≫ ef₁.inv.app (Rf₁.obj (UB.obj K)) =
      ef₁.inv.app (UA.obj M) ≫ Lg'₁.map (Lf₁.map (ρf.app K)) :=
    ef₁.inv.naturality (ρf.app K)
  have hng' : Lg'₁.map (UB.map (adjf₀.counit.app K)) ≫ lg'.app K =
      lg'.app (Lf₀.obj M) ≫ UB'.map (Lg'₀.map (adjf₀.counit.app K)) :=
    lg'.naturality (adjf₀.counit.app K)
  have hnf' : Lf'₁.map (UA'.map (BaseChange.map adjf₀ adjf'₀ eg₀ ef₀ K)) ≫
      lf'.app (Rf'₀.obj (Lg'₀.obj K)) =
      lf'.app (Lg₀.obj M) ≫ UB'.map (Lf'₀.map (BaseChange.map adjf₀ adjf'₀ eg₀ ef₀ K)) :=
    lf'.naturality (BaseChange.map adjf₀ adjf'₀ eg₀ ef₀ K)
  have hcn := adjf'₁.counit.naturality (lg'.app K)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at hcn
  have hL : (adjf'₁.homEquiv _ _).symm (Lg₁.map (ρf.app K) ≫
      BaseChange.map adjf₁ adjf'₁ eg₁ ef₁ (UB.obj K) ≫ Rf'₁.map (lg'.app K)) = E := by
    rw [Adjunction.homEquiv_counit]
    simp only [Functor.map_comp, Category.assoc, Functor.comp_obj]
    rw [hcn, reassoc_of% (map_comp_counit adjf₁ adjf'₁ eg₁ ef₁ (UB.obj K)), reassoc_of% hng,
      reassoc_of% hnf, ← Lg'₁.map_comp_assoc, hεf, Lg'₁.map_comp_assoc, hng', reassoc_of% hf',
      reassoc_of% (hg M)]
  have hR : (adjf'₁.homEquiv _ _).symm (lg.app M ≫
      UA'.map (BaseChange.map adjf₀ adjf'₀ eg₀ ef₀ K) ≫ ρf'.app (Lg'₀.obj K)) = E := by
    rw [Adjunction.homEquiv_counit]
    simp only [Functor.map_comp, Category.assoc, Functor.comp_obj]
    rw [hεf', reassoc_of% hnf', ← UB'.map_comp, map_comp_counit adjf₀ adjf'₀ eg₀ ef₀ K]
    simp only [E, M, Functor.map_comp]
  exact (adjf'₁.homEquiv _ _).symm.injective (hL.trans hR.symm)

/-- `Stacks.CategoryTheory.MateTransport.map_mateEquiv_symm` when the identification of the second
composite is a composite `cf ≪≫ e` of isomorphisms, with the compatibility hypothesis split
accordingly (`hf'` for `cf` and an auxiliary comparison `lc'`, `he` for `e`). -/
theorem map_mateEquiv_symm_of_trans {Lc'₀ : A₀ ⥤ B'₀} {Lc'₁ : A₁ ⥤ B'₁}
    (cf₀ : Lf₀ ⋙ Lg'₀ ≅ Lc'₀) (e₀ : Lc'₀ ≅ Lc₀) (cf₁ : Lf₁ ⋙ Lg'₁ ≅ Lc'₁) (e₁ : Lc'₁ ≅ Lc₁)
    (lc' : NatTrans (UA ⋙ Lc'₁) (Lc'₀ ⋙ UB'))
    (hg : ∀ M : A₀, eg₁.hom.app (UA.obj M) ≫ lc.app M =
      Lf'₁.map (lg.app M) ≫ ((mateEquiv adjf'₀ adjf'₁).symm ρf').app (Lg₀.obj M) ≫
        UB'.map (eg₀.hom.app M))
    (hf' : ∀ M : A₀, cf₁.hom.app (UA.obj M) ≫ lc'.app M =
      Lg'₁.map (((mateEquiv adjf₀ adjf₁).symm ρf).app M) ≫ lg'.app (Lf₀.obj M) ≫
        UB'.map (cf₀.hom.app M))
    (he : ∀ M : A₀, e₁.hom.app (UA.obj M) ≫ lc.app M = lc'.app M ≫ UB'.map (e₀.hom.app M))
    (K : B₀) :
    Lg₁.map (ρf.app K) ≫ BaseChange.map adjf₁ adjf'₁ eg₁ (cf₁ ≪≫ e₁) (UB.obj K) ≫
        Rf'₁.map (lg'.app K) =
      lg.app (Rf₀.obj K) ≫ UA'.map (BaseChange.map adjf₀ adjf'₀ eg₀ (cf₀ ≪≫ e₀) K) ≫
        ρf'.app (Lg'₀.obj K) :=
  map_mateEquiv_symm adjf₀ adjf'₀ eg₀ (cf₀ ≪≫ e₀) adjf₁ adjf'₁ eg₁ (cf₁ ≪≫ e₁) ρf ρf' lg lg' lc
    hg (fun M => by
      simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc, he, reassoc_of% (hf' M),
        Functor.map_comp])
    K

/-- `Stacks.CategoryTheory.MateTransport.map_mateEquiv_symm_of_trans` when the second
identification is `cf ≪≫ eqToIso (congrArg Lk hk)` for a family of composite left adjoints
`Lk` indexed by `k` with an equality `hk : k₁ = k₂`, and the comparisons of the `Lk k` form a
family `lk`: the compatibility along the equality is then automatic. -/
theorem map_mateEquiv_symm_of_eqToIso {I : Type*} {k₁ k₂ : I} (hk : k₁ = k₂)
    (Lk₀ : I → (A₀ ⥤ B'₀)) (Lk₁ : I → (A₁ ⥤ B'₁))
    (lk : ∀ k, NatTrans (UA ⋙ Lk₁ k) (Lk₀ k ⋙ UB'))
    (eg₀' : Lg₀ ⋙ Lf'₀ ≅ Lk₀ k₂) (eg₁' : Lg₁ ⋙ Lf'₁ ≅ Lk₁ k₂)
    (cf₀ : Lf₀ ⋙ Lg'₀ ≅ Lk₀ k₁) (cf₁ : Lf₁ ⋙ Lg'₁ ≅ Lk₁ k₁)
    (hg : ∀ M : A₀, eg₁'.hom.app (UA.obj M) ≫ (lk k₂).app M =
      Lf'₁.map (lg.app M) ≫ ((mateEquiv adjf'₀ adjf'₁).symm ρf').app (Lg₀.obj M) ≫
        UB'.map (eg₀'.hom.app M))
    (hf' : ∀ M : A₀, cf₁.hom.app (UA.obj M) ≫ (lk k₁).app M =
      Lg'₁.map (((mateEquiv adjf₀ adjf₁).symm ρf).app M) ≫ lg'.app (Lf₀.obj M) ≫
        UB'.map (cf₀.hom.app M))
    (K : B₀) :
    Lg₁.map (ρf.app K) ≫
        BaseChange.map adjf₁ adjf'₁ eg₁' (cf₁ ≪≫ eqToIso (congrArg Lk₁ hk)) (UB.obj K) ≫
          Rf'₁.map (lg'.app K) =
      lg.app (Rf₀.obj K) ≫
        UA'.map (BaseChange.map adjf₀ adjf'₀ eg₀' (cf₀ ≪≫ eqToIso (congrArg Lk₀ hk)) K) ≫
          ρf'.app (Lg'₀.obj K) := by
  subst hk
  exact map_mateEquiv_symm_of_trans adjf₀ adjf'₀ eg₀' adjf₁ adjf'₁ eg₁' ρf ρf' lg lg' (lk k₁)
    cf₀ (eqToIso rfl) cf₁ (eqToIso rfl) (lk k₁) hg hf' (fun M => by simp) K

end Square

end Stacks.CategoryTheory.MateTransport

end
