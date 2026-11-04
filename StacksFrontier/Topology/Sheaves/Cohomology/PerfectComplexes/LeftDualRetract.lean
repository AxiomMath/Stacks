module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RestrictDerivedMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.UnitComplexMaps
public import StacksFrontier.Homology.DerivedCategory.Monoidal.DerivedTensorIsoNaturality
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StrictlyPerfectLocalRep

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open TopologicalSpace Opposite Stacks.SheafOfModules.DerivedMonoidal
open Stacks.Cohomology.MonoidalDerived

universe w₁ w₂ v₁ v₂ u₁ u₂ u d d'

/-- Let `R : A ⥤ B` be an exact functor of abelian categories and `α : Q(E) ⟶ Q(F)` the left
fraction `Q(γ) ≫ Q(f)⁻¹` of `γ : E ⟶ G` and a quasi-isomorphism `f : F ⟶ G`. If a morphism of
complexes `β : R(E) ⟶ R(F)` satisfies `Q(β ≫ R(f)) = Q(R(γ))`, then `R(α)` corresponds to `Q(β)`
under the comparison isomorphisms `R(Q(-)) ≅ Q(R(-))`. -/
theorem _root_.CategoryTheory.Functor.mapDerivedCategory_map_eq_of_Q_eq {A : Type u₁}
    [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A] {B : Type u₂} [Category.{v₂} B]
    [Abelian B] [HasDerivedCategory.{w₂} B] (R : A ⥤ B) [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] {E F G : CochainComplex A ℤ}
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) (γ : E ⟶ G) (f : F ⟶ G)
    (hf : IsIso (DerivedCategory.Q.map f))
    (hαfac : α = DerivedCategory.Q.map γ ≫ CategoryTheory.inv (DerivedCategory.Q.map f))
    (β : (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⟶
      (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
    (hβ : DerivedCategory.Q.map (β ≫ (R.mapHomologicalComplex (ComplexShape.up ℤ)).map f) =
      DerivedCategory.Q.map ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map γ)) :
    R.mapDerivedCategory.map α ≫ R.mapDerivedCategoryFactors.hom.app F =
      R.mapDerivedCategoryFactors.hom.app E ≫ DerivedCategory.Q.map β := by
  have hfq : QuasiIso f := (DerivedCategory.isIso_Q_map_iff_quasiIso (C := A) f).mp hf
  have hiso : IsIso (DerivedCategory.Q.map
      ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := B) _).2 inferInstance
  have hisoD : IsIso (R.mapDerivedCategory.map (DerivedCategory.Q.map f)) := by
    have := hf
    infer_instance
  have hnatf := R.mapDerivedCategoryFactors_hom_naturality f
  have hnatγ := R.mapDerivedCategoryFactors_hom_naturality γ
  have hinv : CategoryTheory.inv (R.mapDerivedCategory.map (DerivedCategory.Q.map f)) ≫
      R.mapDerivedCategoryFactors.hom.app F =
        R.mapDerivedCategoryFactors.hom.app G ≫
          CategoryTheory.inv (DerivedCategory.Q.map
            ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, hnatf, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  calc R.mapDerivedCategory.map α ≫ R.mapDerivedCategoryFactors.hom.app F
      = R.mapDerivedCategory.map (DerivedCategory.Q.map γ) ≫
          CategoryTheory.inv (R.mapDerivedCategory.map (DerivedCategory.Q.map f)) ≫
            R.mapDerivedCategoryFactors.hom.app F := by
        rw [hαfac, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_inv,
          Category.assoc]
    _ = R.mapDerivedCategory.map (DerivedCategory.Q.map γ) ≫
          R.mapDerivedCategoryFactors.hom.app G ≫
            CategoryTheory.inv (DerivedCategory.Q.map
              ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) := by rw [hinv]
    _ = (R.mapDerivedCategoryFactors.hom.app E ≫
          DerivedCategory.Q.map ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map γ)) ≫
            CategoryTheory.inv (DerivedCategory.Q.map
              ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) := by
        rw [← Category.assoc, hnatγ]
    _ = R.mapDerivedCategoryFactors.hom.app E ≫ DerivedCategory.Q.map β := by
        rw [Category.assoc, ← hβ, CategoryTheory.Functor.map_comp, Category.assoc,
          IsIso.hom_inv_id,
          Category.comp_id]


namespace CategoryTheory

open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- **The direct-summand step of Stacks 0FPD, in a monoidal functor.** Let `M ⊣ N` be an exact
pairing of `C` and `F : C ⥤ D` a monoidal functor. Suppose the coevaluation, read through
isomorphisms `𝟙 ≅ U₀`, `M' ≅ M`, `N' ≅ N` and `M' ⊗ N' ≅ T`, becomes after `F` a morphism that
factors through `s' : S' ⟶ T'`, where `s'` is the image under `F` (up to the isomorphisms
`φ_S`, `φ_T`) of `s : S ⟶ T` and `S ≅ K' ⊗ N'` carries `s` to `j' ▷ N'`. Then `F M` is a
retract of `F K'`. -/
theorem nonempty_retract_map_of_factorization {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    (M N : C) [ExactPairing M N] {U₀ M' N' T K' S : C} (u : 𝟙_ C ≅ U₀) (eM : M' ≅ M)
    (eN : N' ≅ N) (comp : M' ⊗ N' ≅ T) (j' : K' ⟶ M') (s : S ⟶ T) (Θ : S ≅ K' ⊗ N')
    (hΘ : Θ.hom ≫ (j' ▷ N') = s ≫ comp.inv)
    {U₁ S' T' : D} (φU : F.obj U₀ ≅ U₁) (φS : F.obj S ≅ S') (φT : F.obj T ≅ T') (s' : S' ⟶ T')
    (hs : F.map s ≫ φT.hom = φS.hom ≫ s') (b : U₁ ⟶ S')
    (hβ : F.map (u.inv ≫ (η_ M N ≫ (eM.inv ⊗ₘ eN.inv)) ≫ comp.hom) ≫ φT.hom = φU.hom ≫ b ≫ s') :
    Nonempty (@Retract D _ (F.obj M) (F.obj K')) := by
  let := ExactPairing.map F M N
  obtain ⟨c, hc⟩ : ∃ c, c = u.inv ≫ (η_ M N ≫ (eM.inv ⊗ₘ eN.inv)) ≫ comp.hom := ⟨_, rfl⟩
  rw [← hc] at hβ
  have hη : η_ M N = u.hom ≫ c ≫ comp.inv ≫ (eM.hom ⊗ₘ eN.hom) := by
    simp [hc]
  have hs' : φS.inv ≫ F.map s = s' ≫ φT.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hs, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hF : F.map c = φU.hom ≫ b ≫ φS.inv ≫ F.map s := by
    rw [(Iso.eq_comp_inv _).mpr hβ, Category.assoc, Category.assoc, ← hs']
  have E2 : s ≫ comp.inv ≫ (eM.hom ⊗ₘ eN.hom) =
      Θ.hom ≫ (K' ◁ eN.hom) ≫ ((j' ≫ eM.hom) ▷ N) := by
    rw [whisker_exchange, MonoidalCategory.tensorHom_def, ← Category.assoc s, ← hΘ]
    simp only [Category.assoc, comp_whiskerRight]
  have E4 : F.map s ≫ F.map comp.inv ≫ F.map (eM.hom ⊗ₘ eN.hom) =
      F.map Θ.hom ≫ F.map (K' ◁ eN.hom) ≫ F.map (j' ▷ N) ≫ F.map (eM.hom ▷ N) := by
    simpa only [Functor.map_comp, Category.assoc, comp_whiskerRight] using congrArg F.map E2
  refine ⟨ExactPairing.retractOfCoevaluationFactors (F.map (j' ≫ eM.hom))
    (ε F ≫ F.map u.hom ≫ φU.hom ≫ b ≫ φS.inv ≫ F.map Θ.hom ≫ F.map (K' ◁ eN.hom) ≫
      δ F K' N) ?_⟩
  rw [ExactPairing.map_coevaluation, hη]
  simp only [Functor.map_comp, Category.assoc, hF, comp_whiskerRight, δ_natural_left_assoc,
    δ_natural_left]
  rw [reassoc_of% E4]

end CategoryTheory

namespace Stacks.Cohomology.LeftDualPerfect

variable (X : RingedSpace.{u, u})

/-- The open `W` of `X`, as the image of the whole of `X|_W`. -/
abbrev topOpen (W : Opens X) : Opens X := W.isOpenEmbedding.functor.obj ⊤

/-- The open `topOpen X W` is `W`. -/
theorem topOpen_eq (W : Opens X) : topOpen X W = W := by simp

/-- Restriction of `O_X[0]` to an open is `O_{X|_W}[0]`. -/
def restrictUnitComplexIso (W : Opens X) :
    ((restrictMod X W).mapHomologicalComplex (ComplexShape.up ℤ)).obj (unitComplexR X.sheaf) ≅
      unitComplexR (X.restrict W.isOpenEmbedding).sheaf :=
  (HomologicalComplex.singleMapHomologicalComplex (restrictMod X W) (ComplexShape.up ℤ) 0).app _

/-- The section of degree `0` attached to the restriction to `W` of a morphism
`γ : O_X[0] ⟶ G` is the restriction to `W` of the section attached to `γ`. -/
theorem cocycleOf_restrict (W : Opens X) {G : Complexes X.sheaf}
    (γ : unitComplexR X.sheaf ⟶ G) :
    cocycleOf ((restrictUnitComplexIso X W).inv ≫
        ((restrictMod X W).mapHomologicalComplex (ComplexShape.up ℤ)).map γ) =
      (G.X 0).val.map (homOfLE le_top : topOpen X W ⟶ ⊤).op (cocycleOf γ) :=
  (congrArg (fun φ => φ.val.app (op ⊤) (one (X.restrict W.isOpenEmbedding).sheaf))
      (singleObjXSelf_inv_comp_singleMap_comp_f (restrictMod X W) _ γ)).trans
    ((congrArg (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv ≫
        γ.f 0).val.app (op (topOpen X W)))
        (PresheafOfModules.unit_map_one _ (homOfLE le_top : topOpen X W ⟶ ⊤).op).symm).trans
      (PresheafOfModules.naturality_apply _ _ _))

/-- The open `topOpen X W` is monotone in `W`. -/
theorem topOpen_mono {W U : Opens X} (h : W ≤ U) : topOpen X W ≤ topOpen X U := by
  rw [topOpen_eq, topOpen_eq]
  exact h

/-- Write a morphism `α : Q(O_X[0]) ⟶ Q(F)` in `D(O_X)` as `Q(γ) ≫ Q(f)⁻¹` with
`γ : O_X[0] ⟶ G` and `f : F ⟶ G` a quasi-isomorphism. Then every point `x` has an open
neighbourhood `U` with a cocycle `t` of degree `0` of `F` over `U` such that `f(t)` differs from
the restriction to `U` of the section attached to `γ` by a coboundary `d(u)`. -/
theorem exists_local_cocycle_data [HasDerivedCategory.{d} (Mod X.sheaf)]
    (F : Complexes X.sheaf)
    (α : DerivedCategory.Q.obj (unitComplexR X.sheaf) ⟶ DerivedCategory.Q.obj F) (x : X) :
    ∃ (G : Complexes X.sheaf) (γ : unitComplexR X.sheaf ⟶ G) (f : F ⟶ G)
      (_ : IsIso (DerivedCategory.Q.map f)),
      α = DerivedCategory.Q.map γ ≫ inv (DerivedCategory.Q.map f) ∧
      ∃ U : Opens X, x ∈ U ∧ ∃ (t : (F.X 0).val.obj (op (topOpen X U)))
        (_ : (F.d 0 1).val.app (op (topOpen X U)) t = 0)
        (u : (G.X (-1)).val.obj (op (topOpen X U))),
        (f.f 0).val.app (op (topOpen X U)) t =
          res (G.X 0) le_top (cocycleOf γ) + (G.d (-1) 0).val.app (op (topOpen X U)) u := by
  obtain ⟨G, γ, f, hf, hfac⟩ := DerivedCategory.left_fac (C := Mod X.sheaf) α
  have hfq : QuasiIso f := (DerivedCategory.isIso_Q_map_iff_quasiIso (C := Mod X.sheaf) f).mp hf
  obtain ⟨U, hxU, β, ⟨H⟩⟩ := RingedSpace.exists_local_lift_homotopy_restrictModules
    γ f 0 (isStrictlyPerfect_unitComplex X)
    (fun j hj => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))
    (fun j _ => (quasiIsoAt_iff_isIso_homologyMap f j).1 (hfq.quasiIsoAt j))
    (@IsIso.epi_of_iso _ _ _ _ _ ((quasiIsoAt_iff_isIso_homologyMap f 0).1 (hfq.quasiIsoAt 0))) x
  have hid := (cocycleOf_eq_add_of_homotopy (H.compLeft (restrictUnitComplexIso X U).inv)).trans
    (congrArg (· + _) (cocycleOf_restrict X U γ))
  exact ⟨G, γ, f, hf, hfac, U, hxU, _, cocycleOf_d ((restrictUnitComplexIso X U).inv ≫ β), _, hid⟩

/-- Let `α = Q(γ) ≫ Q(f)⁻¹ : Q(O_X[0]) ⟶ Q(F)` with `f` a quasi-isomorphism, and let `t` be a
cocycle of degree `0` of `F` over `U` with `f(t)` equal to the restriction of the section attached
to `γ` up to a coboundary. Then for `W ≤ U` the restriction of `α` to `W` is, under the comparison
isomorphisms, the image in the derived category of the morphism out of `O_{X|_W}[0]` sending `1`
to the restriction of `t` to `W`. -/
theorem restrict_map_eq_cocycleHom [HasDerivedCategory.{d} (Mod X.sheaf)] {W U : Opens X}
    [HasDerivedCategory.{d'} (Mod (X.restrict W.isOpenEmbedding).sheaf)]
    {F G : Complexes X.sheaf}
    (α : DerivedCategory.Q.obj (unitComplexR X.sheaf) ⟶ DerivedCategory.Q.obj F)
    (γ : unitComplexR X.sheaf ⟶ G) (f : F ⟶ G) (hf : IsIso (DerivedCategory.Q.map f))
    (hfac : α = DerivedCategory.Q.map γ ≫ inv (DerivedCategory.Q.map f)) (hW : W ≤ U)
    (t : (F.X 0).val.obj (op (topOpen X U))) (ht : (F.d 0 1).val.app (op (topOpen X U)) t = 0)
    (u : (G.X (-1)).val.obj (op (topOpen X U)))
    (hid : (f.f 0).val.app (op (topOpen X U)) t =
      res (G.X 0) le_top (cocycleOf γ) + (G.d (-1) 0).val.app (op (topOpen X U)) u) :
    (restrictMod X W).mapDerivedCategory.map α ≫
        (restrictMod X W).mapDerivedCategoryFactors.hom.app F =
      (restrictMod X W).mapDerivedCategoryFactors.hom.app (unitComplexR X.sheaf) ≫
        DerivedCategory.Q.map ((restrictUnitComplexIso X W).hom ≫
          cocycleHom (((restrictMod X W).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
            (res (F.X 0) (topOpen_mono X hW) t) (restrict_cocycle (topOpen_mono X hW) t ht)) :=
  Functor.mapDerivedCategory_map_eq_of_Q_eq (restrictMod X W) α γ f hf hfac _
    (Q_map_iso_comp_cocycleHom_comp (restrictUnitComplexIso X W) _ _ _ _ _
      ((restrict_cocycle_identity f (topOpen_mono X hW) _ _ _ hid).trans
        (congrArg (· + _) (cocycleOf_restrict X W γ).symm)))

open Stacks.Cohomology.MonoidalComplexes in
/-- **The direct-summand step of Stacks 0FPD over an open.** Let `s : S ⟶ M^• ⊗ N^•` be a
morphism of complexes whose image in `D(O_X)` is `Q(j) ▷ Q(N^•)` up to an isomorphism
`Q(S) ≅ Q(K) ⊗^L Q(N^•)`. If, over an open `W`, the coevaluation of `M ⊣ N` is induced by the
cocycle `s(t)` for a cocycle `t` of `S|_W`, then `M|_W` is a retract of `K|_W`. -/
theorem nonempty_retract_restrict [HasDerivedCategory.{d} (Mod X.sheaf)] (W : Opens X)
    [HasDerivedCategory.{d'} (Mod (X.restrict W.isOpenEmbedding).sheaf)]
    (M N : DerivedModules X.sheaf)
    (pair : letI := derivedCategoryMonoidalCategory X; ExactPairing M N)
    (Mc Nc : Complexes X.sheaf) (eM : DerivedCategory.Q.obj Mc ≅ M)
    (eN : DerivedCategory.Q.obj Nc ≅ N) (hM : KFlat X.sheaf Mc) (hN : KFlat X.sheaf Nc)
    (K S : Complexes X.sheaf) (j : K ⟶ Mc) :
    letI := cochainComplexMonoidalCategory X
    letI := derivedCategoryMonoidalCategory X
    ∀ (s : S ⟶ Mc ⊗ Nc)
      (Θ : DerivedCategory.Q.obj S ≅ DerivedCategory.Q.obj K ⊗ DerivedCategory.Q.obj Nc)
      (_ : Θ.hom ≫ (DerivedCategory.Q.map j ▷ DerivedCategory.Q.obj Nc) =
        DerivedCategory.Q.map s ≫ ((symmetricMonoidalDerivedCategory X).comparison Mc Nc hM hN).inv)
      (t : ((((restrictMod X W).mapHomologicalComplex (ComplexShape.up ℤ)).obj S).X 0).val.obj
        (op ⊤))
      (ht : ((((restrictMod X W).mapHomologicalComplex (ComplexShape.up ℤ)).obj S).d 0 1).val.app
        (op ⊤) t = 0),
      (restrictMod X W).mapDerivedCategory.map (coevaluationUnitHom X Mc Nc hM hN
          (letI := pair
           η_ M N ≫ (eM.inv ⊗ₘ eN.inv))) ≫
          (restrictMod X W).mapDerivedCategoryFactors.hom.app (Mc ⊗ Nc) =
        (restrictMod X W).mapDerivedCategoryFactors.hom.app (unitComplexR X.sheaf) ≫
          DerivedCategory.Q.map ((restrictUnitComplexIso X W).hom ≫
            cocycleHom (((restrictMod X W).mapHomologicalComplex (ComplexShape.up ℤ)).obj (Mc ⊗ Nc))
              (((((restrictMod X W).mapHomologicalComplex (ComplexShape.up ℤ)).map s).f 0).val.app
                (op ⊤) t)
              (cocycleHom_d_comp t ht (((restrictMod X W).mapHomologicalComplex
                (ComplexShape.up ℤ)).map s))) →
      Nonempty (Retract ((restrictMod X W).mapDerivedCategory.obj M)
        ((restrictMod X W).mapDerivedCategory.obj (DerivedCategory.Q.obj K))) := by
  let := cochainComplexMonoidalCategory X
  let := derivedCategoryMonoidalCategory X
  let := pair
  intro s Θ hΘ t ht hβ
  let := derivedCategoryMonoidalCategory (X.restrict W.isOpenEmbedding)
  let := restrictDerivedMonoidal X W
  exact nonempty_retract_map_of_factorization (restrictMod X W).mapDerivedCategory M N
    (symmetricMonoidalDerivedCategory X).unitIso eM eN
    ((symmetricMonoidalDerivedCategory X).comparison Mc Nc hM hN) (DerivedCategory.Q.map j)
    (DerivedCategory.Q.map s) Θ hΘ
    ((restrictMod X W).mapDerivedCategoryFactors.app (unitComplexR X.sheaf))
    ((restrictMod X W).mapDerivedCategoryFactors.app S)
    ((restrictMod X W).mapDerivedCategoryFactors.app (Mc ⊗ Nc))
    (DerivedCategory.Q.map (((restrictMod X W).mapHomologicalComplex (ComplexShape.up ℤ)).map s))
    ((restrictMod X W).mapDerivedCategoryFactors_hom_naturality s)
    (DerivedCategory.Q.map ((restrictUnitComplexIso X W).hom ≫
      cocycleHom (((restrictMod X W).mapHomologicalComplex (ComplexShape.up ℤ)).obj S) t ht))
    (hβ.trans (congrArg (_ ≫ ·) ((congrArg DerivedCategory.Q.map ((congrArg (_ ≫ ·)
      (cocycleHom_comp t ht _)).symm.trans (Category.assoc _ _ _).symm)).trans
        (DerivedCategory.Q.map_comp _ _))))

end Stacks.Cohomology.LeftDualPerfect
