module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateNaturality

/-!
# Transposes, pastings and conjugates of the base change map of a square of adjunctions

For a square of adjunctions `Lf ⊣ Rf`, `Lf' ⊣ Rf'` with comparisons `Lg ⋙ Lf' ≅ Lc ≅ Lf ⋙ Lg'`,
`Stacks.CategoryTheory.BaseChange.map` is the base change map `Lg (Rf K) ⟶ Rf' (Lg' K)`. This
file records how it interacts with transposes, with pasting of squares, with the comparison of
internal homs, and with conjugation of the right adjoints.

## Main results

* `Stacks.CategoryTheory.BaseChange.homEquiv_symm_map_comp_map` and
  `Stacks.CategoryTheory.BaseChange.isIso_homEquiv_symm_map_comp_map`: the transpose of `Lg u`
  followed by the base change map, and its invertibility.
* `Stacks.CategoryTheory.BaseChange.twoSquare_eq_mateEquiv_symm_conjugateEquiv`: the base change
  2-square as a mate of a conjugate.
* `Stacks.CategoryTheory.BaseChange.isIso_map_iff_of_iso`,
  `Stacks.CategoryTheory.BaseChange.isIso_map_of_isIso_counit_app`: invertibility criteria.
* `Stacks.CategoryTheory.BaseChange.map_comp_adjunction`: the base change map of a pasted square.
* `Stacks.CategoryTheory.BaseChange.map_comp_map_homComparison_counit`: compatibility with the
  comparison of internal homs.
* `Stacks.CategoryTheory.BaseChange.isIso_map_of_isIso_mateEquiv_symm`: invertibility read on
  the mate of the comparison of the right adjoints.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory

/-- Let `adj : L ⊣ R` and `adj' : L' ⊣ R'` be adjunctions and `e : R' ≅ R`.  Then `L` and `L'`
are two left adjoints of `R`, compared by `CategoryTheory.Adjunction.leftAdjointUniq`, and the
conjugate of that comparison is `e.hom`. -/
theorem conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom'
    {C : Type*} {D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R') (e : R' ≅ R) :
    conjugateEquiv adj' adj (Adjunction.leftAdjointUniq adj (adj'.ofNatIsoRight e)).hom =
      e.hom := by
  have h := conjugateEquiv_comp adj' adj adj'
    (Adjunction.leftAdjointUniq adj (adj'.ofNatIsoRight e)).hom
    (Adjunction.leftAdjointUniq (adj'.ofNatIsoRight e) adj).hom
  rw [conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom, Adjunction.leftAdjointUniq_trans,
    Adjunction.leftAdjointUniq_refl, conjugateEquiv_id] at h
  exact (Iso.comp_inv_eq_id e).1 h

/-- The inverse of the comparison of two left adjoints of one functor is the comparison taken
the other way round. -/
theorem leftAdjointUniq_inv {C : Type*} {D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G) :
    (Adjunction.leftAdjointUniq adj₁ adj₂).inv = (Adjunction.leftAdjointUniq adj₂ adj₁).hom := by
  ext x
  exact Adjunction.leftAdjointUniq_inv_app adj₁ adj₂ x

end Stacks.CategoryTheory

namespace Stacks.CategoryTheory.BaseChange

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ t

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Lg' : B ⥤ B'} {Lc : A ⥤ B'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)

/-- **The base change map turns a map with invertible transpose into one.**  If
`u : P ⟶ Rf K` has invertible transpose `Lf P ⟶ K` under `Lf ⊣ Rf`, then
`Lg u ≫ (base change map at K) : Lg P ⟶ Rf' (Lg' K)` has invertible transpose under `Lf' ⊣ Rf'`:
it is the comparison of the two composites around the square followed by `Lg'` of the transpose
of `u`. -/
theorem homEquiv_symm_map_comp_map {P : A} {K : B} (u : P ⟶ Rf.obj K) :
    (adjf'.homEquiv (Lg.obj P) (Lg'.obj K)).symm (Lg.map u ≫ map adjf adjf' eg ef K) =
      eg.hom.app P ≫ ef.inv.app P ≫ Lg'.map ((adjf.homEquiv P K).symm u) := by
  rw [Adjunction.homEquiv_naturality_left_symm, homEquiv_symm_map, Adjunction.homEquiv_counit,
    Functor.map_comp]
  have h1 := eg.hom.naturality u
  have h2 := ef.inv.naturality u
  simp only [Functor.comp_map] at h1 h2
  rw [← Category.assoc, ← Category.assoc, h1]
  simp only [Category.assoc]
  rw [← reassoc_of% h2]

/-- If `u : P ⟶ Rf K` has invertible transpose, so does `Lg u ≫ (base change map at K)`. -/
theorem isIso_homEquiv_symm_map_comp_map {P : A} {K : B} (u : P ⟶ Rf.obj K)
    [IsIso ((adjf.homEquiv P K).symm u)] :
    IsIso ((adjf'.homEquiv (Lg.obj P) (Lg'.obj K)).symm (Lg.map u ≫ map adjf adjf' eg ef K)) := by
  rw [homEquiv_symm_map_comp_map]
  infer_instance

/-- **The base change map as a horizontal mate.**  When the horizontal functors also have right
adjoints `pg ⊣ qg`, `pg' ⊣ qg'`, the base change map `qf ⋙ pg ⟶ pg' ⋙ qf'` (the mate across the
vertical adjunctions of the comparison of the two composites of left adjoints) is the mate
across the horizontal adjunctions of the conjugate comparison `qg' ⋙ qf ⟶ qf' ⋙ qg` of the two
composites of right adjoints. -/
theorem twoSquare_eq_mateEquiv_symm_conjugateEquiv {Rg : A' ⥤ A} {Rg' : B' ⥤ B}
    (ag : Lg ⊣ Rg) (ag' : Lg' ⊣ Rg') :
    twoSquare adjf adjf' eg ef = (mateEquiv ag' ag).symm (TwoSquare.mk _ _ _ _
      (conjugateEquiv (adjf.comp ag') (ag.comp adjf') (pullbackComparison eg ef).natTrans)) :=
  (mateEquiv ag' ag).eq_symm_apply.2 <| by
    ext K
    exact congrArg (fun t => NatTrans.app t K)
      (iterated_mateEquiv_conjugateEquiv adjf adjf' ag ag' (pullbackComparison eg ef))

/-- **The transpose of the base change map along the horizontal adjunctions.** When the
horizontal functors have right adjoints `Lg ⊣ Rg`, `Lg' ⊣ Rg'`, the transpose of the base change
map at `K` under `Lg ⊣ Rg` is `Rf` of the unit of `Lg' ⊣ Rg'` at `K` followed by the conjugate
comparison `Rg' ⋙ Rf ⟶ Rf' ⋙ Rg` of the two composites of right adjoints at `Lg' K`. -/
theorem homEquiv_map_eq_unit_comp {Rg : A' ⥤ A} {Rg' : B' ⥤ B} (ag : Lg ⊣ Rg)
    (ag' : Lg' ⊣ Rg') (K : B) :
    ag.homEquiv _ _ (map adjf adjf' eg ef K) =
      Rf.map (ag'.unit.app K) ≫ (conjugateEquiv (adjf.comp ag') (ag.comp adjf')
        (pullbackComparison eg ef).natTrans).app (Lg'.obj K) := by
  rw [Adjunction.homEquiv_unit, map, twoSquare_eq_mateEquiv_symm_conjugateEquiv adjf adjf' eg ef
    ag ag']
  exact (unit_mateEquiv_symm ag' ag _ K).symm

/-- **Invertibility of the base change map is invariant under isomorphism of the object**, in
both directions: the base change map is the component of a natural transformation. -/
theorem isIso_map_iff_of_iso {K K' : B} (e : K ≅ K') :
    IsIso (map adjf adjf' eg ef K) ↔ IsIso (map adjf adjf' eg ef K') :=
  NatTrans.isIso_app_iff_of_iso (twoSquare adjf adjf' eg ef).natTrans e

/-- **The base change map is invertible where the counit and the unit are.**  If the counit of
`Lf ⊣ Rf` is invertible at `K` and the unit of `Lf' ⊣ Rf'` at `Lg (Rf K)`, the base change map at
`K` is invertible: it is that unit followed by `Rf'` of its transpose, which is the counit up to
the comparison of the two composites. -/
theorem isIso_map_of_isIso_counit_app (K : B) [IsIso (adjf.counit.app K)]
    [IsIso (adjf'.unit.app (Lg.obj (Rf.obj K)))] : IsIso (map adjf adjf' eg ef K) := by
  rw [map_eq, Adjunction.homEquiv_unit]
  infer_instance

section Pasting

universe v₅ v₆ u₅ u₆

variable {C : Type u₅} {C' : Type u₆} [Category.{v₅} C] [Category.{v₆} C']
  {L₁ : A ⥤ C} {R₁ : C ⥤ A} {L₃ : C ⥤ B} {R₃ : B ⥤ C} {L₂ : A' ⥤ C'} {R₂ : C' ⥤ A'}
  {L₄ : C' ⥤ B'} {R₄ : B' ⥤ C'} {H : C ⥤ C'} {Lc' : C ⥤ B'}

/-- **Pasting of base change maps along composite adjunctions.**  Let the left adjoints of the
square factor as `L₁ ⋙ L₃` and `L₂ ⋙ L₄` through a middle functor `H`, with comparisons `eα` of
the first square and `eg'`, `ef'` of the second, pasted to a comparison of the outer square.  Then
the base change map of the outer square at `K` is the base change map of the first square at
`R₃ K` followed by `R₂` of the base change map of the second square at `K`.
This is `CategoryTheory.mateEquiv_hcomp`. -/
theorem map_comp_adjunction (a₁ : L₁ ⊣ R₁) (a₃ : L₃ ⊣ R₃) (a₂ : L₂ ⊣ R₂) (a₄ : L₄ ⊣ R₄)
    (eα : Lg ⋙ L₂ ≅ L₁ ⋙ H) (eg' : H ⋙ L₄ ≅ Lc') (ef' : L₃ ⋙ Lg' ≅ Lc') (K : B) :
    map (a₁.comp a₃) (a₂.comp a₄)
        ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eα L₄ ≪≫
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L₁ (eg' ≪≫ ef'.symm) ≪≫
          (Functor.associator _ _ _).symm) (Iso.refl _) K =
      map a₁ a₂ eα (Iso.refl _) (R₃.obj K) ≫ R₂.map (map a₃ a₄ eg' ef' K) := by
  have h : pullbackComparison ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eα L₄ ≪≫
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L₁ (eg' ≪≫ ef'.symm) ≪≫
          (Functor.associator _ _ _).symm) (Iso.refl ((L₁ ⋙ L₃) ⋙ Lg')) =
      TwoSquare.vComp (pullbackComparison eα (Iso.refl _)) (pullbackComparison eg' ef') := by
    ext X
    simp [pullbackComparison, TwoSquare.vComp]
  simp only [map, twoSquare]
  rw [h, mateEquiv_hcomp]
  simp [TwoSquare.hComp]

end Pasting

section InternalHom

variable {Rg : A' ⥤ A} {Rg' : B' ⥤ B} (ag : Lg ⊣ Rg) (ag' : Lg' ⊣ Rg')
  {LM RM : B ⥤ B} {LM' RM' : B' ⥤ B'} (a : LM ⊣ RM) (a' : LM' ⊣ RM') (μ : LM ⋙ Lg' ≅ Lg' ⋙ LM')

/-- **The base change map at an internal Hom, against the counit.** Let `LM ⊣ RM` and
`LM' ⊣ RM'` be internal-Hom adjunctions on `B` and `B'`, compared along `Lg'` by
`μ : LM ⋙ Lg' ≅ Lg' ⋙ LM'`, and let `φ : Lg' (RM K) ⟶ RM' (Lg' K)` be the transpose of
`μ⁻¹ ≫ Lg'(counit)`. Then the base change map at `RM (Rg' L)` followed by `Rf'` of `φ` and of
`RM'` of the counit of `Lg' ⊣ Rg'` is the counit of `Lg ⊣ Rg` after the identification
`Rf (RM (Rg' L)) ≅ Rf (Rg' (RM' L)) ≅ Rg (Rf' (RM' L))` given by the conjugates of `μ` and of the
comparison of the two composites. -/
theorem map_comp_map_homComparison_counit (e : Lg ⋙ Lf' ≅ Lf ⋙ Lg') (L : B') :
    map adjf adjf' e (Iso.refl _) (RM.obj (Rg'.obj L)) ≫
        Rf'.map (a'.homEquiv _ _ (μ.inv.app (RM.obj (Rg'.obj L)) ≫
          Lg'.map (a.counit.app (Rg'.obj L))) ≫ RM'.map (ag'.counit.app L)) =
      Lg.map (Rf.map (((conjugateIsoEquiv (ag'.comp a') (a.comp ag')) μ).inv.app L) ≫
          (conjugateEquiv (adjf.comp ag') (ag.comp adjf') e.hom).app (RM'.obj L)) ≫
        ag.counit.app _ := by
  have hc : (pullbackComparison e (Iso.refl ((Lf ⋙ Lg')))).natTrans = e.hom := by
    ext X
    simp [pullbackComparison]
  refine Eq.trans ?_ (Adjunction.homEquiv_counit ag _ _ _)
  rw [Equiv.eq_symm_apply, Adjunction.homEquiv_naturality_right,
    homEquiv_map_eq_unit_comp adjf adjf' e (Iso.refl _) ag ag', hc,
    conjugateIsoEquiv_inv_app_eq_unit_comp ag' a a' μ L, Functor.map_comp Rf, Category.assoc]
  have hn := (conjugateEquiv (adjf.comp ag') (ag.comp adjf') e.hom).naturality
    (a'.homEquiv _ _ (μ.inv.app (RM.obj (Rg'.obj L)) ≫ Lg'.map (a.counit.app (Rg'.obj L))) ≫
      RM'.map (ag'.counit.app L))
  simp only [Functor.comp_map, Functor.map_comp, Functor.id_obj, Category.assoc] at hn ⊢
  rw [hn]

/-- `map_comp_map_homComparison_counit` with the right adjoint `Rf'` a composite `Rf₁ ⋙ Rf₂` and
the comparison `φ` given by an equation, in the shape in which the base change map is followed by
`Rf₂ (Rf₁ φ)` and then by `Rf₂ (Rf₁ (RM' counit))`. -/
theorem map_comp_map_homComparison_counit_of_eq {C : Type*} [Category C] {Rf₁ : B' ⥤ C}
    {Rf₂ : C ⥤ A'} (adj₂ : Lf' ⊣ Rf₁ ⋙ Rf₂) (e : Lg ⋙ Lf' ≅ Lf ⋙ Lg') (L : B')
    (φ : Lg'.obj (RM.obj (Rg'.obj L)) ⟶ RM'.obj (Lg'.obj (Rg'.obj L)))
    (hφ : φ = a'.homEquiv _ _ (μ.inv.app (RM.obj (Rg'.obj L)) ≫
      Lg'.map (a.counit.app (Rg'.obj L))))
    (cI : RM' ⋙ Rg' ≅ Rg' ⋙ RM) (hI : cI = conjugateIsoEquiv (ag'.comp a') (a.comp ag') μ)
    (cJ : Rg' ⋙ Rf ≅ (Rf₁ ⋙ Rf₂) ⋙ Rg)
    (hJ : cJ = conjugateIsoEquiv (adjf.comp ag') (ag.comp adj₂) e) :
    (map adjf adj₂ e (Iso.refl _) (RM.obj (Rg'.obj L)) ≫ Rf₂.map (Rf₁.map φ)) ≫
        Rf₂.map (Rf₁.map (RM'.map (ag'.counit.app L))) =
      Lg.map (Rf.map (cI.inv.app L) ≫ cJ.hom.app (RM'.obj L)) ≫ ag.counit.app _ := by
  subst hφ hI hJ
  rw [Category.assoc, ← Functor.map_comp Rf₂, ← Functor.map_comp Rf₁]
  exact map_comp_map_homComparison_counit adjf adj₂ ag ag' a a' μ e L

end InternalHom

/-! ### Pullback comparisons induced by comparisons of right adjoints -/

section Conjugate

variable {L₂ L₅ : A ⥤ B'} {R₂ R₅ : B' ⥤ A} {ι : Type t} {Lk : ι → (A ⥤ B')} {Rk : ι → (B' ⥤ A)}
  {Rg : A' ⥤ A} {Rg' : B' ⥤ B}

/-- Let the two composites of left adjoints around the square be compared with left adjoints
`L₂`, `L₅` of composites of right adjoints through comparisons `pc`, `pc'`, and these with a
family of left adjoints `Lk k` through comparisons `tc`, `tc'` of right adjoints, all induced by
uniqueness of left adjoints; let `k₁ = k₂`.  Then the conjugate of the resulting comparison of the
two composites of left adjoints is the composite of the comparisons of right adjoints. -/
theorem conjugateEquiv_pullbackComparison_leftAdjointUniq (ag : Lg ⊣ Rg) (ag' : Lg' ⊣ Rg')
    (a₂ : L₂ ⊣ R₂) (a₅ : L₅ ⊣ R₅) (ak : ∀ k, Lk k ⊣ Rk k) {k₁ k₂ : ι} (hk : k₁ = k₂)
    (pc : R₂ ≅ Rf' ⋙ Rg) (tc : R₂ ≅ Rk k₂) (pc' : R₅ ≅ Rg' ⋙ Rf) (tc' : R₅ ≅ Rk k₁) :
    conjugateEquiv (adjf.comp ag') (ag.comp adjf')
        (pullbackComparison
          ((Adjunction.leftAdjointUniq (a₂.ofNatIsoRight pc) (ag.comp adjf')).symm ≪≫
            Adjunction.leftAdjointUniq a₂ ((ak k₂).ofNatIsoRight tc.symm))
          (((Adjunction.leftAdjointUniq (a₅.ofNatIsoRight pc') (adjf.comp ag')).symm ≪≫
            Adjunction.leftAdjointUniq a₅ ((ak k₁).ofNatIsoRight tc'.symm)) ≪≫
              eqToIso (congrArg Lk hk))).natTrans =
      pc'.inv ≫ tc'.hom ≫ eqToHom (congrArg Rk hk) ≫ tc.inv ≫ pc.hom := by
  subst hk
  have e5 := conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom a₅ pc' (adjf.comp ag')
  have e4 := conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom (ak k₁) tc'.symm a₅
  have e2 := conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom' a₂ (ak k₁) tc.symm
  have e1 := conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom' (ag.comp adjf') a₂ pc
  simp only [Iso.symm_inv, Iso.symm_hom] at e4 e2
  simp only [eqToHom_refl, Category.id_comp]
  rw [← e5, ← e4, ← e2, ← e1, conjugateEquiv_comp_assoc, conjugateEquiv_comp_assoc,
    conjugateEquiv_comp]
  congr 1
  simp only [pullbackComparison, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    eqToIso_refl, Iso.refl_inv, Category.id_comp, Category.assoc, leftAdjointUniq_inv]

/-- A component of a mate is invertible as soon as the same component of the mate, across two
other adjunctions with the same right adjoints, of the same 2-cell is: the right adjoints and the
vertical functors are allowed to differ by equalities, the two mates then differ by the
comparisons of left adjoints. -/
theorem isIso_mateEquiv_symm_app_of_eq {Mg : A ⥤ A'} {Sg : A' ⥤ A} {Mg' : B ⥤ B'}
    {Sg' : B' ⥤ B} {Tf : B ⥤ A} {Tf' : B' ⥤ A'} (ag : Lg ⊣ Rg) (bg : Mg ⊣ Sg) (ag' : Lg' ⊣ Rg')
    (bg' : Mg' ⊣ Sg') (hg : Rg = Sg) (hg' : Rg' = Sg') (hf : Rf = Tf) (hf' : Rf' = Tf')
    (θ : Rg' ⋙ Rf ⟶ Rf' ⋙ Rg) (θ' : Sg' ⋙ Tf ⟶ Tf' ⋙ Sg) (h₁ : Sg' ⋙ Tf = Rg' ⋙ Rf)
    (h₂ : Rf' ⋙ Rg = Tf' ⋙ Sg) (hθ : θ' = eqToHom h₁ ≫ θ ≫ eqToHom h₂) (K : B)
    (hK : IsIso (((mateEquiv bg' bg).symm (TwoSquare.mk _ _ _ _ θ')).natTrans.app K)) :
    IsIso (((mateEquiv ag' ag).symm (TwoSquare.mk _ _ _ _ θ)).natTrans.app K) := by
  subst hg hg' hf hf'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hθ
  subst hθ
  rw [mateEquiv_symm_congr_left ag' bg' ag, mateEquiv_symm_congr_right bg' bg ag]
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- A mate is invertible as soon as the mate, across two other adjunctions with the same right
adjoints, of the same 2-cell is: the right adjoints and the vertical functors are allowed to
differ by equalities, the two mates then differ by the comparisons of left adjoints. -/
theorem isIso_mateEquiv_symm_of_eq {Mg : A ⥤ A'} {Sg : A' ⥤ A} {Mg' : B ⥤ B'}
    {Sg' : B' ⥤ B} {Tf : B ⥤ A} {Tf' : B' ⥤ A'} (ag : Lg ⊣ Rg) (bg : Mg ⊣ Sg) (ag' : Lg' ⊣ Rg')
    (bg' : Mg' ⊣ Sg') (hg : Rg = Sg) (hg' : Rg' = Sg') (hf : Rf = Tf) (hf' : Rf' = Tf')
    (θ : Rg' ⋙ Rf ⟶ Rf' ⋙ Rg) (θ' : Sg' ⋙ Tf ⟶ Tf' ⋙ Sg) (h₁ : Sg' ⋙ Tf = Rg' ⋙ Rf)
    (h₂ : Rf' ⋙ Rg = Tf' ⋙ Sg) (hθ : θ' = eqToHom h₁ ≫ θ ≫ eqToHom h₂)
    (hK : IsIso ((mateEquiv bg' bg).symm (TwoSquare.mk _ _ _ _ θ')).natTrans) :
    IsIso ((mateEquiv ag' ag).symm (TwoSquare.mk _ _ _ _ θ)).natTrans :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun K =>
    isIso_mateEquiv_symm_app_of_eq ag bg ag' bg' hg hg' hf hf' θ θ' h₁ h₂ hθ K inferInstance

/-- **Invertibility of the base change morphism at one object, transported to another choice of
adjunctions.**
Suppose the comparisons of the two composites of left adjoints around the square are induced,
as in `conjugateEquiv_pullbackComparison_leftAdjointUniq`, by comparisons `pc`, `tc`, `pc'`,
`tc'` of right adjoints, and let `bg`, `bg'` be adjunctions of the horizontal functors whose
right adjoints, like those of the vertical functors and of the family, agree with the given
ones up to equality.  If the mate across `bg`, `bg'` of the comparison `mc' ≫ mc⁻¹` of composite
right adjoints, built from the same data, is invertible, then so is the base change map at
every object. -/
theorem isIso_map_of_isIso_mateEquiv_symm_app (ag : Lg ⊣ Rg) (ag' : Lg' ⊣ Rg')
    (a₂ : L₂ ⊣ R₂) (a₅ : L₅ ⊣ R₅) (ak : ∀ k, Lk k ⊣ Rk k) {k₁ k₂ : ι} (hk : k₁ = k₂)
    (pc : R₂ ≅ Rf' ⋙ Rg) (tc : R₂ ≅ Rk k₂) (pc' : R₅ ≅ Rg' ⋙ Rf) (tc' : R₅ ≅ Rk k₁)
    {Mg : A ⥤ A'} {Sg : A' ⥤ A} {Mg' : B ⥤ B'} {Sg' : B' ⥤ B} {Tf : B ⥤ A} {Tf' : B' ⥤ A'}
    {Nk : ι → (B' ⥤ A)} (bg : Mg ⊣ Sg) (bg' : Mg' ⊣ Sg') (hg : Rg = Sg) (hg' : Rg' = Sg')
    (hf : Rf = Tf) (hf' : Rf' = Tf') (hk' : ∀ k, Rk k = Nk k)
    (h₃ : Tf' ⋙ Sg = Rf' ⋙ Rg) (h₄ : Sg' ⋙ Tf = Rg' ⋙ Rf)
    (mc : Tf' ⋙ Sg ≅ Nk k₂) (mc' : Sg' ⋙ Tf ≅ Nk k₁)
    (hmc : mc = eqToIso h₃ ≪≫ pc.symm ≪≫ tc ≪≫ eqToIso (hk' k₂))
    (hmc' : mc' = eqToIso h₄ ≪≫ pc'.symm ≪≫ tc' ≪≫ eqToIso (hk' k₁))
    (β : Tf ⋙ Mg ⟶ Mg' ⋙ Tf')
    (hβ : β = ((mateEquiv bg' bg).symm
      (TwoSquare.mk _ _ _ _ (mc'.hom ≫ eqToHom (congrArg Nk hk) ≫ mc.inv))).natTrans)
    (K : B) (hK : IsIso (β.app K)) :
    IsIso (map adjf adjf'
      ((Adjunction.leftAdjointUniq (a₂.ofNatIsoRight pc) (ag.comp adjf')).symm ≪≫
        Adjunction.leftAdjointUniq a₂ ((ak k₂).ofNatIsoRight tc.symm))
      (((Adjunction.leftAdjointUniq (a₅.ofNatIsoRight pc') (adjf.comp ag')).symm ≪≫
        Adjunction.leftAdjointUniq a₅ ((ak k₁).ofNatIsoRight tc'.symm)) ≪≫
          eqToIso (congrArg Lk hk)) K) := by
  rw [map, twoSquare_eq_mateEquiv_symm_conjugateEquiv _ _ _ _ ag ag',
    conjugateEquiv_pullbackComparison_leftAdjointUniq adjf adjf' ag ag' a₂ a₅ ak hk]
  subst hβ
  refine isIso_mateEquiv_symm_app_of_eq ag bg ag' bg' hg hg' hf hf' _ _ h₄ h₃.symm ?_ K hK
  subst hmc hmc' hk
  simp

/-- **Invertibility of the base change morphism, transported to another choice of adjunctions.**
Suppose the comparisons of the two composites of left adjoints around the square are induced,
as in `conjugateEquiv_pullbackComparison_leftAdjointUniq`, by comparisons `pc`, `tc`, `pc'`,
`tc'` of right adjoints, and let `bg`, `bg'` be adjunctions of the horizontal functors whose
right adjoints, like those of the vertical functors and of the family, agree with the given
ones up to equality.  If the mate across `bg`, `bg'` of the comparison `mc' ≫ mc⁻¹` of composite
right adjoints, built from the same data, is invertible, then so is the base change map at
every object. -/
theorem isIso_map_of_isIso_mateEquiv_symm (ag : Lg ⊣ Rg) (ag' : Lg' ⊣ Rg')
    (a₂ : L₂ ⊣ R₂) (a₅ : L₅ ⊣ R₅) (ak : ∀ k, Lk k ⊣ Rk k) {k₁ k₂ : ι} (hk : k₁ = k₂)
    (pc : R₂ ≅ Rf' ⋙ Rg) (tc : R₂ ≅ Rk k₂) (pc' : R₅ ≅ Rg' ⋙ Rf) (tc' : R₅ ≅ Rk k₁)
    {Mg : A ⥤ A'} {Sg : A' ⥤ A} {Mg' : B ⥤ B'} {Sg' : B' ⥤ B} {Tf : B ⥤ A} {Tf' : B' ⥤ A'}
    {Nk : ι → (B' ⥤ A)} (bg : Mg ⊣ Sg) (bg' : Mg' ⊣ Sg') (hg : Rg = Sg) (hg' : Rg' = Sg')
    (hf : Rf = Tf) (hf' : Rf' = Tf') (hk' : ∀ k, Rk k = Nk k)
    (h₃ : Tf' ⋙ Sg = Rf' ⋙ Rg) (h₄ : Sg' ⋙ Tf = Rg' ⋙ Rf)
    (mc : Tf' ⋙ Sg ≅ Nk k₂) (mc' : Sg' ⋙ Tf ≅ Nk k₁)
    (hmc : mc = eqToIso h₃ ≪≫ pc.symm ≪≫ tc ≪≫ eqToIso (hk' k₂))
    (hmc' : mc' = eqToIso h₄ ≪≫ pc'.symm ≪≫ tc' ≪≫ eqToIso (hk' k₁))
    (hK : IsIso ((mateEquiv bg' bg).symm
      (TwoSquare.mk _ _ _ _ (mc'.hom ≫ eqToHom (congrArg Nk hk) ≫ mc.inv))).natTrans) :
    ∀ K, IsIso (map adjf adjf'
      ((Adjunction.leftAdjointUniq (a₂.ofNatIsoRight pc) (ag.comp adjf')).symm ≪≫
        Adjunction.leftAdjointUniq a₂ ((ak k₂).ofNatIsoRight tc.symm))
      (((Adjunction.leftAdjointUniq (a₅.ofNatIsoRight pc') (adjf.comp ag')).symm ≪≫
        Adjunction.leftAdjointUniq a₅ ((ak k₁).ofNatIsoRight tc'.symm)) ≪≫
          eqToIso (congrArg Lk hk)) K) := by
  intro K
  exact isIso_map_of_isIso_mateEquiv_symm_app adjf adjf' ag ag' a₂ a₅ ak hk pc tc pc' tc' bg bg'
    hg hg' hf hf' hk' h₃ h₄ mc mc' hmc hmc' _ rfl K (NatIso.isIso_app_of_isIso _ K)

end Conjugate

end Stacks.CategoryTheory.BaseChange

end
