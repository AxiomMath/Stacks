module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceDictionarySquares
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsSmul
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSheavesProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcChartFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability

/-!
# A sheaf of modules read chartwise as morphisms of restrictions is the internal Hom

Let `Y` be an algebraic space and `A`, `C` two `𝒪_Y`-modules. For an étale scheme chart
`φ_T : T ⟶ Y` the morphisms `A|_T ⟶ C|_T` of the restrictions to the slice `Y_étale/T` (the
sections over `T` of the internal Hom `𝓗om_{𝒪_Y}(A, C)` of Stacks 03EM) are the morphisms
`φ_T^*A ⟶ φ_T^*C` of the pullbacks of Stacks 03LU to the chart, read through the comparison of
Stacks 04M0 (`AlgebraicGeometry.Space.chartHomEquiv`); restriction along a morphism of charts is
the restricted reading of Stacks 03LU (`AlgebraicGeometry.Space.chartHomEquiv_sliceRestrict`),
and multiplication by a function on `T` is multiplication by the corresponding global function on
the chart (`AlgebraicGeometry.Space.chartHomEquiv_smul`).

Consequently a sheaf of `𝒪_Y`-modules `F` (with sections in any universe-lifted form) whose
sections over every chart are identified, additively, naturally for the restricted readings and
linearly, with the morphisms of the pullbacks of `A` and `C` to that chart, is the internal Hom
(`AlgebraicGeometry.Space.chartReadingIso`), hence quasi-coherent when `A` is of finite
presentation and `C` is quasi-coherent, by Stacks 03M1 (6)
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_chartReading`). This is the form in which the
proof of Stacks 0CKG (2) identifies the band of the gerbe of smooth lifts with a sheaf of
homomorphisms.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace CategoryTheory

/-- Conjugating by a square of isomorphisms through a natural middle map: given two commuting
squares of isomorphisms and a naturality square `b₁ ≫ mC = mA ≫ b₂`, the conjugates of `b₂` and
of `b₁` agree. This is the abstract rearrangement behind
`AlgebraicGeometry.Space.chartHomEquiv_sliceRestrict`, stated in an arbitrary category so that no
rewrite is performed among modules. -/
theorem conj_comp_eq_of_squares {C : Type*} [Category C]
    {PA PC QA QC XA XC YA YC RA RC : C}
    (cA : QA ≅ PA) (cC : QC ≅ PC) (ΦA : PA ≅ RA) (ΦC : PC ≅ RC) (gA : QA ≅ XA) (gC : QC ≅ XC)
    (mA : XA ⟶ YA) (mC : XC ⟶ YC) (oA : YA ≅ RA) (oC : YC ≅ RC) (b₁ : XA ⟶ XC) (b₂ : YA ⟶ YC)
    (sqA : gA.hom ≫ mA ≫ oA.hom = cA.hom ≫ ΦA.hom)
    (sqC : gC.hom ≫ mC ≫ oC.hom = cC.hom ≫ ΦC.hom) (nat : b₁ ≫ mC = mA ≫ b₂)
    {l : RA ⟶ RC} {r : QA ⟶ QC} (hl : l = oA.inv ≫ b₂ ≫ oC.hom)
    (hr : r = gA.hom ≫ b₁ ≫ gC.inv) :
    ΦA.hom ≫ l ≫ ΦC.inv = cA.inv ≫ r ≫ cC.hom := by
  subst hl hr
  have hA : ΦA.hom = cA.inv ≫ gA.hom ≫ mA ≫ oA.hom := by
    rw [sqA, Iso.inv_hom_id_assoc]
  have hC : mC ≫ oC.hom ≫ ΦC.inv = gC.inv ≫ cC.hom := by
    rw [← Category.assoc, ← cancel_epi gC.hom, ← Category.assoc, sqC, Iso.hom_inv_id_assoc,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hA]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% nat, hC]

/-- Moving an endomorphism past the last factor of a triple composite. -/
theorem comp_comp_comp_eq_of_comm {C : Type*} [Category C] {W X Y Z : C} (a : W ⟶ X)
    (b : X ⟶ Y) (g : Y ⟶ Y) (c : Y ⟶ Z) (g' : Z ⟶ Z) (h : c ≫ g' = g ≫ c) :
    a ≫ b ≫ g ≫ c = (a ≫ b ≫ c) ≫ g' := by
  simp only [Category.assoc, h]

/-- The restriction maps of the internal Hom of Stacks 03EM are `homRestr`, by definition; stated
for a variable presheaf of rings so that it is instantiated rather than re-checked. -/
theorem internalHom_map_apply_eq_homRestr {D : Type*} [Category D] (O : Dᵒᵖ ⥤ CommRingCat)
    (F G : PresheafOfModules.{u} (Oforget O)) {T₁ T₂ : Dᵒᵖ} (f : T₁ ⟶ T₂)
    (γ : (internalHom O F G).obj T₁) :
    (internalHom O F G).map f γ = homRestr O F G f.unop γ :=
  rfl

/-- An isomorphism of bundled modules from a linear equivalence of their carriers. -/
def ModuleCat.isoMkOfLinearEquiv {R : Type*} [Ring R] {M N : ModuleCat.{u} R} (e : M ≃ₗ[R] N) :
    M ≅ N where
  hom := ModuleCat.ofHom e.toLinearMap
  inv := ModuleCat.ofHom e.symm.toLinearMap
  hom_inv_id := ModuleCat.hom_ext (LinearMap.ext e.symm_apply_apply)
  inv_hom_id := ModuleCat.hom_ext (LinearMap.ext e.apply_symm_apply)

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local irreducible] modulePullback

section HomEquiv

variable {Y : AlgebraicSpaces B S hS} (A C : Modules.{u, u} B S hS Y.1 Y.2)

/-- **Morphisms of the restrictions to the slice at a chart are morphisms of the pullbacks to the
chart**: the comparison of Stacks 04M0 (`AlgebraicGeometry.Space.chartModuleSliceEquiv`) is an
equivalence, read through the identification of the pullback of Stacks 03LU to the chart with the
restriction to the slice (`AlgebraicGeometry.Space.chartModuleRestrictionSliceIso`). -/
def chartHomEquiv (T : SmallEtale B S hS Y.1) :
    ((SheafOfModules.overFunctor (structureRingSheaf B S hS Y) T).obj A ⟶
        (SheafOfModules.overFunctor (structureRingSheaf B S hS Y) T).obj C) ≃
      ((modulePullback B S hS (chartToSpace B S hS Y T)).obj A ⟶
        (modulePullback B S hS (chartToSpace B S hS Y T)).obj C) :=
  (chartModuleSliceEquiv B S hS Y T).fullyFaithfulFunctor.homEquiv.trans
    (Iso.homCongr ((chartModuleRestrictionSliceIso B S hS Y T).app A)
      ((chartModuleRestrictionSliceIso B S hS Y T).app C)).symm

/-- `AlgebraicGeometry.Space.chartHomEquiv` sends `β` to its image under the reindexing to the
chart, conjugated by `AlgebraicGeometry.Space.chartModuleRestrictionSliceIso`. -/
theorem chartHomEquiv_apply (T : SmallEtale B S hS Y.1)
    (β : (SheafOfModules.overFunctor (structureRingSheaf B S hS Y) T).obj A ⟶
      (SheafOfModules.overFunctor (structureRingSheaf B S hS Y) T).obj C) :
    chartHomEquiv B S hS A C T β =
      ((chartModuleRestrictionSliceIso B S hS Y T).app A).hom ≫
        (chartModuleSliceReindex B S hS Y T).map β ≫
          ((chartModuleRestrictionSliceIso B S hS Y T).app C).inv :=
  rfl

/-- Restriction of a morphism of restrictions along a morphism of slices, through
`SheafOfModules.overFunctorMap`. -/
def chartSliceHomRestrict {T' T : SmallEtale B S hS Y.1} (f : T' ⟶ T)
    (β : (SheafOfModules.overFunctor (structureRingSheaf B S hS Y) T).obj A ⟶
      (SheafOfModules.overFunctor (structureRingSheaf B S hS Y) T).obj C) :
    (SheafOfModules.overFunctor (structureRingSheaf B S hS Y) T').obj A ⟶
      (SheafOfModules.overFunctor (structureRingSheaf B S hS Y) T').obj C :=
  (SheafOfModules.overFunctorMap (structureRingSheaf B S hS Y) f).inv.app A ≫
    (SheafOfModules.overMap (structureRingSheaf B S hS Y) f).map β ≫
      (SheafOfModules.overFunctorMap (structureRingSheaf B S hS Y) f).hom.app C

/-- The comparison of Stacks 03LU at a factorization `g ≫ p = v` is the inverse of the composition
comparison followed by the transport along the factorization. -/
theorem pullbackComparison_eq_symm {P T Z : AlgebraicSpaces B S hS} (g : T ⟶ P) (p : P ⟶ Z)
    (v : T ⟶ Z) (hv : g ≫ p = v) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    QuasiCoherentDescent.pullbackComparison B S hS g p v hv M =
      ((modulePullbackCompIso B S hS g p ≪≫
        eqToIso (congrArg (fun k => modulePullback B S hS k) hv)).app M).symm := by
  subst hv
  apply Iso.ext
  simp [QuasiCoherentDescent.pullbackComparison]

/-- The comparison of Stacks 03LU at the factorization `chartMap f ≫ φ_T = φ_{T'}` is the inverse
of the comparison `AlgebraicGeometry.Space.chartModuleRestrictionComp` of Stacks 03LY. -/
theorem pullbackComparison_chartMap {T' T : SmallEtale B S hS Y.1} (f : T' ⟶ T)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    QuasiCoherentDescent.pullbackComparison B S hS (chartMap B S hS Y f)
        (chartToSpace B S hS Y T) (chartToSpace B S hS Y T') (chartMap_comp_chartToSpace B S hS Y f)
        M = ((chartModuleRestrictionComp B S hS Y f).app M).symm :=
  pullbackComparison_eq_symm B S hS _ _ _ _ M

/-- **The reading of morphisms through Stacks 04M0 is natural**: restriction to a smaller slice
is the restricted reading of Stacks 03LU along the morphism of charts. -/
theorem chartHomEquiv_sliceRestrict {T' T : SmallEtale B S hS Y.1} (f : T' ⟶ T)
    (β : (SheafOfModules.overFunctor (structureRingSheaf B S hS Y) T).obj A ⟶
      (SheafOfModules.overFunctor (structureRingSheaf B S hS Y) T).obj C) :
    chartHomEquiv B S hS A C T' (chartSliceHomRestrict B S hS A C f β) =
      QuasiCoherentDescent.restrictForm B S hS (chartMap B S hS Y f) (chartToSpace B S hS Y T)
        (chartToSpace B S hS Y T') (chartMap_comp_chartToSpace B S hS Y f)
        (chartHomEquiv B S hS A C T β) := by
  have sqA := chartModuleRestrictionSliceIso_comp_unconditional B S hS Y f A
  have sqC := chartModuleRestrictionSliceIso_comp_unconditional B S hS Y f C
  have nat := chartModuleInverseImageSliceApp_naturality B S hS Y f β
  rw [QuasiCoherentDescent.restrictForm_eq, QuasiCoherentDescent.factorForm_eq,
    pullbackComparison_chartMap, pullbackComparison_chartMap, chartHomEquiv_apply,
    chartHomEquiv_apply]
  exact conj_comp_eq_of_squares ((chartModuleRestrictionComp B S hS Y f).app A)
    ((chartModuleRestrictionComp B S hS Y f).app C)
    ((chartModuleRestrictionSliceIso B S hS Y T').app A)
    ((chartModuleRestrictionSliceIso B S hS Y T').app C)
    ((chartModuleInverseImage B S hS Y f).mapIso
      ((chartModuleRestrictionSliceIso B S hS Y T).app A))
    ((chartModuleInverseImage B S hS Y f).mapIso
      ((chartModuleRestrictionSliceIso B S hS Y T).app C))
    _ _
    ((chartModuleSliceReindex B S hS Y T').mapIso
      ((SheafOfModules.overFunctorMap (structureRingSheaf B S hS Y) f).app A))
    ((chartModuleSliceReindex B S hS Y T').mapIso
      ((SheafOfModules.overFunctorMap (structureRingSheaf B S hS Y) f).app C))
    _ _ sqA sqC nat
    (((chartModuleSliceReindex B S hS Y T').map_comp _ _).trans
      (congrArg (_ ≫ ·) ((chartModuleSliceReindex B S hS Y T').map_comp _ _)))
    (((chartModuleInverseImage B S hS Y f).map_comp _ _).trans
      (congrArg (_ ≫ ·) ((chartModuleInverseImage B S hS Y f).map_comp _ _)))

/-- Restriction of morphisms of restrictions along a morphism of slices is the restriction map
of the internal Hom of Stacks 03EM. -/
theorem chartSliceHomRestrict_val {T' T : SmallEtale B S hS Y.1} (f : T' ⟶ T)
    (β : (SheafOfModules.overFunctor (structureRingSheaf B S hS Y) T).obj A ⟶
      (SheafOfModules.overFunctor (structureRingSheaf B S hS Y) T).obj C) :
    (chartSliceHomRestrict B S hS A C f β).val =
      homRestr (smallEtaleStructurePresheaf B S hS Y.1 Y.2) A.val C.val f β.val := by
  ext U x
  rfl

/-- **A function on a chart as a global function on the chart space**: `r ∈ 𝒪_Y(T)` restricted
to every étale chart of `T`, through the comparison of Stacks 04M0. -/
def chartRingMap (T : SmallEtale B S hS Y.1) :
    (structureRingSheaf B S hS Y).obj.obj (op T) →+*
      globalFunctions' B S hS (chartSpace B S hS Y T).1 where
  toFun r := ⟨fun T'' => fRestr (smallEtaleStructurePresheaf B S hS Y.1 Y.2) T r
      (op ((SmallEtale.chartLocalization B S hS Y.1 T).obj T''.unop)), fun {T₁ T₂} g => by
    change ((structureRingSheaf B S hS Y).obj.map
        ((SmallEtale.chartLocalization B S hS Y.1 T).map g.unop).left.op).hom
        (((structureRingSheaf B S hS Y).obj.map
          ((SmallEtale.chartLocalization B S hS Y.1 T).obj T₁.unop).hom.op).hom r) =
      ((structureRingSheaf B S hS Y).obj.map
        ((SmallEtale.chartLocalization B S hS Y.1 T).obj T₂.unop).hom.op).hom r
    rw [← RingCat.comp_apply, ← Functor.map_comp, ← op_comp, Over.w]⟩
  map_one' := by ext T''; exact map_one _
  map_mul' a b := by ext T''; exact map_mul _ a b
  map_zero' := by ext T''; exact map_zero _
  map_add' a b := by ext T''; exact map_add _ a b

/-- **The reading of morphisms through Stacks 04M0 is linear.** -/
theorem chartHomEquiv_smul (T : SmallEtale B S hS Y.1)
    (r : (structureRingSheaf B S hS Y).obj.obj (op T))
    (β : (SheafOfModules.overFunctor (structureRingSheaf B S hS Y) T).obj A ⟶
      (SheafOfModules.overFunctor (structureRingSheaf B S hS Y) T).obj C) :
    chartHomEquiv B S hS A C T
        (β ≫ ⟨multEndoHom (smallEtaleStructurePresheaf B S hS Y.1 Y.2) C.val T r⟩) =
      chartHomEquiv B S hS A C T β ≫ globalFunctionsSmul B S hS (chartRingMap B S hS T r)
        ((modulePullback B S hS (chartToSpace B S hS Y T)).obj C) := by
  ext U x
  exact map_smul (((chartModuleRestrictionSliceIso B S hS Y T).app C).inv.val.app U).hom
    (globalFunctionsAt B S hS (chartRingMap B S hS T r) U)
    (((chartModuleSliceReindex B S hS Y T).map β).val.app U
      ((((chartModuleRestrictionSliceIso B S hS Y T).app A).hom.val.app U) x))

/-- **The reading of morphisms through Stacks 04M0 is additive.** -/
theorem chartHomEquiv_add (T : SmallEtale B S hS Y.1)
    (β β' : (SheafOfModules.overFunctor (structureRingSheaf B S hS Y) T).obj A ⟶
      (SheafOfModules.overFunctor (structureRingSheaf B S hS Y) T).obj C) :
    chartHomEquiv B S hS A C T (β + β') =
      chartHomEquiv B S hS A C T β + chartHomEquiv B S hS A C T β' := by
  ext U x
  exact map_add (((chartModuleRestrictionSliceIso B S hS Y T).app C).inv.val.app U).hom _ _

/-- The inverse of the reading of morphisms through Stacks 04M0 is additive. -/
theorem chartHomEquiv_symm_add (T : SmallEtale B S hS Y.1)
    (ψ ψ' : (modulePullback B S hS (chartToSpace B S hS Y T)).obj A ⟶
      (modulePullback B S hS (chartToSpace B S hS Y T)).obj C) :
    (chartHomEquiv B S hS A C T).symm (ψ + ψ') =
      (chartHomEquiv B S hS A C T).symm ψ + (chartHomEquiv B S hS A C T).symm ψ' := by
  rw [Equiv.symm_apply_eq, chartHomEquiv_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The inverse of the reading of morphisms through Stacks 04M0 sends multiplication by the global
function `chartRingMap r` to multiplication by `r`. -/
theorem chartHomEquiv_symm_comp_smul (T : SmallEtale B S hS Y.1)
    (r : (structureRingSheaf B S hS Y).obj.obj (op T))
    (ψ : (modulePullback B S hS (chartToSpace B S hS Y T)).obj A ⟶
      (modulePullback B S hS (chartToSpace B S hS Y T)).obj C) :
    (chartHomEquiv B S hS A C T).symm (ψ ≫ globalFunctionsSmul B S hS (chartRingMap B S hS T r)
        ((modulePullback B S hS (chartToSpace B S hS Y T)).obj C)) =
      (chartHomEquiv B S hS A C T).symm ψ ≫
        (⟨multEndoHom (smallEtaleStructurePresheaf B S hS Y.1 Y.2) C.val T r⟩ :
          (SheafOfModules.overFunctor (structureRingSheaf B S hS Y) T).obj C ⟶
            (SheafOfModules.overFunctor (structureRingSheaf B S hS Y) T).obj C) := by
  rw [Equiv.symm_apply_eq, chartHomEquiv_smul, Equiv.apply_symm_apply]

/-- The inverse of the reading of morphisms through Stacks 04M0 sends the restricted reading of
Stacks 03LU along a morphism of charts to restriction to the smaller slice. -/
theorem chartHomEquiv_symm_restrictForm {T' T : SmallEtale B S hS Y.1} (f : T' ⟶ T)
    (ψ : (modulePullback B S hS (chartToSpace B S hS Y T)).obj A ⟶
      (modulePullback B S hS (chartToSpace B S hS Y T)).obj C) :
    (chartHomEquiv B S hS A C T').symm
        (QuasiCoherentDescent.restrictForm B S hS (chartMap B S hS Y f) (chartToSpace B S hS Y T)
          (chartToSpace B S hS Y T') (chartMap_comp_chartToSpace B S hS Y f) ψ) =
      chartSliceHomRestrict B S hS A C f ((chartHomEquiv B S hS A C T).symm ψ) := by
  rw [Equiv.symm_apply_eq, chartHomEquiv_sliceRestrict, Equiv.apply_symm_apply]

end HomEquiv

section Reading

variable {Y : AlgebraicSpaces B S hS} (A C : Modules.{u, u} B S hS Y.1 Y.2)
  (F : SheafOfModules.{u + 1} (structureRingSheaf B S hS Y))
  (e : ∀ T : SmallEtale B S hS Y.1, F.val.obj (op T) ≃+
    ((modulePullback B S hS (chartToSpace B S hS Y T)).obj A ⟶
      (modulePullback B S hS (chartToSpace B S hS Y T)).obj C))
  (hnat : ∀ {T' T : SmallEtale B S hS Y.1} (f : T' ⟶ T) (s : F.val.obj (op T)),
    e T' (F.val.map f.op s) =
      QuasiCoherentDescent.restrictForm B S hS (chartMap B S hS Y f) (chartToSpace B S hS Y T)
        (chartToSpace B S hS Y T') (chartMap_comp_chartToSpace B S hS Y f) (e T s))
  (hlin : ∀ (T : SmallEtale B S hS Y.1) (r : (structureRingSheaf B S hS Y).obj.obj (op T))
    (s : F.val.obj (op T)),
    e T (r • s) = e T s ≫ globalFunctionsSmul B S hS (chartRingMap B S hS T r)
      ((modulePullback B S hS (chartToSpace B S hS Y T)).obj C))

/-- The internal Hom `𝓗om_{𝒪_Y}(A, C)` of Stacks 03EM on the small étale site of `Y`, read as a
sheaf of `𝒪_Y`-modules indexed by `AlgebraicGeometry.Space.structureRingSheaf`. -/
def chartInternalHom : SheafOfModules.{u + 1} (structureRingSheaf B S hS Y) where
  val := internalHom (smallEtaleStructurePresheaf B S hS Y.1 Y.2) A.val C.val
  isSheaf := (RingedSite.internalHomSheaf (smallEtaleRingedSite B S hS Y.1 Y.2) A C).isSheaf

/-- `AlgebraicGeometry.Space.chartInternalHom` is the internal Hom of the small étale ringed
site. -/
def chartInternalHomIso :
    chartInternalHom B S hS A C ≅
      RingedSite.internalHomSheaf (smallEtaleRingedSite B S hS Y.1 Y.2) A C :=
  Iso.refl _

include hlin in
/-- The sections of `F` over a chart, as sections of the internal Hom, linearly. -/
def chartReadingLinearEquiv (T : SmallEtale B S hS Y.1) :
    F.val.obj (op T) ≃ₗ[(structureRingSheaf B S hS Y).obj.obj (op T)]
      (chartInternalHom B S hS A C).val.obj (op T) where
  toFun s := ((chartHomEquiv B S hS A C T).symm (e T s)).val
  invFun γ := (e T).symm (chartHomEquiv B S hS A C T ⟨γ⟩)
  left_inv s := by
    change (e T).symm (chartHomEquiv B S hS A C T ((chartHomEquiv B S hS A C T).symm (e T s))) = s
    rw [Equiv.apply_symm_apply, AddEquiv.symm_apply_apply]
  right_inv γ := by
    change ((chartHomEquiv B S hS A C T).symm (e T ((e T).symm
      (chartHomEquiv B S hS A C T ⟨γ⟩)))).val = γ
    rw [AddEquiv.apply_symm_apply, Equiv.symm_apply_apply]
  map_add' s t := by
    change ((chartHomEquiv B S hS A C T).symm (e T (s + t))).val =
      ((chartHomEquiv B S hS A C T).symm (e T s)).val +
        ((chartHomEquiv B S hS A C T).symm (e T t)).val
    rw [map_add, chartHomEquiv_symm_add]
    rfl
  map_smul' r s := by
    change ((chartHomEquiv B S hS A C T).symm (e T (r • s))).val =
      ((chartHomEquiv B S hS A C T).symm (e T s)).val ≫
        multEndoHom (smallEtaleStructurePresheaf B S hS Y.1 Y.2) C.val T r
    rw [hlin, chartHomEquiv_symm_comp_smul]
    rfl

/-- The restriction maps of the internal Hom are the restrictions of Stacks 03EM. -/
theorem chartInternalHom_map_apply {T₁ T₂ : (SmallEtale B S hS Y.1)ᵒᵖ} (f : T₁ ⟶ T₂)
    (γ : (chartInternalHom B S hS A C).val.obj T₁) :
    (chartInternalHom B S hS A C).val.map f γ =
      homRestr (smallEtaleStructurePresheaf B S hS Y.1 Y.2) A.val C.val f.unop γ :=
  internalHom_map_apply_eq_homRestr _ A.val C.val f γ

include hnat in
/-- `AlgebraicGeometry.Space.chartReadingLinearEquiv` commutes with the restriction maps of `F`
and of the internal Hom. -/
theorem chartReadingLinearEquiv_naturality {T₁ T₂ : (SmallEtale B S hS Y.1)ᵒᵖ} (f : T₁ ⟶ T₂)
    (s : F.val.obj T₁) :
    chartReadingLinearEquiv B S hS A C F e hlin T₂.unop (F.val.map f s) =
      (chartInternalHom B S hS A C).val.map f
        (chartReadingLinearEquiv B S hS A C F e hlin T₁.unop s) := by
  rw [chartInternalHom_map_apply]
  exact (congrArg (fun t => ((chartHomEquiv B S hS A C T₂.unop).symm t).val)
    (hnat f.unop s)).trans (by rw [chartHomEquiv_symm_restrictForm, chartSliceHomRestrict_val]; rfl)

include hnat hlin in
/-- **A sheaf of `𝒪_Y`-modules read chartwise as morphisms of the pullbacks of `A` and `C`,
naturally for the restricted readings of Stacks 03LU and linearly, is the internal Hom
`𝓗om_{𝒪_Y}(A, C)` of Stacks 03EM.** -/
def chartReadingIso : F ≅ chartInternalHom B S hS A C :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun T => ModuleCat.isoMkOfLinearEquiv (chartReadingLinearEquiv B S hS A C F e hlin T.unop))
      (fun _ _ f => ModuleCat.hom_ext (LinearMap.ext fun s =>
        chartReadingLinearEquiv_naturality B S hS A C F e hnat hlin f s)))

end Reading

/-- **Stacks 03M1 (6), read chartwise.**  A sheaf of `𝒪_Y`-modules whose sections over every
étale chart are identified, additively, naturally for the restricted readings of Stacks 03LU and
linearly, with the morphisms of the pullbacks to the chart of an `𝒪_Y`-module `A` of finite
presentation and of a quasi-coherent `𝒪_Y`-module `C`, is quasi-coherent. -/
theorem isQuasicoherentOnSite_of_chartReading {Y : AlgebraicSpaces B S hS}
    (A C : Modules.{u, u} B S hS Y.1 Y.2) (hA : A.IsQuasicoherentOnSite)
    (hfp : A.IsFinitePresentationOnSite) (hC : C.IsQuasicoherentOnSite)
    (F : SheafOfModules.{u + 1} (structureRingSheaf B S hS Y))
    (e : ∀ T : SmallEtale B S hS Y.1, F.val.obj (op T) ≃+
      ((modulePullback B S hS (chartToSpace B S hS Y T)).obj A ⟶
        (modulePullback B S hS (chartToSpace B S hS Y T)).obj C))
    (hnat : ∀ {T' T : SmallEtale B S hS Y.1} (f : T' ⟶ T) (s : F.val.obj (op T)),
      e T' (F.val.map f.op s) =
        QuasiCoherentDescent.restrictForm B S hS (chartMap B S hS Y f) (chartToSpace B S hS Y T)
          (chartToSpace B S hS Y T') (chartMap_comp_chartToSpace B S hS Y f) (e T s))
    (hlin : ∀ (T : SmallEtale B S hS Y.1) (r : (structureRingSheaf B S hS Y).obj.obj (op T))
      (s : F.val.obj (op T)),
      e T (r • s) = e T s ≫ globalFunctionsSmul B S hS (chartRingMap B S hS T r)
        ((modulePullback B S hS (chartToSpace B S hS Y T)).obj C)) :
    F.IsQuasicoherentOnSite := by
  let := smallEtaleRingedSite_essentiallySmall B S hS Y.1 Y.2
  have h₁ := isQuasicoherentOnSite_internalHomSheafSmall B S hS Y.1 Y.2 A C hA hC hfp
  have h₂ := SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'.{u + 1, u, u, u, u + 1} h₁
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((RingedSite.internalHomSheafSmallIso (smallEtaleRingedSite B S hS Y.1 Y.2) A C) ≪≫
      (chartInternalHomIso B S hS A C).symm ≪≫ (chartReadingIso B S hS A C F e hnat hlin).symm) h₂

section Iso

variable {P Q Z : AlgebraicSpaces B S hS}

/-- **The inverse image along an isomorphism of algebraic spaces is an equivalence**, with the
inverse image along the inverse as inverse (Stacks 03LU). -/
def modulePullbackEquivalenceOfInv (c : P ⟶ Q) (d : Q ⟶ P) (hcd : c ≫ d = 𝟙 P)
    (hdc : d ≫ c = 𝟙 Q) : Modules.{u, u} B S hS Q.1 Q.2 ≌ Modules.{u, u} B S hS P.1 P.2 :=
  CategoryTheory.Equivalence.mk (modulePullback B S hS c) (modulePullback B S hS d)
    ((modulePullbackIdIso B S hS Q).symm ≪≫
      eqToIso (congrArg (fun k => modulePullback B S hS k) hdc.symm) ≪≫
        (modulePullbackCompIso B S hS d c).symm)
    (modulePullbackCompIso B S hS c d ≪≫
      eqToIso (congrArg (fun k => modulePullback B S hS k) hcd) ≪≫ modulePullbackIdIso B S hS P)

/-- **The restricted reading of Stacks 03LU along an isomorphism is bijective.** -/
theorem restrictForm_bijective_of_inv (c : P ⟶ Q) (d : Q ⟶ P) (hcd : c ≫ d = 𝟙 P)
    (hdc : d ≫ c = 𝟙 Q) (k : Q ⟶ Z) (r : P ⟶ Z) (hr : c ≫ k = r)
    (M N : Modules.{u, u} B S hS Z.1 Z.2) :
    Function.Bijective (QuasiCoherentDescent.restrictForm B S hS c k r hr (M := M) (N := N)) := by
  have hmap : Function.Bijective (fun w : (modulePullback B S hS k).obj M ⟶
      (modulePullback B S hS k).obj N => (modulePullback B S hS c).map w) :=
    (modulePullbackEquivalenceOfInv B S hS c d hcd hdc).fullyFaithfulFunctor.map_bijective _ _
  have hfac : Function.Bijective (QuasiCoherentDescent.factorForm B S hS c k r hr (M := M)
      (N := N)) :=
    ⟨QuasiCoherentDescent.factorForm_injective B S hS c k r hr,
      fun v => QuasiCoherentDescent.exists_factorForm_eq B S hS c k r hr v⟩
  exact hfac.comp hmap

/-- The restricted reading depends on the restricting morphism only through its value. -/
theorem restrictForm_congr_left {k : Q ⟶ Z} {p p' : P ⟶ Q} (hp : p = p') (r : P ⟶ Z)
    (hr : p ≫ k = r) (hr' : p' ≫ k = r) {M N : Modules.{u, u} B S hS Z.1 Z.2}
    (w : (modulePullback B S hS k).obj M ⟶ (modulePullback B S hS k).obj N) :
    QuasiCoherentDescent.restrictForm B S hS p k r hr w =
      QuasiCoherentDescent.restrictForm B S hS p' k r hr' w := by
  subst hp
  rfl

/-- **The restricted reading of Stacks 03LU is additive.** -/
theorem restrictForm_add (p : P ⟶ Q) (k : Q ⟶ Z) (r : P ⟶ Z) (hr : p ≫ k = r)
    {M N : Modules.{u, u} B S hS Z.1 Z.2}
    (w w' : (modulePullback B S hS k).obj M ⟶ (modulePullback B S hS k).obj N) :
    QuasiCoherentDescent.restrictForm B S hS p k r hr (w + w') =
      QuasiCoherentDescent.restrictForm B S hS p k r hr w +
        QuasiCoherentDescent.restrictForm B S hS p k r hr w' := by
  have : (modulePullback B S hS p).Additive :=
    Adjunction.left_adjoint_additive (modulePullbackAdjunction B S hS p)
  rw [QuasiCoherentDescent.restrictForm_eq, QuasiCoherentDescent.restrictForm_eq,
    QuasiCoherentDescent.restrictForm_eq, QuasiCoherentDescent.factorForm_eq,
    QuasiCoherentDescent.factorForm_eq, QuasiCoherentDescent.factorForm_eq, Functor.map_add,
    Preadditive.add_comp, Preadditive.comp_add]

end Iso

section Composite

variable {Y X : AlgebraicSpaces B S hS}

/-- The reading of Stacks 03LU at the factorization `φ_T ≫ j`, as an additive equivalence. -/
def factorFormAddEquiv (T : SmallEtale B S hS Y.1) (j : Y ⟶ X)
    (A C : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePullback B S hS (chartToSpace B S hS Y T)).obj ((modulePullback B S hS j).obj A) ⟶
      (modulePullback B S hS (chartToSpace B S hS Y T)).obj ((modulePullback B S hS j).obj C)) ≃+
    ((modulePullback B S hS (chartToSpace B S hS Y T ≫ j)).obj A ⟶
      (modulePullback B S hS (chartToSpace B S hS Y T ≫ j)).obj C) where
  toFun := QuasiCoherentDescent.factorForm B S hS _ j _ rfl
  invFun v := (QuasiCoherentDescent.pullbackComparison B S hS _ j _ rfl A).inv ≫ v ≫
    (QuasiCoherentDescent.pullbackComparison B S hS _ j _ rfl C).hom
  left_inv u := by
    simp only [QuasiCoherentDescent.factorForm, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  right_inv v := by
    simp only [QuasiCoherentDescent.factorForm, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id]
  map_add' u u' := by
    simp only [QuasiCoherentDescent.factorForm, Preadditive.add_comp, Preadditive.comp_add]

/-- The reading of Stacks 03LU commutes with multiplication by a global function. -/
theorem factorForm_comp_globalFunctionsSmul {P Q Z : AlgebraicSpaces B S hS} (p : P ⟶ Q) (k : Q ⟶ Z)
    (r : P ⟶ Z) (hr : p ≫ k = r) {M N : Modules.{u, u} B S hS Z.1 Z.2}
    (w : (modulePullback B S hS p).obj ((modulePullback B S hS k).obj M) ⟶
      (modulePullback B S hS p).obj ((modulePullback B S hS k).obj N))
    (t : globalFunctions' B S hS P.1) :
    QuasiCoherentDescent.factorForm B S hS p k r hr
        (w ≫ globalFunctionsSmul B S hS t _) =
      QuasiCoherentDescent.factorForm B S hS p k r hr w ≫
        globalFunctionsSmul B S hS t ((modulePullback B S hS r).obj N) := by
  simp only [QuasiCoherentDescent.factorForm, Category.assoc, comp_globalFunctionsSmul,
    comp_globalFunctionsSmul_assoc]

/-- **Stacks 03M1 (6), read chartwise through an étale morphism.** The variant of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_chartReading` in which the sections over a
chart `T` of `Y` are read as morphisms of the pullbacks along `φ_T ≫ j` of modules `A`, `C` on
`X`, for an étale `j : Y ⟶ X`. -/
theorem isQuasicoherentOnSite_of_chartReading_comp (j : Y ⟶ X) (A C : Modules.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherentOnSite) (hfp : A.IsFinitePresentationOnSite)
    (hC : C.IsQuasicoherentOnSite)
    (F : SheafOfModules.{u + 1} (structureRingSheaf B S hS Y))
    (e : ∀ T : SmallEtale B S hS Y.1, F.val.obj (op T) ≃+
      ((modulePullback B S hS (chartToSpace B S hS Y T ≫ j)).obj A ⟶
        (modulePullback B S hS (chartToSpace B S hS Y T ≫ j)).obj C))
    (hnat : ∀ {T' T : SmallEtale B S hS Y.1} (f : T' ⟶ T) (s : F.val.obj (op T)),
      e T' (F.val.map f.op s) =
        QuasiCoherentDescent.restrictForm B S hS (chartMap B S hS Y f)
          (chartToSpace B S hS Y T ≫ j) (chartToSpace B S hS Y T' ≫ j)
          (by rw [← Category.assoc, chartMap_comp_chartToSpace]) (e T s))
    (hlin : ∀ (T : SmallEtale B S hS Y.1) (r : (structureRingSheaf B S hS Y).obj.obj (op T))
      (s : F.val.obj (op T)),
      e T (r • s) = e T s ≫ globalFunctionsSmul B S hS (chartRingMap B S hS T r)
        ((modulePullback B S hS (chartToSpace B S hS Y T ≫ j)).obj C)) :
    F.IsQuasicoherentOnSite := by
  refine isQuasicoherentOnSite_of_chartReading B S hS ((modulePullback B S hS j).obj A)
    ((modulePullback B S hS j).obj C)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS j A hA)
    (isFinitePresentationOnSite_modulePullback B S hS j A hfp)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS j C hC) F
    (fun T => (e T).trans (factorFormAddEquiv B S hS T j A C).symm) (fun {T' T} f s => ?_)
    (fun T r s => ?_)
  · apply (factorFormAddEquiv B S hS T' j A C).injective
    show QuasiCoherentDescent.factorForm B S hS _ j _ rfl
        ((factorFormAddEquiv B S hS T' j A C).symm (e T' (F.val.map f.op s))) =
      QuasiCoherentDescent.factorForm B S hS _ j _ rfl
        (QuasiCoherentDescent.restrictForm B S hS (chartMap B S hS Y f) (chartToSpace B S hS Y T)
          (chartToSpace B S hS Y T') (chartMap_comp_chartToSpace B S hS Y f)
          ((factorFormAddEquiv B S hS T j A C).symm (e T s)))
    rw [← QuasiCoherentDescent.restrictForm_factorForm B S hS (chartMap B S hS Y f)
      (chartToSpace B S hS Y T) j _ rfl (chartToSpace B S hS Y T')
      (chartMap_comp_chartToSpace B S hS Y f)
      _ (by rw [← Category.assoc, chartMap_comp_chartToSpace]) rfl]
    exact ((factorFormAddEquiv B S hS T' j A C).apply_symm_apply _).trans
      ((hnat f s).trans (congrArg _ ((factorFormAddEquiv B S hS T j A C).apply_symm_apply _).symm))
  · apply (factorFormAddEquiv B S hS T j A C).injective
    refine ((factorFormAddEquiv B S hS T j A C).apply_symm_apply _).trans ((hlin T r s).trans ?_)
    refine (congrArg (· ≫ globalFunctionsSmul B S hS (chartRingMap B S hS T r) _)
      ((factorFormAddEquiv B S hS T j A C).apply_symm_apply (e T s)).symm).trans ?_
    exact (factorForm_comp_globalFunctionsSmul B S hS _ j _ rfl _ _).symm

end Composite

end AlgebraicGeometry.Space
