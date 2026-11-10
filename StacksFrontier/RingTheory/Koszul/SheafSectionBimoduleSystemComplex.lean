module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticMilnorGlobalSections
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroDerivedStructure
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphism
public import StacksFrontier.RingTheory.Koszul.PowBaseDegreeZeroTowerPlain
public import StacksFrontier.RingTheory.Koszul.SheafSectionBimoduleSystem

/- Keep the admissible-sequence convention previously supplied by the global instance. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

/-!
# The tower of Tag 0GZJ attached to a module over the Koszul sheaf, and `R Γ = 0`

Let `R` be a commutative ring, `f₁, …, f_r ∈ R`, `t ≥ 1`, and let `ℬ` be the sheaf of differential
graded algebras `(K_{n+1})_n` on the chaotic site `Stacks.LiftedNat` of the proof of
Proposition 0GZK. A right differential graded `ℬ`-module `𝓜` gives the inverse system of bimodules
`Koszul.liftedPowSectionBimoduleSystem f ht 𝓜`, whose `n`-th term is the module of sections of `𝓜`
over the stage `t - 1 + n`, and with it the right-hand tower `n ↦ 𝓜(t - 1 + n) ⊗_R^𝐋 K_t` of
Tag 0GZJ. This file proves that **if `R Γ(𝓜) = 0`, that tower has derived limit zero**: this is
the step `0 = R lim M_n ⇒ 0 = R lim (M_n ⊗_R^𝐋 K_t)` of the proof of Proposition 0GZK.

The tower `n ↦ 𝓜(t - 1 + n)` of `D(R)` read in the differential graded encoding
`D(degreeZero R R, d)` of `D(R)` has derived limit zero: through the comparison equivalence of
Tag 09SC its terms are the complexes of sections of `𝓜` over the stages, with the restriction maps
as transitions, and that inverse system has derived limit `R Γ(𝓜)`
(`Stacks.ChaoticSite.isDerivedLimit_derivedGlobalSections`), the stages `t - 1 + n` being cofinal.
The step from `n ↦ 𝓜(t - 1 + n)` to `n ↦ 𝓜(t - 1 + n) ⊗_R^𝐋 K_t` is
`Koszul.isZero_of_isDerivedLimit_powBaseDegreeZeroDerivedTensorTower`.

## Main results

* `InverseSequence.proIsoShift`: an inverse system indexed by `ℕ` is pro-isomorphic to its shift
  `n ↦ X_{n + c}`.
* `Stacks.ChaoticSite.isDerivedLimit_derivedGlobalSections`: **`R Γ(𝓜)` is a derived limit of the
  tower of complexes of sections of `𝓜`**, for every right differential graded `ℬ`-module `𝓜`.
* `Koszul.liftedPowSectionComplexIso`: the complex of `R`-modules of homogeneous components of the
  `n`-th bimodule of the system is the complex of sections of `𝓜` over the stage `t - 1 + n`.
* `Koszul.isZero_of_isDerivedLimit_powBaseDegreeZeroDerivedTensorTower_liftedPowSection`: **if
  `R Γ(𝓜) = 0`, the tower `n ↦ 𝓜(t - 1 + n) ⊗_R^𝐋 K_t` has derived limit zero.**

## References

* [Stacks Project, Tag 0GZK](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ)
* [Stacks Project, Tag 0H9L](https://stacks.math.columbia.edu/tag/0H9L) for the derived limits of
  pro-isomorphic inverse systems.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
  Stacks.PresheafOfModules

universe u

/-! ### Cofinal shifts of an inverse system -/

namespace InverseSequence

variable {D : Type*} [Category D]

/-- The shift `n ↦ c + n` of the indices, as a functor of `ℕ`. -/
def addFunctor (c : ℕ) : ℕ ⥤ ℕ := Monotone.functor fun _ _ h => Nat.add_le_add_left h c

/-- The functor `addFunctor c` sends `n` to `c + n`. -/
@[simp] theorem addFunctor_obj (c n : ℕ) : (addFunctor c).obj n = c + n := rfl

/-- **An inverse system is pro-isomorphic to its shift** `n ↦ X_{c + n}`: the forward maps are
identities and the backward maps are the transition maps `X_{c + m} ⟶ X_m`. -/
def proIsoShift (X : ℕᵒᵖ ⥤ D) (c : ℕ) : ProIso X ((addFunctor c).op ⋙ X) where
  α m := c + m
  β m := m
  αmono _ _ h := Nat.add_le_add_left h c
  βmono _ _ h := h
  αle m := Nat.le_add_left m c
  βle m := le_rfl
  φ m := 𝟙 _
  ψ m := tr X (Nat.le_add_left m c)
  φnat h := (Category.comp_id _).trans (Category.id_comp _).symm
  ψnat h := by
    change tr X (Nat.add_le_add_left h c) ≫ tr X (Nat.le_add_left _ c) =
      tr X (Nat.le_add_left _ c) ≫ tr X h
    rw [ProIso.tr_trans, ProIso.tr_trans]
  ψφ m := Category.id_comp _
  φψ m := Category.comp_id _

end InverseSequence

namespace CategoryTheory.Pretriangulated

variable {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A cofinal shift of an inverse system with zero derived limit has invertible difference
map.** -/
theorem isIso_familyDifference_shift_of_isDerivedLimit {F : ℕᵒᵖ ⥤ D}
    [HasProductsOfShape ℕ D] {K : D} (hK : IsDerivedLimit F K) (hz : IsZero K) (c : ℕ) :
    IsIso (familyDifference (fun n : ℕ => F.obj ⟨c + n⟩)
      fun n => F.map (homOfLE (Nat.add_le_add_left (Nat.le_succ n) c)).op) := by
  obtain ⟨K', hK'⟩ := exists_isDerivedLimit ((InverseSequence.addFunctor c).op ⋙ F)
  obtain ⟨e⟩ := Rlim.Pro.nonempty_iso_of_isDerivedLimit_of_pro_isomorphism F _ K K' hK hK'
    (InverseSequence.proIsoShift F c)
  exact hK'.isIso_difference_of_isZero (hz.of_iso e.symm)

end CategoryTheory.Pretriangulated

/-! ### The derived global sections as a derived limit, for every module -/

namespace Stacks.ChaoticSite

open _root_.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule

attribute [local instance 10000] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]
  (ℬ : DifferentialGradedAlgebra.{u, u} (constRingSheaf (C := LiftedNat.{u}) R))

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective in
/-- **The derived global sections of a module are a derived limit of its tower of sections**: for
every right differential graded `ℬ`-module `M`, `R Γ(M)` is the derived limit in `D(R)` of the
tower `n ↦ M(n)` of complexes of sections of `M` over the stages. The case of a graded injective
K-injective module is `Stacks.ChaoticSite.isDerivedLimit_derivedGlobalSections_of_isDGInjective`;
a graded injective K-injective resolution `M ⟶ I` induces quasi-isomorphisms on the sections over
every stage, hence an isomorphism of the two towers in `D(R)`, and an isomorphism
`R Γ(M) ≅ R Γ(I)`. -/
theorem isDerivedLimit_derivedGlobalSections (M : DifferentialGradedModule.{u, u, u} ℬ) :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} R)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    IsDerivedLimit (sectionsTower R M.complex ⋙ DerivedCategory.Q)
      ((derivedGlobalSections R ℬ).obj ((toDerivedCategory.{u, u, u} ℬ).obj
        ((DifferentialGradedModule.HomotopyCategory.quotient ℬ).obj M))) := by
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} R)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  obtain ⟨I, f, hf, hG, hK⟩ : ∃ (I : DifferentialGradedModule.{u, u, u} ℬ) (f : M ⟶ I),
      QuasiIso f.toHomologicalComplex ∧ GradedInjective I ∧ IsKInjective I :=
    hasKInjectiveResolutions_dg.{u, u, u} (X := constRingedSite LiftedNat.{u} R) ℬ M
  have hI : IsDGInjective I := ⟨hG, hK⟩
  have := hf
  let q := DifferentialGradedModule.HomotopyCategory.quotient ℬ
  have hs : IsIso ((toDerivedCategory.{u, u, u} ℬ).map (q.map f)) :=
    Localization.inverts _ (quasiIsomorphisms.{u, u, u} ℬ) (q.map f)
      ((quasiIsomorphisms_quotient_map_iff f).2 hf)
  let eK : (derivedGlobalSections R ℬ).obj ((toDerivedCategory.{u, u, u} ℬ).obj (q.obj I)) ≅
      (derivedGlobalSections R ℬ).obj ((toDerivedCategory.{u, u, u} ℬ).obj (q.obj M)) :=
    ((derivedGlobalSections R ℬ).mapIso
      (asIso ((toDerivedCategory.{u, u, u} ℬ).map (q.map f)))).symm
  have hT : ∀ n : ℕ, IsIso ((Functor.whiskerRight (sectionsTowerMap R f.toHomologicalComplex)
      DerivedCategory.Q).app (op n)) := fun n => by
    have := quasiIso_sectionsTowerMap_app R f.toHomologicalComplex n
    change IsIso (DerivedCategory.Q.map ((sectionsTowerMap R f.toHomologicalComplex).app (op n)))
    infer_instance
  have : IsIso (Functor.whiskerRight (sectionsTowerMap R f.toHomologicalComplex)
      DerivedCategory.Q) := NatIso.isIso_of_isIso_app _
  exact (isDerivedLimit_of_iso eK
    (isDerivedLimit_derivedGlobalSections_of_isDGInjective R ℬ hI)).of_iso
    (asIso (Functor.whiskerRight (sectionsTowerMap R f.toHomologicalComplex)
      DerivedCategory.Q)).symm

end Stacks.ChaoticSite

/-! ### The components of the bimodules of the system are the complexes of sections -/

namespace Koszul

open DifferentialGraded DifferentialGradedAlgebra DifferentialGradedModule
  Stacks.ChaoticSite

attribute [local instance] SheafOfModules.GradedAlgebra.sectionsGOne
  SheafOfModules.GradedAlgebra.sectionsGMul SheafOfModules.GradedAlgebra.sectionsGRing
  Stacks.uliftIntAlgebra

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) {t : ℕ} (ht : 1 ≤ t)
  (𝓜 : SheafOfModules.DifferentialGradedModule.{u, u, u} (liftedPowSheafAlgebra.{u} f))

/-- The algebra map of `R` into the Koszul algebra at the stage carrying `K_{t+n}`, read in the
sections of `ℬ`, is the scalar `r · 1`. -/
theorem liftedPowSectionAlgebraHom_algebraMap (n : ℕ) (c : R) :
    (liftedPowSectionAlgebraHom f ht n).toAlgebraHom (algebraMap R (powAlgebra f (t + n)).A c) =
      DirectSum.of ((liftedPowSheafAlgebra f).toGradedAlgebra.sectionsPiece (liftedPowStage t n)) 0
        (c • (liftedPowSheafAlgebra f).one.eval (liftedPowStage t n)) := by
  let A := liftedPowDiagram.{u} f
  let U := liftedPowStage.{u} t n
  have h1 : (liftedPowSectionAlgebraHom f ht n).toAlgebraHom
      (algebraMap R (powAlgebra f (t + n)).A c) =
      (sectionRingEquiv A U).symm (algebraMap R (A.obj U).A c) := by
    change (sectionRingEquiv A U).symm
      ((liftedPowStageAlgebraHom f ht n).toAlgebraHom (algebraMap R _ c)) = _
    rw [AlgHom.commutes]
  rw [h1]
  apply (sectionRingEquiv A U).injective
  rw [RingEquiv.apply_symm_apply]
  have h2 : sectionRingEquiv A U (DirectSum.of ((systemAlgebra A).toGradedAlgebra.sectionsPiece U) 0
      (c • (liftedPowSheafAlgebra f).one.eval U)) =
      sectionRingHom A U (DirectSum.of ((systemAlgebra A).toGradedAlgebra.sectionsPiece U) 0
        (c • (liftedPowSheafAlgebra f).one.eval U)) := rfl
  refine Eq.trans ?_ (h2.trans (sectionRingHom_of A U 0 _)).symm
  exact Algebra.algebraMap_eq_smul_one c

/-- **The scalars of `R` act on the sections of `𝓜` over a stage through `K_{t+n}` as they do on
the sheaf of modules.** -/
theorem liftedPowSectionModule_smul_of (n : ℕ) (k : ℤ)
    (x : (𝓜.complex.X k).val.obj (liftedPowStage t n)) (c : R) :
    c • @id (liftedPowSectionModule f ht 𝓜 n).M
        (DirectSum.of (𝓜.sectionsPiece (liftedPowStage t n)) k x) =
      @id (liftedPowSectionModule f ht 𝓜 n).M
        (DirectSum.of (𝓜.sectionsPiece (liftedPowStage t n)) k (c • x)) := by
  change 𝓜.act (liftedPowStage t n) (DirectSum.of _ k x)
      ((liftedPowSectionAlgebraHom f ht n).toAlgebraHom
        (algebraMap R (powAlgebra f (t + n)).A c)) = _
  rw [liftedPowSectionAlgebraHom_algebraMap, SheafOfModules.DifferentialGradedModule.act_of,
    SheafOfModules.DifferentialGradedModule.actOn_of]
  change DirectSum.of (𝓜.sectionsPiece (liftedPowStage t n)) (k + 0)
      ((𝓜.mul k 0).app (liftedPowStage t n) x
        (c • (liftedPowSheafAlgebra f).one.eval (liftedPowStage t n))) =
    DirectSum.of (𝓜.sectionsPiece (liftedPowStage t n)) k (c • x)
  have hm : (𝓜.mul k 0).app (liftedPowStage t n) x
      (c • (liftedPowSheafAlgebra f).one.eval (liftedPowStage t n)) =
      c • (𝓜.mul k 0).app (liftedPowStage t n) x
        ((liftedPowSheafAlgebra f).one.eval (liftedPowStage t n)) :=
    (𝓜.mul k 0).map_smul_right (liftedPowStage t n) c x _
  have hs : ∀ (j : ℤ) (y : (𝓜.complex.X j).val.obj (liftedPowStage t n)),
      DirectSum.of (𝓜.sectionsPiece (liftedPowStage t n)) j (c • y) =
        c • DirectSum.of (𝓜.sectionsPiece (liftedPowStage t n)) j y := fun j y =>
    (DirectSum.lof _ ℤ (𝓜.sectionsPiece (liftedPowStage t n)) j).map_smul c y
  rw [hm, hs, SheafOfModules.of_heq (add_zero k) (𝓜.mul_one k (liftedPowStage t n) x)]
  exact (hs k x).symm

/-- The complex of `R`-modules of homogeneous components of the `n`-th bimodule of the system,
read over `R` placed in degree zero. -/
abbrev liftedPowSectionComponents (n : ℕ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  degreeZeroComplex (R := R) (S := R) (A := R) (toBaseModule (liftedPowSectionModule f ht 𝓜 n))

/-- The sections of the degree-`k` piece of `𝓜` over the stage carrying `K_{t+n}` are the
degree-`k` component of the `n`-th bimodule of the system, as `R`-modules. -/
def liftedPowSectionPieceEquiv (n : ℕ) (k : ℤ) :
    ((sectionsTower R 𝓜.complex).obj (op (t - 1 + n))).X k ≃ₗ[R]
      (liftedPowSectionComponents f ht 𝓜 n).X k where
  __ := Stacks.ExternalGrading.intSummandEquiv (𝓜.sectionsPiece (liftedPowStage t n)) k
  map_smul' c x := Subtype.ext (liftedPowSectionModule_smul_of f ht 𝓜 n k x c).symm

/-- **The complex of sections of `𝓜` over the stage `t - 1 + n` is the complex of homogeneous
components of the `n`-th bimodule of the system.** -/
def liftedPowSectionComplexIso (n : ℕ) :
    (sectionsTower R 𝓜.complex).obj (op (t - 1 + n)) ≅ liftedPowSectionComponents f ht 𝓜 n :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k => (liftedPowSectionPieceEquiv f ht 𝓜 n k).toModuleIso)
    (by
      rintro i j (rfl : i + 1 = j)
      ext x
      apply Subtype.ext
      change (((liftedPowSectionComponents f ht 𝓜 n).d i (i + 1)).hom _ :
          (toBaseModule (liftedPowSectionModule f ht 𝓜 n)).grading (i + 1)).val = _
      rw [degreeZeroComplex_d_val (A := R) _ rfl]
      change (𝓜.sectionModule (liftedPowStage t n)).d
          (DirectSum.of (𝓜.sectionsPiece (liftedPowStage t n)) i x) =
        DirectSum.of (𝓜.sectionsPiece (liftedPowStage t n)) (i + 1)
          ((𝓜.complex.d i (i + 1)).val.app (liftedPowStage t n) x)
      exact SheafOfModules.DifferentialGradedModule.sectionModule_d_of 𝓜 _ i x)

/-- The transition homomorphism of the system of bimodules, read as a homomorphism of right
differential graded modules over `R` placed in degree zero: restriction of sections from the stage
of `K_{t+n+1}` to the stage of `K_{t+n}`. -/
def liftedPowSectionBaseTrans (n : ℕ) :
    toBaseModule (liftedPowSectionModule f ht 𝓜 (n + 1)) ⟶
      toBaseModule (liftedPowSectionModule f ht 𝓜 n) :=
  ((liftedPowSectionBimoduleSystem f ht 𝓜).trans (Nat.le_succ n)).rightHom

/-- **The identification of the complexes of sections with the complexes of components commutes
with the transitions**: restriction of sections from the stage of `K_{t+n+1}` to the stage of
`K_{t+n}` is the transition homomorphism of the system of bimodules. -/
theorem liftedPowSectionComplexIso_naturality (n : ℕ) :
    (liftedPowSectionComplexIso f ht 𝓜 (n + 1)).hom ≫
      degreeZeroComplexMap (A := R) (liftedPowSectionBaseTrans f ht 𝓜 n) =
    (sectionsTower R 𝓜.complex).map (homOfLE (Nat.add_le_add_left (Nat.le_succ n) (t - 1))).op ≫
      (liftedPowSectionComplexIso f ht 𝓜 n).hom := by
  ext k x
  apply Subtype.ext
  change 𝓜.sectionRestrictAdd (liftedPowStageMap t (Nat.le_succ n))
      (DirectSum.of (𝓜.sectionsPiece (liftedPowStage t (n + 1))) k x) =
    DirectSum.of (𝓜.sectionsPiece (liftedPowStage t n)) k
      ((𝓜.complex.X k).val.map (Stacks.LiftedNat.ofNat.op.map
        (homOfLE (Nat.add_le_add_left (Nat.le_succ n) (t - 1))).op) x)
  exact (SheafOfModules.DifferentialGradedModule.sectionRestrictAdd_of 𝓜 _ k x).trans rfl

/-! ### The tower `n ↦ 𝓜(t - 1 + n)` in the differential graded encoding of `D(R)` -/

/-- A rearrangement of composites: if `c ≫ a' = a ≫ q` and `m₁ ≫ b = q ≫ m₂`, then
`a ≫ m₁ ≫ b = c ≫ a' ≫ m₂`. -/
theorem _root_.CategoryTheory.comp_comp_eq_comp_comp_of_eq {D : Type*} [Category D]
    {W X Y Z V T : D} (a : W ⟶ X) (m₁ : X ⟶ Y) (b : Y ⟶ Z) (c : W ⟶ V) (a' : V ⟶ T)
    (q : X ⟶ T) (m₂ : T ⟶ Z) (h1 : c ≫ a' = a ≫ q) (h3 : m₁ ≫ b = q ≫ m₂) :
    a ≫ m₁ ≫ b = c ≫ a' ≫ m₂ := by
  rw [h3, ← Category.assoc, ← h1, Category.assoc]

section Derived

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The `n`-th bimodule of the system, read in `D(R)`, is the complex of sections of `𝓜` over
the stage `t - 1 + n`**: the comparison equivalence `D(degreeZero R R, d) ≌ D(R)` of Tag 09SC
carries the class of a differential graded module to the class of its complex of components, and
that complex is the complex of sections. -/
def liftedPowSectionDerivedIso (n : ℕ) :
    (degreeZeroDerivedEquivalence (R := R) (S := R) (A := R)).functor.obj
        ((quasiIsomorphisms' (degreeZero R R)).Q.obj ((toHomotopyCategory (degreeZero R R)).obj
          (toBaseModule (liftedPowSectionModule f ht 𝓜 n)))) ≅
      DerivedCategory.Q.obj ((sectionsTower R 𝓜.complex).obj (op (t - 1 + n))) :=
  degreeZeroDerivedComponentIso.app (toBaseModule (liftedPowSectionModule f ht 𝓜 n)) ≪≫
    DerivedCategory.Q.mapIso (liftedPowSectionComplexIso f ht 𝓜 n).symm

/-- The identifications `Koszul.liftedPowSectionDerivedIso` commute with the transitions. -/
theorem liftedPowSectionDerivedIso_naturality (n : ℕ) :
    (liftedPowSectionDerivedIso f ht 𝓜 (n + 1)).hom ≫
      DerivedCategory.Q.map ((sectionsTower R 𝓜.complex).map
        (homOfLE (Nat.add_le_add_left (Nat.le_succ n) (t - 1))).op) =
    (degreeZeroDerivedEquivalence (R := R) (S := R) (A := R)).functor.map
        ((quasiIsomorphisms' (degreeZero R R)).Q.map ((toHomotopyCategory (degreeZero R R)).map
          (liftedPowSectionBaseTrans f ht 𝓜 n))) ≫
      (liftedPowSectionDerivedIso f ht 𝓜 n).hom := by
  have h1 := (degreeZeroDerivedComponentIso (R := R) (S := R) (A := R)).hom.naturality
    (liftedPowSectionBaseTrans f ht 𝓜 n)
  have h2 : (liftedPowSectionComplexIso f ht 𝓜 (n + 1)).inv ≫
      (sectionsTower R 𝓜.complex).map (homOfLE (Nat.add_le_add_left (Nat.le_succ n) (t - 1))).op =
      degreeZeroComplexMap (A := R) (liftedPowSectionBaseTrans f ht 𝓜 n) ≫
        (liftedPowSectionComplexIso f ht 𝓜 n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, liftedPowSectionComplexIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  simp only [liftedPowSectionDerivedIso, Iso.trans_hom, Iso.app_hom, Category.assoc]
  have h3 : DerivedCategory.Q.map (liftedPowSectionComplexIso f ht 𝓜 (n + 1)).inv ≫
      DerivedCategory.Q.map ((sectionsTower R 𝓜.complex).map
        (homOfLE (Nat.add_le_add_left (Nat.le_succ n) (t - 1))).op) =
      DerivedCategory.Q.map (degreeZeroComplexMap (A := R) (liftedPowSectionBaseTrans f ht 𝓜 n)) ≫
        DerivedCategory.Q.map (liftedPowSectionComplexIso f ht 𝓜 n).inv := by
    rw [← Functor.map_comp, h2, Functor.map_comp]
  exact CategoryTheory.comp_comp_eq_comp_comp_of_eq _ _ _ _ _ _ _ h1 h3

/-- **If `R Γ(𝓜) = 0`, the tower `n ↦ 𝓜(t - 1 + n)` of `D(degreeZero R R, d)` has invertible
difference map**, that is, derived limit zero. -/
theorem isIso_familyDifference_liftedPowSection
    (hΓ : IsZero ((derivedGlobalSections R (liftedPowSheafAlgebra f)).obj
      ((SheafOfModules.DifferentialGradedModule.toDerivedCategory.{u, u, u} _).obj
        ((SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient _).obj 𝓜)))) :
    IsIso (familyDifference
      (fun n => (quasiIsomorphisms' (degreeZero R R)).Q.obj
        ((toHomotopyCategory (degreeZero R R)).obj
          (toBaseModule (liftedPowSectionModule f ht 𝓜 n))))
      fun n => (quasiIsomorphisms' (degreeZero R R)).Q.map
        ((toHomotopyCategory (degreeZero R R)).map
          (liftedPowSectionBaseTrans f ht 𝓜 n))) := by
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} R)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  let E := (degreeZeroDerivedEquivalence (R := R) (S := R) (A := R)).functor
  let G : ℕ → derivedCategory' (degreeZero R R) := fun n =>
    (quasiIsomorphisms' (degreeZero R R)).Q.obj ((toHomotopyCategory (degreeZero R R)).obj
      (toBaseModule (liftedPowSectionModule f ht 𝓜 n)))
  let T : ∀ n, G (n + 1) ⟶ G n := fun n => (quasiIsomorphisms' (degreeZero R R)).Q.map
    ((toHomotopyCategory (degreeZero R R)).map (liftedPowSectionBaseTrans f ht 𝓜 n))
  have h1 := isIso_familyDifference_shift_of_isDerivedLimit
    (Stacks.ChaoticSite.isDerivedLimit_derivedGlobalSections R (liftedPowSheafAlgebra f) 𝓜) hΓ
    (t - 1)
  have h2 : IsIso (familyDifference (fun n => E.obj (G n)) fun n => E.map (T n)) :=
    isIso_familyDifference_of_iso (liftedPowSectionDerivedIso f ht 𝓜)
      (liftedPowSectionDerivedIso_naturality f ht 𝓜) h1
  have hpc := map_familyDifference_piComparison E G T
  have : IsIso (E.map (familyDifference G T)) := by
    rw [← Category.comp_id (E.map _), ← IsIso.hom_inv_id (piComparison E _), ← Category.assoc, hpc,
      Category.assoc]
    infer_instance
  exact isIso_of_reflects_iso _ E

/-- **If `R Γ(𝓜) = 0`, the tower `n ↦ 𝓜(t - 1 + n) ⊗_R^𝐋 K_t` of Tag 0GZJ has derived limit
zero.** This is the step `0 = R lim M_n ⇒ 0 = R lim (M_n ⊗_R^𝐋 K_t)` of the proof of
Proposition 0GZK, for an arbitrary right differential graded module `𝓜` over `ℬ` representing
`(M_n)`. -/
theorem isZero_of_isDerivedLimit_powBaseDegreeZeroDerivedTensorTower_liftedPowSection
    (hΓ : IsZero ((derivedGlobalSections R (liftedPowSheafAlgebra f)).obj
      ((SheafOfModules.DifferentialGradedModule.toDerivedCategory.{u, u, u} _).obj
        ((SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient _).obj 𝓜))))
    [HasProduct fun n : ℕ => (powBaseDegreeZeroDerivedTensorTower f t ht
      (liftedPowSectionBimoduleSystem f ht 𝓜).toBimoduleSystem.obj
      (fun n => (liftedPowSectionBimoduleSystem f ht 𝓜).trans (Nat.le_succ n))).tower.obj (op n)]
    (K' : derivedCategory' (degreeZero R R))
    (hK' : IsDerivedLimit (powBaseDegreeZeroDerivedTensorTower f t ht
      (liftedPowSectionBimoduleSystem f ht 𝓜).toBimoduleSystem.obj
      (fun n => (liftedPowSectionBimoduleSystem f ht 𝓜).trans (Nat.le_succ n))).tower K') :
    IsZero K' :=
  isZero_of_isDerivedLimit_powBaseDegreeZeroDerivedTensorTower f t ht
    (liftedPowSectionBimoduleSystem f ht 𝓜).toBimoduleSystem.obj
    (fun n => (liftedPowSectionBimoduleSystem f ht 𝓜).trans (Nat.le_succ n))
    (isIso_familyDifference_liftedPowSection f ht 𝓜 hΓ) hK'

end Derived

end Koszul

end
