module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectBounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperDimOneGlobalSectionsPerfect

/-!
# The amplitude of `RΓ` on a scheme of dimension at most one over an algebraically closed field

Let `Y` be a separated scheme of finite type and of dimension at most one over an algebraically
closed field and `Λ` a finite ring. For every sheaf `G` of `Λ`-modules on `Y_étale` the cohomology
`H^q(Y, G)` vanishes for `q > 2` ([Stacks, Tag 0A53]), so `RΓ(Y, C)` lies in degrees `≤ b + 2` for
every complex `C` concentrated in degrees `≤ b`, bounded below.

## Main results

* `StacksDraft.Perfect.isLE_rightDerivedFunctorPlus_of_bounded` — for an additive functor whose
  right derived functor carries objects placed in degree `0` into degrees `≤ d`, the right derived
  functor carries a bounded complex concentrated in degrees `≤ b` into degrees `≤ b + d`.
* `StacksDraft.Perfect.isGE_rightDerivedFunctorPlus_of_isStrictlyGE` — a right derived functor
  carries a complex concentrated in degrees `≥ a` into degrees `≥ a`.
* `Stacks.SheafTwist.isLE_etaleModuleDerivedGlobalSections_single_of_dimLEOne` — `RΓ(Y, G)` lies in
  degrees `≤ 2` for a sheaf `G`.
* `Stacks.SheafTwist.isLE_etaleModuleDerivedGlobalSections_of_dimLEOne` — `RΓ(Y, C)` lies in
  degrees `≤ b + 2` for a complex `C` concentrated in degrees `[a, b]`.

## References

* [Stacks Project, Tag 0A53](https://stacks.math.columbia.edu/tag/0A53)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace StacksDraft.Perfect

attribute [local instance] HasDerivedCategory.standard
  Functor.commShiftRightDerivedFunctorPlus Functor.isTriangulated_rightDerivedFunctorPlus

variable {A B : Type*} [Category* A] [Abelian A] [EnoughInjectives A] [Category* B] [Abelian B]
  (F : A ⥤ B) [F.Additive] (d : ℤ)
  (hgood : ∀ G : A, (DerivedCategory.Plus.ι.obj
    (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj G))).IsLE d)

include hgood in
/-- `RF(G[i])` lies in degrees `≤ i + d`. -/
lemma isLE_rightDerivedFunctorPlus_singleFunctor (G : A) (i : ℤ) :
    (DerivedCategory.Plus.ι.obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A i).obj G))).IsLE
        (i + d) := by
  let e₁ : (DerivedCategory.Plus.singleFunctor A i).obj G ≅
      ((DerivedCategory.Plus.singleFunctor A 0).obj G)⟦-i⟧ :=
    (((DerivedCategory.Plus.singleFunctors A).shiftIso (-i) i 0 (by omega)).app G).symm
  have := hgood G
  have : ((DerivedCategory.Plus.ι ⋙ shiftFunctor (DerivedCategory B) (-i)).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj G))).IsLE
        (i + d) := DerivedCategory.TStructure.t.isLE_shift (DerivedCategory.Plus.ι.obj
          (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj G))) d (-i)
          (i + d)
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((DerivedCategory.Plus.ι.mapIso (F.rightDerivedFunctorPlus.mapIso e₁ ≪≫
      (F.rightDerivedFunctorPlus.commShiftIso (-i)).app _) ≪≫
      (DerivedCategory.Plus.ι.commShiftIso (-i)).app _).symm) _

include hgood in
/-- `RF(C)` lies in degrees `≤ a + d` for a complex `C` concentrated in the single degree `a`. -/
lemma isLE_rightDerivedFunctorPlus_of_single (C : CochainComplex A ℤ)
    (hC : CochainComplex.plus A C) (a : ℤ) (hz : ∀ i, i ≠ a → IsZero (C.X i)) :
    (DerivedCategory.Plus.ι.obj
      (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj (Functor.plusObj C hC)))).IsLE
        (a + d) :=
  have := isLE_rightDerivedFunctorPlus_singleFunctor F d hgood (C.X a) a
  DerivedCategory.TStructure.t.isLE_of_iso (DerivedCategory.Plus.ι.mapIso
    (F.rightDerivedFunctorPlus.mapIso
      (DerivedCategory.Plus.Qh.mapIso (Functor.isoSingleFunctorObjPlus C hC a hz) ≪≫
        ((Functor.singleFunctorPlusIsoCompQh a).app (C.X a)).symm))).symm _

include hgood in
/-- `RF(C)` lies in degrees `≤ a + m + d` for a bounded below complex `C` concentrated in degrees
`[a, a + m]`. -/
lemma isLE_rightDerivedFunctorPlus_of_bounded_aux (m : ℕ) :
    ∀ (C : CochainComplex A ℤ) (a : ℤ) (hC : CochainComplex.plus A C),
      (∀ i, i < a ∨ a + m < i → IsZero (C.X i)) →
      (DerivedCategory.Plus.ι.obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj (Functor.plusObj C hC)))).IsLE
          (a + m + d) := by
  induction m with
  | zero =>
    intro C a hC hz
    simpa using isLE_rightDerivedFunctorPlus_of_single F d hgood C hC a
      (fun i hi => hz i (by omega))
  | succ m ih =>
    intro C a hC hz
    let T := (DerivedCategory.Plus.ι.mapTriangle.obj (F.rightDerivedFunctorPlus.mapTriangle.obj
      (DerivedCategory.Plus.Qh.mapTriangle.obj (Functor.stupidTruncTrianglehPlus C a hC))))
    have hT : T ∈ distTriang _ := DerivedCategory.Plus.ι.map_distinguished _
      (F.rightDerivedFunctorPlus.map_distinguished _
        (DerivedCategory.Plus.Qh.map_distinguished _
          (Functor.stupidTruncTrianglehPlus_distinguished C a hC)))
    have h₁ : T.obj₁.IsLE (a + (m + 1 : ℕ) + d) := by
      have : T.obj₁.IsLE (a + 1 + m + d) := ih _ (a + 1) _ (fun i hi => by
        rcases hi with hi | hi
        · exact Functor.isZero_stupidTruncGE_X_of_lt C (a + 1) i hi
        · exact Functor.isZero_stupidTrunc_X_of_isZero C _ i (hz i (by omega)))
      exact DerivedCategory.TStructure.t.isLE_of_le _ (a + 1 + m + d) _ (by push_cast; omega)
    have h₃ : T.obj₃.IsLE (a + (m + 1 : ℕ) + d) := by
      have : T.obj₃.IsLE (a + d) := isLE_rightDerivedFunctorPlus_of_single F d hgood _ _ a
        (fun i hi => by
          rcases lt_or_gt_of_ne hi with hi | hi
          · exact Functor.isZero_stupidTrunc_X_of_isZero C _ i (hz i (by omega))
          · exact Functor.isZero_stupidTruncLE_X_of_lt C a i hi)
      exact DerivedCategory.TStructure.t.isLE_of_le _ (a + d) _ (by push_cast; omega)
    exact DerivedCategory.TStructure.t.isLE₂ T hT _ h₁ h₃

include hgood in
/-- **The amplitude of a right derived functor on a bounded complex.** If `RF` carries every
object placed in degree `0` into degrees `≤ d`, then it carries a complex concentrated in degrees
`[a, b]` into degrees `≤ b + d`. -/
theorem isLE_rightDerivedFunctorPlus_of_bounded (C : CochainComplex A ℤ) (a b : ℤ)
    [C.IsStrictlyGE a] [C.IsStrictlyLE b] :
    (DerivedCategory.Plus.ι.obj (F.rightDerivedFunctorPlus.obj
      (DerivedCategory.Plus.Qh.obj (Functor.plusObj C ⟨a, inferInstance⟩)))).IsLE (b + d) := by
  have := isLE_rightDerivedFunctorPlus_of_bounded_aux F d hgood (b - min a b).toNat C (min a b)
    ⟨a, inferInstance⟩ (fun i hi => hi.elim (fun hi => C.isZero_of_isStrictlyGE a i (by omega))
      (fun hi => C.isZero_of_isStrictlyLE b i (by omega)))
  rwa [show min a b + ((b - min a b).toNat : ℤ) = b by omega] at this

end StacksDraft.Perfect

namespace Stacks.SheafTwist

attribute [local instance] HasDerivedCategory.standard

variable {Λ : Type r} [Ring Λ] [Finite Λ] {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {Y : Scheme.{u}}
  (f : Y ⟶ Spec (.of Ω)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (hdim : topologicalKrullDim Y ≤ 1)

include f hdim in
/-- **`RΓ(Y, G)` lies in degrees `≤ 2`** for a sheaf `G` of modules over a finite ring on a
separated scheme of finite type of dimension at most one over an algebraically closed field
([Stacks, Tag 0A53]). -/
theorem isLE_etaleModuleDerivedGlobalSections_single_of_dimLEOne
    (G : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) :
    (DerivedCategory.Plus.ι.obj
      ((Stacks.EtaleCohomology.etaleModuleDerivedGlobalSections.{u, r} Λ Y).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G))).IsLE 2 := by
  have := Stacks.EtaleCohomology.etaleModules_enoughInjectives.{u, r} Λ Y
  obtain ⟨Ires, -, hge⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE 0
    ((CochainComplex.singleFunctor (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) 0).obj G)
  let I := Ires.cocomplex
  have : I.IsStrictlyGE 0 := hge
  let M' := ((moduleSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have hvan : ∀ n : ℕ, 2 ≤ n → Subsingleton (M'.homology ((n : ℤ) + 1)) := by
    intro n hn
    obtain ⟨φ, hφ⟩ :=
      Stacks.EtaleResolution.exists_injective_homology_sections.{max (u + 1) r, u, r}
      Λ Y G I Ires.ι n
    let e := homologyGlobalSectionsForgetIso (Λ := Λ) I ((n : ℤ) + 1)
    have := subsingleton_ext_sheafForget_of_dimLEOne f hdim G (n + 1) (by omega)
    have := hφ.subsingleton
    exact e.addCommGroupIsoToAddEquiv.toEquiv.symm.subsingleton
  have hM : (DerivedCategory.Q.obj M').IsLE 2 := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
    have := hvan n (by omega)
    exact (ModuleCat.isZero_iff_subsingleton.2 this).of_iso
      ((DerivedCategory.homologyFunctorFactors _ _).app M')
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (Functor.rightDerivedFunctorPlusInjectiveResolutionIso
      (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, r} Λ Y) G Ires ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
        (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology _
          (Stacks.EtaleCohomology.etaleMkIdIsTerminal Y)) (ComplexShape.up ℤ)).app I)).symm 2

include f hdim in
/-- **`RΓ(Y, C)` lies in degrees `≤ b + 2`** for a complex `C` concentrated in degrees `[a, b]`,
on a separated scheme of finite type of dimension at most one over an algebraically closed field,
with coefficients in a finite ring. -/
theorem isLE_etaleModuleDerivedGlobalSections_of_dimLEOne
    (C : CochainComplex (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) ℤ) (a b : ℤ)
    [C.IsStrictlyGE a] [C.IsStrictlyLE b] :
    (DerivedCategory.Plus.ι.obj
      ((Stacks.EtaleCohomology.etaleModuleDerivedGlobalSections.{u, r} Λ Y).obj
        (DerivedCategory.Plus.Q.obj ⟨C, ⟨a, inferInstance⟩⟩))).IsLE (b + 2) := by
  have := Stacks.EtaleCohomology.etaleModules_enoughInjectives.{u, r} Λ Y
  have : (DerivedCategory.Plus.ι.obj
      ((Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, r} Λ Y).rightDerivedFunctorPlus.obj
        ((HomotopyCategory.Plus.quotient _ ⋙ DerivedCategory.Plus.Qh).obj
          ⟨C, ⟨a, inferInstance⟩⟩))).IsLE (b + 2) :=
    StacksDraft.Perfect.isLE_rightDerivedFunctorPlus_of_bounded
      (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, r} Λ Y) 2
      (isLE_etaleModuleDerivedGlobalSections_single_of_dimLEOne f hdim) C a b
  exact DerivedCategory.TStructure.t.isLE_of_iso (DerivedCategory.Plus.ι.mapIso
    ((Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, r} Λ Y).rightDerivedFunctorPlus.mapIso
      ((DerivedCategory.Plus.quotientCompQhIso _).app ⟨C, ⟨a, inferInstance⟩⟩))) (b + 2)

end Stacks.SheafTwist

namespace StacksDraft.Perfect

attribute [local instance] HasDerivedCategory.standard

/-- **A right derived functor preserves lower bounds**: for a complex `C` concentrated in degrees
`≥ a`, `RF(C)` lies in degrees `≥ a`. -/
theorem isGE_rightDerivedFunctorPlus_of_isStrictlyGE {A B : Type*} [Category* A] [Abelian A]
    [EnoughInjectives A] [Category* B] [Abelian B] (F : A ⥤ B) [F.Additive]
    (C : CochainComplex A ℤ) (a : ℤ) [C.IsStrictlyGE a] :
    (DerivedCategory.Plus.ι.obj (F.rightDerivedFunctorPlus.obj
      (DerivedCategory.Plus.Q.obj ⟨C, ⟨a, inferInstance⟩⟩))).IsGE a := by
  obtain ⟨R, -, hge⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a C
  have := R.injective
  have := R.quasiIso
  let φ : (⟨C, ⟨a, inferInstance⟩⟩ : CochainComplex.Plus A) ⟶ ⟨R.cocomplex, R.boundedBelow⟩ :=
    ObjectProperty.homMk R.ι
  have : IsIso (DerivedCategory.Plus.Q.map φ) := by
    have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map φ)) := by
      show IsIso (DerivedCategory.Q.map ((CochainComplex.Plus.ι _).map φ))
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 R.quasiIso
    exact isIso_of_reflects_iso _ DerivedCategory.Plus.ι
  have : IsIso (F.mapHomologicalComplexDerivedUnit R.boundedBelow) :=
    inferInstanceAs (IsIso ((F.mapHomologicalComplexQhIso R.boundedBelow).inv ≫
      DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient _).obj ⟨R.cocomplex, R.boundedBelow⟩))))
  have : CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      R.cocomplex) a := (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi =>
    F.map_isZero (R.cocomplex.isZero_of_isStrictlyGE a i hi)
  have : (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      R.cocomplex)).IsGE a := (DerivedCategory.isGE_Q_obj_iff _ _).2 inferInstance
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((asIso (F.mapHomologicalComplexDerivedUnit R.boundedBelow)) ≪≫
      (DerivedCategory.Plus.ι.mapIso (F.rightDerivedFunctorPlus.mapIso
        ((DerivedCategory.Plus.quotientCompQhIso _).app _ ≪≫
          (asIso (DerivedCategory.Plus.Q.map φ)).symm)))) a

end StacksDraft.Perfect

end
