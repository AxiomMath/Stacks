module

public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import StacksFrontier.Homology.Perfect.Duality
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.BLinear
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DerivedCoextensionIsDualizing
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.HomothetyOverRing
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift

/-!
# The derived homothety of a derived coextension of scalars, without a dualizing hypothesis

Let `f : A →+* B` be a homomorphism of commutative rings with `A` Noetherian, let `M` be an
object of `D(A)` and let `RHom_A(B, M)` be its derived coextension of scalars, an object of
`D(B)`. The derived homothety `B ⟶ RHom_B(RHom_A(B, M), RHom_A(B, M))` is invertible, and remains
so after any shift, as soon as two things hold:

* `M` is represented by a bounded-below complex of injective `A`-modules;
* the canonical biduality morphism with respect to `M` is invertible at `B[0]`.

For `M = A[0]` the second hypothesis holds when `B[0]` is perfect over `A`.

## Main results

* `Dualizing.exists_injectiveRepresentative`: an object of the derived category of an abelian
  category with enough injectives that is cohomologically bounded below is represented by a
  bounded-below complex of injectives.
* `Dualizing.quasiIso_homothety_shift`: the scalar homothety of the shift of a complex is a
  quasi-isomorphism if that of the complex is.
* `Dualizing.isIso_bidualityMor_of_iso_dualizing`: invertibility of the canonical biduality
  morphism depends on the dualizing object only through its isomorphism class.
* `Dualizing.isIso_derivedHomothety_overRing_of_injectiveRepresentative`: the derived homothety
  of `derivedHomAdjunctionOverRing` at `ω` is invertible as soon as the scalar homothety of one
  bounded-below injective representative of `ω` is a quasi-isomorphism.
* `Dualizing.nonempty_endLinearEquiv_derivedHom_of_isIso_bidualityMor`: under the two hypotheses
  above, the endomorphisms of `RHom_A(B, M)` in `D(B)` are `B`-linearly isomorphic to `B`.
* `Dualizing.subsingleton_hom_derivedHom_shift_of_isIso_bidualityMor`: under the two hypotheses
  above, there is at most one morphism `RHom_A(B, M) ⟶ RHom_A(B, M)[n]` for `n ≠ 0`.
* `Dualizing.isIso_derivedHomothety_overRing_derivedHom_shift`: under the two hypotheses above,
  the derived homothety at any shift of `RHom_A(B, M)` is invertible.
* `Dualizing.isIso_dualizingBidualityMor_derivedTensorUnit_of_isPerfect`: biduality with respect
  to the derived tensor unit over `A` is invertible at a perfect object.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0AX0](https://stacks.math.columbia.edu/tag/0AX0)
* [Stacks Project, Tag 07VI](https://stacks.math.columbia.edu/tag/07VI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Dualizing

/-! ### A bounded-below injective representative -/

/-- An object of the derived category of an abelian category with enough injectives which is
cohomologically concentrated in degrees `≥ n` is isomorphic to the image of a complex of injective
objects that is strictly concentrated in degrees `≥ n`. -/
theorem exists_injectiveRepresentative {C : Type*} [Category C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory.{w} C] (X : DerivedCategory C) (n : ℤ) [X.IsGE n] :
    ∃ I : CochainComplex C ℤ, I.IsStrictlyGE n ∧ (∀ i : ℤ, Injective (I.X i)) ∧
      Nonempty (X ≅ DerivedCategory.Q.obj I) := by
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE X n
  obtain ⟨M, hM, i, hi⟩ :=
    CochainComplex.Plus.exists_quasiIso_injective (C := C) ⟨L, ⟨n, inferInstance⟩⟩ n
  have hiso : IsIso (DerivedCategory.Q.map i.hom) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ i.hom).2 hi
  refine ⟨((InjectiveObject.ι C).mapHomologicalComplex (ComplexShape.up ℤ)).obj M.obj,
    ?_, fun j => (M.obj.X j).2, ⟨e ≪≫ @asIso _ _ _ _ _ hiso⟩⟩
  infer_instance

end Dualizing

namespace Dualizing

/-! ### The scalar homothety under a shift -/

/-- If the scalar homothety of a complex `I` of `R`-modules is a quasi-isomorphism, then so is the
scalar homothety of its shift `I⟦n⟧`. -/
theorem quasiIso_homothety_shift {R : Type u} [CommRing R]
    (I : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) (hI : QuasiIso (homothety I)) :
    QuasiIso (homothety (I⟦n⟧)) := by
  let e := endomorphismComplexShiftIso I n
  have hcomm : homothety I ≫ e.hom = homothety (I⟦n⟧) := by
    refine HomologicalComplex.hom_ext _ _ fun j => ?_
    by_cases hj : j = 0
    · subst j
      rw [HomologicalComplex.comp_f]
      ext a
      change ULift.{v} R at a
      show (e.hom.f 0).hom (ULift.up
        (a.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I))) =
        ULift.up (a.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 (I⟦n⟧)))
      exact congrArg ULift.up ((homComplexSelfShiftIso I n).2 a.down)
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
        (AddCommGrpCat.of (ULift.{v} R)) j hj).eq_of_src _ _
  rw [← hcomm]
  infer_instance

/-! ### Biduality and an isomorphism of the dualizing object -/

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]

private theorem bidualityMor_comp_hom_map (d : DerivedHomAdjunction R)
    {ω ω' : DerivedCategory (ModuleCat.{v} R)} (i : ω ≅ ω')
    (K : DerivedCategory (ModuleCat.{v} R)) :
    bidualityMor d ω K ≫
        d.hom.map ((show d.hom.obj (Opposite.op K, ω') ⟶ d.hom.obj (Opposite.op K, ω) from
            d.hom.map ((𝟙 (Opposite.op K), i.inv) :
              (Opposite.op K, ω') ⟶ (Opposite.op K, ω))).op, i.hom) =
      bidualityMor d ω' K := by
  set D := d.hom.obj (Opposite.op K, ω)
  set D' := d.hom.obj (Opposite.op K, ω')
  set dinv : D' ⟶ D := d.hom.map ((𝟙 (Opposite.op K), i.inv) :
    (Opposite.op K, ω') ⟶ (Opposite.op K, ω)) with hdinv
  set dhom : D ⟶ D' := d.hom.map ((𝟙 (Opposite.op K), i.hom) :
    (Opposite.op K, ω) ⟶ (Opposite.op K, ω')) with hdhom
  apply (d.homEquiv K D' ω').injective
  have hsplit : d.hom.map ((dinv.op, i.hom) :
        (Opposite.op D, ω) ⟶ (Opposite.op D', ω')) =
      d.hom.map ((dinv.op, 𝟙 ω) : (Opposite.op D, ω) ⟶ (Opposite.op D', ω)) ≫
        d.hom.map ((𝟙 (Opposite.op D'), i.hom) :
          (Opposite.op D', ω) ⟶ (Opposite.op D', ω')) := by
    rw [← d.hom.map_comp]
    congr 1
    exact Prod.ext (by simp) (by simp)
  rw [hsplit, ← Category.assoc, d.homEquiv_naturality_right i.hom,
    d.homEquiv_dinaturality dinv (bidualityMor d ω K)]
  have hb : d.homEquiv K D ω (bidualityMor d ω K) =
      (d.tensorSwap K D).hom ≫ d.evaluation K ω := by
    rw [bidualityMor, AddEquiv.apply_symm_apply]
  have hb' : d.homEquiv K D' ω' (bidualityMor d ω' K) =
      (d.tensorSwap K D').hom ≫ d.evaluation K ω' := by
    rw [bidualityMor, AddEquiv.apply_symm_apply]
  have hcancel : dinv ≫ dhom = 𝟙 D' := by
    rw [hdinv, hdhom, ← d.hom.map_comp,
      show ((𝟙 (Opposite.op K), i.inv) : (Opposite.op K, ω') ⟶ (Opposite.op K, ω)) ≫
          ((𝟙 (Opposite.op K), i.hom) : (Opposite.op K, ω) ⟶ (Opposite.op K, ω')) =
          𝟙 (Opposite.op K, ω') from Prod.ext (by simp) (by simp)]
    exact d.hom.map_id _
  have heval : d.evaluation K ω ≫ i.hom =
      d.tensor.map ((dhom, 𝟙 K) : (D, K) ⟶ (D', K)) ≫ d.evaluation K ω' :=
    (d.evaluation_naturality_right i.hom).symm
  rw [hb, hb']
  simp only [Category.assoc]
  rw [d.tensorSwap_naturality_assoc (𝟙 K) dinv, heval, d.tensor_map_comp_assoc, hcancel,
    Category.id_comp, d.tensor_map_id, Category.id_comp]


/-- Invertibility of the canonical biduality morphism depends on the dualizing object only
through its isomorphism class. -/
theorem isIso_bidualityMor_of_iso_dualizing (d : DerivedHomAdjunction R)
    {ω ω' : DerivedCategory (ModuleCat.{v} R)} (i : ω ≅ ω')
    (K : DerivedCategory (ModuleCat.{v} R)) (h : IsIso (bidualityMor d ω K)) :
    IsIso (bidualityMor d ω' K) := by
  set D := d.hom.obj (Opposite.op K, ω)
  set D' := d.hom.obj (Opposite.op K, ω')
  set dinv : D' ⟶ D := d.hom.map ((𝟙 (Opposite.op K), i.inv) :
    (Opposite.op K, ω') ⟶ (Opposite.op K, ω)) with hdinv
  set dhom : D ⟶ D' := d.hom.map ((𝟙 (Opposite.op K), i.hom) :
    (Opposite.op K, ω) ⟶ (Opposite.op K, ω')) with hdhom
  have hc₁ : dinv ≫ dhom = 𝟙 D' := by
    rw [hdinv, hdhom, ← d.hom.map_comp,
      show ((𝟙 (Opposite.op K), i.inv) : (Opposite.op K, ω') ⟶ (Opposite.op K, ω)) ≫
          ((𝟙 (Opposite.op K), i.hom) : (Opposite.op K, ω) ⟶ (Opposite.op K, ω')) =
          𝟙 (Opposite.op K, ω') from Prod.ext (by simp) (by simp)]
    exact d.hom.map_id _
  have hc₂ : dhom ≫ dinv = 𝟙 D := by
    rw [hdinv, hdhom, ← d.hom.map_comp,
      show ((𝟙 (Opposite.op K), i.hom) : (Opposite.op K, ω) ⟶ (Opposite.op K, ω')) ≫
          ((𝟙 (Opposite.op K), i.inv) : (Opposite.op K, ω') ⟶ (Opposite.op K, ω)) =
          𝟙 (Opposite.op K, ω) from Prod.ext (by simp) (by simp)]
    exact d.hom.map_id _
  have hiso : IsIso (d.hom.map ((dinv.op, i.hom) :
      (Opposite.op D, ω) ⟶ (Opposite.op D', ω'))) := by
    refine ⟨d.hom.map ((dhom.op, i.inv) :
      (Opposite.op D', ω') ⟶ (Opposite.op D, ω)), ?_, ?_⟩
    · rw [← d.hom.map_comp,
        show ((dinv.op, i.hom) : (Opposite.op D, ω) ⟶ (Opposite.op D', ω')) ≫
            ((dhom.op, i.inv) : (Opposite.op D', ω') ⟶ (Opposite.op D, ω)) =
            𝟙 (Opposite.op D, ω) from
          Prod.ext (show dinv.op ≫ dhom.op = 𝟙 (Opposite.op D) by
              rw [← CategoryTheory.op_comp, hc₂]; rfl)
            (show i.hom ≫ i.inv = 𝟙 ω by simp)]
      exact d.hom.map_id _
    · rw [← d.hom.map_comp,
        show ((dhom.op, i.inv) : (Opposite.op D', ω') ⟶ (Opposite.op D, ω)) ≫
            ((dinv.op, i.hom) : (Opposite.op D, ω) ⟶ (Opposite.op D', ω')) =
            𝟙 (Opposite.op D', ω') from
          Prod.ext (show dhom.op ≫ dinv.op = 𝟙 (Opposite.op D') by
              rw [← CategoryTheory.op_comp, hc₁]; rfl)
            (show i.inv ≫ i.hom = 𝟙 ω' by simp)]
      exact d.hom.map_id _
  rw [← bidualityMor_comp_hom_map d i K]
  infer_instance

end Dualizing

namespace Dualizing

open StacksDraft.DerivedHom

/-- The derived homothety of `derivedHomAdjunctionOverRing A` at `ω` is invertible, given a
complex `J` of injective modules, strictly concentrated in degrees `≥ a`, that represents `ω` and
whose scalar homothety is a quasi-isomorphism. -/
theorem isIso_derivedHomothety_overRing_of_injectiveRepresentative (A : Type u) [CommRing A]
    (ω : DerivedCategory (ModuleCat.{max u v} A))
    (J : CochainComplex (ModuleCat.{max u v} A) ℤ) (a : ℤ) (hGE : J.IsStrictlyGE a)
    (hinj : ∀ i : ℤ, Injective (J.X i)) (e : ω ≅ DerivedCategory.Q.obj J)
    (hJ : QuasiIso (homothety J)) :
    IsIso (derivedHomothety (derivedHomAdjunctionOverRing A) (derivedTensorUnit A)
      (derivedTensorUnitLeft A) ω) := by
  let Φ : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} (ULift.{v} A) :=
    ModuleCat.restrictScalars.{max u v}
      (ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom
  have hΦ : Φ.IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
      (ULift.ringEquiv : ULift.{v} A ≃+* A)
  have hJge : CochainComplex.IsStrictlyGE
      ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact Φ.map_isZero ((CochainComplex.isStrictlyGE_iff J a).mp hGE i hi)
  have hJinj : ∀ i : ℤ,
      Injective (((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj J).X i) :=
    fun i => Φ.injective_obj_of_injective (hinj i)
  exact isIso_derivedHomothety_overRing A ω
    (isIso_derivedHomothety_of_injectiveRepresentative _ _
      ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) a
      ((Φ.mapDerivedCategoryFactors.app J).symm ≪≫ (Φ.mapDerivedCategory.mapIso e).symm)
      (quasiIso_homothety_restrictScalars
        (ULift.ringEquiv : ULift.{v} A ≃+* A) J hJ))

end Dualizing

namespace Dualizing

section Generalized

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The derived `ω`-dual over `A` of `RHom_A(B, ω)` is isomorphic to `B[0]`, given a complex `I`
of injective modules, strictly concentrated in degrees `≥ a`, that represents `ω`, and assuming
the biduality morphism of `B[0]` with respect to `ω` is invertible. -/
def dualRestrictScalarsDerivedHomIso_of_isIso_bidualityMor [IsNoetherianRing A] (f : A →+* B)
    {ω : DerivedCategory (ModuleCat.{max v u} A)}
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (a : ℤ)
    (hGE : I.IsStrictlyGE a) (hinj : ∀ i, Injective (I.X i))
    (e : ω ≅ DerivedCategory.Q.obj I)
    (hbid : IsIso (dualizingBidualityMor.{u, max v u} A ω (targetSingle.{u, v} f))) :
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max v u} A).hom.obj
        (Opposite.op ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.obj
          ((derivedHom.{u, v, u} f).obj ω)), ω) ≅
      targetSingle.{u, v} f :=
  (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max v u} A).hom.mapIso
      ((restrictScalarsDerivedHomIso.{u, v} f I a hGE hinj e).symm.op.prod (Iso.refl ω)) ≪≫
    (asIso (dualizingBidualityMor.{u, max v u} A ω (targetSingle.{u, v} f))).symm

/-- For `n ≠ 0` there is at most one morphism `RHom_A(B, ω) ⟶ RHom_A(B, ω)[n]` in `D(B)`, given
a complex `I` of injective modules, strictly concentrated in degrees `≥ a`, that represents `ω`,
and assuming the biduality morphism of `B[0]` with respect to `ω` is invertible. -/
theorem subsingleton_hom_derivedHom_shift_of_isIso_bidualityMor [IsNoetherianRing A]
    (f : A →+* B) {ω : DerivedCategory (ModuleCat.{max v u} A)}
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (a : ℤ)
    (hGE : I.IsStrictlyGE a) (hinj : ∀ i, Injective (I.X i))
    (e : ω ≅ DerivedCategory.Q.obj I)
    (hbid : IsIso (dualizingBidualityMor.{u, max v u} A ω (targetSingle.{u, v} f)))
    (n : ℤ) (hn : n ≠ 0) :
    Subsingleton ((derivedHom.{u, v, u} f).obj ω ⟶
      (shiftFunctor (DerivedCategory (ModuleCat.{max v u} B)) n).obj
        ((derivedHom.{u, v, u} f).obj ω)) := by
  obtain ⟨adj⟩ := restrictScalarsDerived_adj_derivedHom.{u, v, u} f
  have hcs : (derivedHom.{u, v, u} f).CommShift ℤ := adj.rightAdjointCommShift ℤ
  have hzero : Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) n).obj
      (targetSingle.{u, v} f)) := by
    rcases lt_or_gt_of_ne hn with h | h
    · exact DerivedCategory.isZero_of_isGE _ 0 n h
    · exact DerivedCategory.isZero_of_isLE _ 0 n h
  have hsubH : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) n).obj
      ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, max v u} A).obj
        (Opposite.op ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.obj
          ((derivedHom.{u, v, u} f).obj ω)), ω))) :=
    ModuleCat.isZero_iff_subsingleton.mp (hzero.of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) n).mapIso
        (dualRestrictScalarsDerivedHomIso_of_isIso_bidualityMor.{u, v} f I a hGE hinj e hbid)))
  have hsubHom : Subsingleton
      ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.obj
          ((derivedHom.{u, v, u} f).obj ω) ⟶
        (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) n).obj ω) :=
    Equiv.subsingleton (extAddEquivHomologyDerivedInternalHom.{u, max v u}
      (((ModuleCat.restrictScalars.{max v u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((coextendComplex.{u, u, v} f).obj I))
      (restrictScalarsDerivedHomModelIso.{u, v} f I a hGE hinj e) I a hGE hinj e n).symm.toEquiv
  exact Equiv.subsingleton
    ((Iso.homCongr (Iso.refl ((derivedHom.{u, v, u} f).obj ω))
        ((((derivedHom.{u, v, u} f).commShiftIso n).app ω).symm)).trans
      (adj.homEquiv ((derivedHom.{u, v, u} f).obj ω)
        ((shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) n).obj ω)).symm)

/-- The endomorphisms of `RHom_A(B, ω)` in `D(B)` are additively equivalent to the morphisms
`1 ⟶ B[0]` in `D(A)`, by an equivalence under which multiplication by `b : B` corresponds to
postcomposition with multiplication by `b` on `B[0]`. This takes a complex `I` of injective
modules, strictly concentrated in degrees `≥ a`, that represents `ω`, and assumes the biduality
morphism of `B[0]` with respect to `ω` is invertible. -/
theorem exists_endAddEquiv_hom_derivedTensorUnit_of_isIso_bidualityMor [IsNoetherianRing A]
    (f : A →+* B) {ω : DerivedCategory (ModuleCat.{max v u} A)}
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (a : ℤ) (hGE : I.IsStrictlyGE a)
    (hinj : ∀ i, Injective (I.X i)) (e : ω ≅ DerivedCategory.Q.obj I)
    (hbid : IsIso (dualizingBidualityMor.{u, max v u} A ω (targetSingle.{u, v} f))) :
    ∃ E : End ((derivedHom.{u, v, u} f).obj ω) ≃+
        (StacksDraft.DerivedHom.derivedTensorUnit.{u, max v u} A ⟶ targetSingle.{u, v} f),
      ∀ (b : B) (φ : End ((derivedHom.{u, v, u} f).obj ω)),
        E (b • φ) = E φ ≫ (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
          (targetMul.{u, v} f b) := by
  obtain ⟨adj⟩ := restrictScalarsDerived_adj_derivedHom.{u, v, u} f
  set d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max v u} A
  set D₁ := d.hom.obj (Opposite.op (targetSingle.{u, v} f), ω)
  set θ := restrictScalarsDerivedHomIso.{u, v} f I a hGE hinj e
  set bid := @asIso _ _ _ _ (dualizingBidualityMor.{u, max v u} A ω (targetSingle.{u, v} f)) hbid
  set mb : ∀ b : B, targetSingle.{u, v} f ⟶ targetSingle.{u, v} f := fun b =>
    (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map (targetMul.{u, v} f b)
  refine ⟨End.addEquiv.trans ((adj.homAddEquiv ((derivedHom.{u, v, u} f).obj ω) ω).symm.trans
      ((precompAddEquiv θ ω).symm.trans
        ((homUnitAddEquiv d (StacksDraft.DerivedHom.derivedTensorUnit.{u, max v u} A)
            (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, max v u} A) ω D₁).symm.trans
          (postcompAddEquiv _ bid.symm)))), fun b φ => ?_⟩
  simp only [AddEquiv.trans_apply (e₁ := End.addEquiv), End.addEquiv_apply, End.homEquiv_apply,
    End.smul_asHom]
  generalize φ.asHom = φ
  have h₁ : (adj.homAddEquiv ((derivedHom.{u, v, u} f).obj ω) ω).symm (b • φ) =
      (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.map
          (b • 𝟙 ((derivedHom.{u, v, u} f).obj ω)) ≫
        (adj.homAddEquiv ((derivedHom.{u, v, u} f).obj ω) ω).symm φ := by
    apply (adj.homEquiv ((derivedHom.{u, v, u} f).obj ω) ω).injective
    rw [Adjunction.homAddEquiv_symm_apply, Equiv.apply_symm_apply,
      adj.homEquiv_naturality_left, Adjunction.homAddEquiv_symm_apply,
      Equiv.apply_symm_apply, Linear.smul_comp, Category.id_comp]
  have h₂ : θ.inv ≫ (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.map
        (b • 𝟙 ((derivedHom.{u, v, u} f).obj ω)) =
      d.hom.map (((mb b).op, 𝟙 ω) : (Opposite.op (targetSingle.{u, v} f), ω) ⟶
        (Opposite.op (targetSingle.{u, v} f), ω)) ≫ θ.inv :=
    (square_inv θ θ (restrictScalarsDerivedHomIso_smul.{u, v} f b I a hGE hinj e)).symm
  have h₃ := homUnitAddEquiv_naturality d
    (StacksDraft.DerivedHom.derivedTensorUnit.{u, max v u} A)
    (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, max v u} A)
    (StacksDraft.DerivedHom.derivedTensorUnitLeft_natural.{u, max v u} A) ω
    (d.hom.map (((mb b).op, 𝟙 ω) : (Opposite.op (targetSingle.{u, v} f), ω) ⟶
      (Opposite.op (targetSingle.{u, v} f), ω)))
  have h₄ : d.hom.map ((((d.hom.map (((mb b).op, 𝟙 ω) :
            (Opposite.op (targetSingle.{u, v} f), ω) ⟶
              (Opposite.op (targetSingle.{u, v} f), ω)))).op, 𝟙 ω) :
          (Opposite.op D₁, ω) ⟶ (Opposite.op D₁, ω)) ≫ bid.inv =
      bid.inv ≫ mb b :=
    square_inv bid bid (bidualityMor_naturality
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max v u} A) ω (mb b))
  dsimp only [AddEquiv.trans_apply, postcompAddEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    Iso.symm_hom]
  rw [h₁]
  show _ ≫ bid.inv = _
  rw [show (precompAddEquiv θ ω).symm
      ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.map
          (b • 𝟙 ((derivedHom.{u, v, u} f).obj ω)) ≫
        (adj.homAddEquiv ((derivedHom.{u, v, u} f).obj ω) ω).symm φ) =
      d.hom.map (((mb b).op, 𝟙 ω) : (Opposite.op (targetSingle.{u, v} f), ω) ⟶
          (Opposite.op (targetSingle.{u, v} f), ω)) ≫
        (precompAddEquiv θ ω).symm
          ((adj.homAddEquiv ((derivedHom.{u, v, u} f).obj ω) ω).symm φ) from by
    show θ.inv ≫ _ ≫ _ = _ ≫ θ.inv ≫ _
    rw [← Category.assoc, h₂, Category.assoc]]
  rw [show (homUnitAddEquiv d (StacksDraft.DerivedHom.derivedTensorUnit.{u, max v u} A)
        (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, max v u} A) ω D₁).symm
        (d.hom.map (((mb b).op, 𝟙 ω) : (Opposite.op (targetSingle.{u, v} f), ω) ⟶
            (Opposite.op (targetSingle.{u, v} f), ω)) ≫
          (precompAddEquiv θ ω).symm
            ((adj.homAddEquiv ((derivedHom.{u, v, u} f).obj ω) ω).symm φ)) =
      (homUnitAddEquiv d (StacksDraft.DerivedHom.derivedTensorUnit.{u, max v u} A)
          (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, max v u} A) ω D₁).symm
          ((precompAddEquiv θ ω).symm
            ((adj.homAddEquiv ((derivedHom.{u, v, u} f).obj ω) ω).symm φ)) ≫
        d.hom.map ((((d.hom.map (((mb b).op, 𝟙 ω) :
            (Opposite.op (targetSingle.{u, v} f), ω) ⟶
              (Opposite.op (targetSingle.{u, v} f), ω)))).op, 𝟙 ω) :
          (Opposite.op D₁, ω) ⟶ (Opposite.op D₁, ω)) from by
    apply (homUnitAddEquiv d (StacksDraft.DerivedHom.derivedTensorUnit.{u, max v u} A)
      (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, max v u} A) ω D₁).injective
    rw [AddEquiv.apply_symm_apply, h₃, AddEquiv.apply_symm_apply]]
  exact comp_square_right _ h₄

/-- The endomorphisms of `RHom_A(B, ω)` in `D(B)` are `B`-linearly isomorphic to `B`, given a
complex `I` of injective modules, strictly concentrated in degrees `≥ a`, that represents `ω`, and
assuming the biduality morphism of `B[0]` with respect to `ω` is invertible. -/
theorem nonempty_endLinearEquiv_derivedHom_of_isIso_bidualityMor [IsNoetherianRing A]
    (f : A →+* B) {ω : DerivedCategory (ModuleCat.{max v u} A)}
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (a : ℤ) (hGE : I.IsStrictlyGE a)
    (hinj : ∀ i, Injective (I.X i)) (e : ω ≅ DerivedCategory.Q.obj I)
    (hbid : IsIso (dualizingBidualityMor.{u, max v u} A ω (targetSingle.{u, v} f))) :
    Nonempty (End ((derivedHom.{u, v, u} f).obj ω) ≃ₗ[B] B) := by
  obtain ⟨E, hE⟩ := exists_endAddEquiv_hom_derivedTensorUnit_of_isIso_bidualityMor.{u, v}
    f I a hGE hinj e hbid
  set S := DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0
  set uIso := derivedTensorUnitIsoSingle.{u, v} A
  set Θ := E.trans ((precompAddEquiv uIso (targetSingle.{u, v} f)).symm.trans
    ((singleHomAddEquiv.{u, v} A (derivedTensorUnitModule.{u, v} A)
        (targetAsModule.{u, v} f)).trans
      ((derivedTensorUnitModuleHom.{u, v} A (targetAsModule.{u, v} f)).trans AddEquiv.ulift)))
    with hΘ
  have hsmul : ∀ (b : B) (φ : End ((derivedHom.{u, v, u} f).obj ω)), Θ (b • φ) = b * Θ φ := by
    intro b φ
    have h1 : (precompAddEquiv uIso (targetSingle.{u, v} f)).symm (E φ ≫ S.map
          (targetMul.{u, v} f b)) =
        (precompAddEquiv uIso (targetSingle.{u, v} f)).symm (E φ) ≫ S.map
          (targetMul.{u, v} f b) := by
      show uIso.inv ≫ E φ ≫ S.map (targetMul.{u, v} f b) =
        (uIso.inv ≫ E φ) ≫ S.map (targetMul.{u, v} f b)
      rw [Category.assoc]
    simp only [hΘ, AddEquiv.trans_apply]
    rw [hE b φ, h1, singleHomAddEquiv_comp_map]
    rfl
  exact ⟨{ Θ with map_smul' := hsmul }⟩



/-- The derived homothety at any object `ω'` isomorphic to the shift `RHom_A(B, ω)[n]` is
invertible, given a complex `I` of injective modules, strictly concentrated in degrees `≥ a`, that
represents `ω`, and assuming the biduality morphism of `B[0]` with respect to `ω` is
invertible. -/
theorem isIso_derivedHomothety_overRing_derivedHom_shift [IsNoetherianRing A]
    (f : A →+* B) {ω : DerivedCategory (ModuleCat.{max v u} A)}
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (a : ℤ) (hGE : I.IsStrictlyGE a)
    (hinj : ∀ i, Injective (I.X i)) (e : ω ≅ DerivedCategory.Q.obj I)
    (hbid : IsIso (dualizingBidualityMor.{u, max v u} A ω (targetSingle.{u, v} f)))
    (n : ℤ) {ω' : DerivedCategory (ModuleCat.{max v u} B)}
    (e' : ω' ≅ (shiftFunctor (DerivedCategory (ModuleCat.{max v u} B)) n).obj
      ((derivedHom.{u, v, u} f).obj ω)) :
    IsIso (derivedHomothety
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v} B)
      (StacksDraft.DerivedHom.derivedTensorUnit.{u, v} B)
      (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, v} B) ω') := by
  have hI : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  set J := (coextendComplex.{u, u, v} f).obj I
  have hJge : J.IsStrictlyGE a := isStrictlyGE_coextendComplex_obj.{u, v} f I a
  have hJinj : ∀ i : ℤ, Injective (J.X i) := injective_coextendComplex_obj_X.{u, v} f I hinj
  have hJki : J.IsKInjective := CochainComplex.isKInjective_of_injective J a
  set eJ : (derivedHom.{u, v, u} f).obj ω ≅ DerivedCategory.Q.obj J :=
    (derivedHom.{u, v, u} f).mapIso e ≪≫ derivedHomObjIsoCoextend.{u, v} f I hI
  obtain ⟨e₀⟩ := nonempty_endLinearEquiv_derivedHom_of_isIso_bidualityMor.{u, v}
    f I a hGE hinj e hbid
  have hvanish : ∀ m : ℤ, m ≠ 0 →
      IsZero ((CochainComplex.HomComplexR B J J).homology m) := by
    intro m hm
    refine isZero_homology_homComplexR_of_subsingleton.{u, v} J a m ?_
    have := subsingleton_hom_derivedHom_shift_of_isIso_bidualityMor.{u, v}
      f I a hGE hinj e hbid m hm
    exact Equiv.subsingleton (Iso.homCongr eJ.symm
      ((shiftFunctor (DerivedCategory (ModuleCat.{max v u} B)) m).mapIso eJ.symm))
  have hhom : QuasiIso (homothety J) :=
    quasiIso_homothety_of_rankOne J
      ((homologyZeroEndLinearEquiv J).trans ((endLinearEquivOfIso eJ.symm).trans e₀)) hvanish
  have hshift : QuasiIso (homothety (J⟦n⟧)) := quasiIso_homothety_shift J n hhom
  have hSge : (J⟦n⟧).IsStrictlyGE (a - n) := J.isStrictlyGE_shift a n (a - n) (by omega)
  have hSinj : ∀ i : ℤ, Injective ((J⟦n⟧).X i) := fun i =>
    Injective.of_iso (J.shiftFunctorObjXIso n i (n + i) (by abel)).symm (hJinj (n + i))
  exact isIso_derivedHomothety_overRing_of_injectiveRepresentative.{u, v} B ω' (J⟦n⟧) (a - n)
    hSge hSinj (e' ≪≫ (shiftFunctor (DerivedCategory (ModuleCat.{max v u} B)) n).mapIso eJ ≪≫
      ((DerivedCategory.Q.commShiftIso n).app J).symm) hshift

end Generalized

end Dualizing

namespace Dualizing

section Perfect07VI

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The canonical biduality morphism with respect to the derived tensor unit over `A` is
invertible at every object `K` of `D(A)` whose preimage under the scalar equivalence is
perfect. -/
theorem isIso_dualizingBidualityMor_derivedTensorUnit_of_isPerfect
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : StacksDraft.Perfect.IsPerfect
      ((derivedScalarEquivalence.{u, max v u} A).inverse.obj K)) :
    IsIso (dualizingBidualityMor.{u, max v u} A
      (StacksDraft.DerivedHom.derivedTensorUnit.{u, max v u} A) K) := by
  have h1 : IsIso (bidualityMor
      (StacksDraft.DerivedHom.derivedHomAdjunctionULift.{u, max v u, max (max v u) u + 1}
        (R := A)).toDerivedHomAdjunction
      (DerivedCategory.Q.obj (𝟙_ (StacksDraft.DerivedHom.Model.Complex (ULift.{max v u} A))))
      ((derivedScalarEquivalence.{u, max v u} A).inverse.obj K)) :=
    (StacksDraft.Perfect.isPerfect_derivedDual_and_naturalIsos
      ((derivedScalarEquivalence.{u, max v u} A).inverse.obj K) hK).biduality_isIso
  have h2 := isIso_bidualityMor_of_iso_dualizing _
    ((derivedScalarEquivalence.{u, max v u} A).unitIso.app
      (DerivedCategory.Q.obj (𝟙_ (StacksDraft.DerivedHom.Model.Complex (ULift.{max v u} A)))))
    ((derivedScalarEquivalence.{u, max v u} A).inverse.obj K) h1
  rw [dualizingBidualityMor_eq_transport]
  exact isIso_bidualityMor_transport _ (derivedScalarEquivalence.{u, max v u} A) _ K h2

/-- Perfectness of `B[0]` over `A` passes to its scalar preimage over `ULift A`. -/
theorem isPerfect_scalarPreimage_targetSingle (f : A →+* B)
    (h : StacksDraft.Perfect.IsPerfect (targetSingle.{u, v} f)) :
    StacksDraft.Perfect.IsPerfect
      ((derivedScalarEquivalence.{u, max v u} A).inverse.obj (targetSingle.{u, v} f)) :=
  StacksDraft.Perfect.isPerfect_restrictScalars_ringEquiv
    (ULift.ringEquiv : ULift.{max v u} A ≃+* A) _ h

end Perfect07VI

end Dualizing

end
