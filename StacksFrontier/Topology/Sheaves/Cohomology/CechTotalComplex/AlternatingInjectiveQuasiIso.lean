module

public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingGlobalSections
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueAlternatingVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.InjectiveVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.InjectiveQuasiIso

/-!
# The alternating Čech comparison for a complex of injectives

Let `(X, O_X)` be a ringed space and let `U : I → Opens X` be a *finite* open covering of `X`.
For an arbitrary — in particular unbounded — complex `K^•` of injective sheaves of
`O_X`-modules the canonical map

`Γ(X, K^•) ⟶ Tot(Č_alt^•(U, K^•))`

of Tag 08C0 from the complex of global sections to the total alternating Čech complex is a
quasi-isomorphism.

## Main results

* `Stacks.Cech.isZero_alternatingSubgroup_of_card_lt`: alternating Čech cochains of degree at
  least the number of members of the family vanish.
* `Stacks.Cech.isIso_kernelLift_of_hom`: a kernel-form augmentation transports along a
  morphism of complexes that is invertible in degree zero and monic in degree one.
* `Stacks.Cech.isIso_globalSectionsAlternatingCechRestriction_kernelLift`: Tag 01EG in
  alternating kernel form.
* `Stacks.Cech.quasiIso_globalSectionsToAlternatingCech_of_injective`: the comparison is a
  quasi-isomorphism for a complex of injectives over a finite covering.

## Implementation notes

The statement is an instance of the resolution criterion for a total complex, Tag 0133 in the
form `quasiIso_total_of_resolution_flip`. The difference from the non-alternating
`Stacks.Cech.quasiIso_globalSectionsToCech_of_injective` is where the finiteness comes from:
there the complex `K^•` is assumed bounded below, which bounds the diagonals of the Čech
bicomplex from one side and the nonnegativity of the Čech degree bounds them from the other;
here `K^•` is arbitrary and the covering is finite, so the *alternating* Čech complex itself is
bounded — an alternating cochain indexed by tuples longer than the number of members of the
family vanishes, because such a tuple has a repeated index.

The column exactness in positive degrees is alternating Čech acyclicity of the abelian sheaf
underlying an injective sheaf of modules, which is `underlying_isFlasque` (the abelian-group
shadow of Tag 01EP) followed by `isZero_alternatingCechComplex_homology_of_isFlasque`.

In degree zero the criterion asks for an isomorphism onto the kernel of the first alternating
Čech differential. That is Tag 01EG, which
`Stacks.Cech.isIso_globalSectionsCechRestriction_kernelLift` provides for Mathlib's Čech
complex; `isIso_kernelLift_of_hom` carries it across the canonical inclusion of the
alternating Čech complex followed by `Stacks.Cech.cechComplexIso`, which is invertible in
degree zero — a degree-zero index tuple has a single entry, so every degree-zero cochain is
alternating — and monic in degree one. The comparison isomorphisms between the nonnegatively
graded alternating Čech complex and the integer-indexed one are then handled by
`Stacks.Cech.isIso_extendZero_kernelLift`.

The space and the coefficient universes coincide, as the existing Čech product API and Tag
01EG require.

## References

* [Stacks Project, Tag 08C1](https://stacks.math.columbia.edu/tag/08C1)
* [Stacks Project, Tag 08C0](https://stacks.math.columbia.edu/tag/08C0)
* [Stacks Project, Tag 01EG](https://stacks.math.columbia.edu/tag/01EG)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape TopologicalSpace Opposite
open StacksDraft.TotalComplexQuasiIso

universe u v w

namespace Stacks.Cech

/-! ### Alternating cochains over a finite family -/

/-- Over a finite family of opens the alternating Čech cochains vanish in every degree at
least the number of members of the family: a longer index tuple has a repeated index. -/
theorem isZero_alternatingSubgroup_of_card_lt {Y : TopCat.{u}} {J : Type v} [Finite J]
    (V : J → Opens Y) (ℱ : TopCat.Presheaf Ab.{w} Y) (p : ℕ) (hp : Nat.card J < p + 1) :
    IsZero (AddCommGrpCat.of (CechCochains.alternatingSubgroup V ℱ p)) := by
  have hnotinj (i : Fin (p + 1) → J) : ¬ Function.Injective i := fun hi ↦
    absurd (Nat.card_le_card_of_injective i hi) (by simpa using hp)
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact ⟨fun s t ↦ Subtype.ext (funext fun i ↦ by
    rw [s.2.1 i (hnotinj i), t.2.1 i (hnotinj i)])⟩

/-! ### Transport of a kernel-form augmentation -/

/-- **Transport of a kernel-form augmentation.** Let `φ : C ⟶ D` be a morphism of
nonnegatively graded complexes which is invertible in degree zero and monic in degree one, and
let `u` be an isomorphism of the two augmenting objects compatible with `φ`. If the
augmentation of `D` is an isomorphism onto the kernel of its first differential, so is the
augmentation of `C`. -/
theorem isIso_kernelLift_of_hom {A : Type*} [Category A] [Abelian A]
    {C D : CochainComplex A ℕ} (φ : C ⟶ D) [IsIso (φ.f 0)] [Mono (φ.f 1)]
    {P Q : A} (u : P ⟶ Q) [IsIso u]
    (r : P ⟶ C.X 0) (hr : r ≫ C.d 0 1 = 0) (r' : Q ⟶ D.X 0) (hr' : r' ≫ D.d 0 1 = 0)
    (hcompat : r ≫ φ.f 0 = u ≫ r')
    (h : IsIso (kernel.lift (D.d 0 1) r' hr')) :
    IsIso (kernel.lift (C.d 0 1) r hr) := by
  have hw : C.d 0 1 ≫ φ.f 1 = φ.f 0 ≫ D.d 0 1 := (φ.comm 0 1).symm
  have hfork : (kernel.ι (D.d 0 1) ≫ inv (φ.f 0)) ≫ C.d 0 1 = 0 := by
    refine (cancel_mono (φ.f 1)).mp ?_
    rw [Category.assoc, Category.assoc, hw, IsIso.inv_hom_id_assoc, kernel.condition, zero_comp]
  have hkmap : IsIso (kernel.map (C.d 0 1) (D.d 0 1) (φ.f 0) (φ.f 1) hw) := by
    refine ⟨⟨kernel.lift (C.d 0 1) (kernel.ι (D.d 0 1) ≫ inv (φ.f 0)) hfork, ?_, ?_⟩⟩
    · exact (cancel_mono (kernel.ι (C.d 0 1))).mp (by simp)
    · exact (cancel_mono (kernel.ι (D.d 0 1))).mp (by simp)
  have hcomp : kernel.lift (C.d 0 1) r hr ≫
      kernel.map (C.d 0 1) (D.d 0 1) (φ.f 0) (φ.f 1) hw =
      u ≫ kernel.lift (D.d 0 1) r' hr' :=
    (cancel_mono (kernel.ι (D.d 0 1))).mp (by simp [hcompat])
  rw [(IsIso.eq_comp_inv _).2 hcomp]
  infer_instance

/-! ### Degree zero of the alternating Čech complex -/

variable (X : TopCat.{u}) {I : Type u} (U : I → Opens X)

/-- Every degree-zero Čech cochain is alternating: a degree-zero index tuple has a single
entry, so it is injective and no two of its positions differ. -/
theorem alternatingSubgroup_zero_eq_top (ℱ : TopCat.Presheaf Ab.{u} X) :
    CechCochains.alternatingSubgroup U ℱ 0 = ⊤ := by
  refine eq_top_iff.2 fun s _ ↦ ⟨fun i hi ↦ ?_, fun i a b hab ↦ ?_⟩
  · exact absurd (fun a b _ ↦ (Fin.eq_zero a).trans (Fin.eq_zero b).symm) hi
  · exact absurd ((Fin.eq_zero a).trans (Fin.eq_zero b).symm) hab

/-- The inclusion of the alternating cochains of a fixed degree is monic. -/
private theorem mono_ofHom_alternatingSubgroup_subtype (ℱ : TopCat.Presheaf Ab.{u} X) (p : ℕ) :
    Mono (AddCommGrpCat.ofHom (CechCochains.alternatingSubgroup U ℱ p).subtype) :=
  (AddCommGrpCat.mono_iff_injective _).2 Subtype.val_injective

/-- In degree zero the canonical inclusion of the alternating Čech complex is invertible. -/
theorem isIso_alternatingCechInclusion_f_zero (ℱ : TopCat.Presheaf Ab.{u} X) :
    IsIso ((alternatingCechInclusion U ℱ).f 0) := by
  rw [alternatingCechInclusion_f]
  have hmono := mono_ofHom_alternatingSubgroup_subtype X U ℱ 0
  have hepi : Epi (AddCommGrpCat.ofHom (CechCochains.alternatingSubgroup U ℱ 0).subtype) :=
    (AddCommGrpCat.epi_iff_surjective _).2 fun s ↦
      ⟨⟨s, by simp [alternatingSubgroup_zero_eq_top]⟩, rfl⟩
  exact isIso_of_mono_of_epi _

/-- The canonical inclusion of the alternating Čech complex is monic in every degree. -/
theorem mono_alternatingCechInclusion_f (ℱ : TopCat.Presheaf Ab.{u} X) (p : ℕ) :
    Mono ((alternatingCechInclusion U ℱ).f p) := by
  rw [alternatingCechInclusion_f]
  exact mono_ofHom_alternatingSubgroup_subtype X U ℱ p

/-- The isomorphism between the universe lift of an abelian group and the group itself. -/
noncomputable def uliftSectionsIso (A : Ab.{u}) :
    (AddCommGrpCat.uliftFunctor.{u, u}).obj A ≅ A :=
  AddEquiv.toAddCommGrpIso (AddEquiv.ulift (α := (A : Type u)))

/-- The alternating Čech complex included into Mathlib's Čech complex. -/
noncomputable def alternatingCechToCech (ℱ : TopCat.Presheaf Ab.{u} X) :
    alternatingCechComplex U ℱ ⟶ (CategoryTheory.cechComplexFunctor U).obj ℱ :=
  alternatingCechInclusion U ℱ ≫ (cechComplexIso U ℱ).hom

/-- The degree-zero augmentation of the alternating Čech complex is the augmentation of
Mathlib's Čech complex, read through the inclusion of the alternating subcomplex and the
universe lift on global sections. -/
theorem globalSectionsAlternatingCechRestriction_comp (ℱ : TopCat.Presheaf Ab.{u} X) :
    globalSectionsAlternatingCechRestriction X U ℱ ≫ (alternatingCechToCech X U ℱ).f 0 =
      (uliftSectionsIso (ℱ.obj (op ⊤))).hom ≫ globalSectionsCechRestriction X U ℱ 0 := by
  refine cechπ_hom_ext U ℱ fun x ↦ ?_
  have hR : globalSectionsCechRestriction X U ℱ 0 ≫ cechπ U ℱ 0 x =
      AddCommGrpCat.ofHom (CechCochains.restr ℱ (le_top : CechCochains.inter U x ≤ ⊤)) := by
    rw [cechπ_eq, ← Category.assoc]
    have hlift : globalSectionsCechRestriction X U ℱ 0 ≫
        _root_.Stacks.CategoryTheory.CechComplex.π U ℱ 0 x =
        ℱ.map (homOfLE le_top).op := Pi.lift_comp_π _ x
    rw [hlift, interSectionsIso, Functor.mapIso_hom]
    change _ = ℱ.map (homOfLE (le_top : CechCochains.inter U x ≤ ⊤)).op
    rw [← ℱ.map_comp]
    exact congrArg ℱ.map (Subsingleton.elim _ _)
  rw [alternatingCechToCech, HomologicalComplex.comp_f, cechComplexIso_hom_f,
    Category.assoc, Category.assoc, Category.assoc,
    cechComplexObjIso_hom_comp_cechπ_eval, hR]
  exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ ↦ rfl)

/-- **Tag 01EG in alternating kernel form.** For a sheaf of modules, the degree-zero
augmentation of the alternating Čech complex of the underlying abelian presheaf is an
isomorphism onto the kernel of the first alternating Čech differential. -/
theorem isIso_globalSectionsAlternatingCechRestriction_kernelLift
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} (hU : (⊤ : Opens X) = iSup U)
    (M : SheafOfModules.{u} R) :
    IsIso (kernel.lift
      ((alternatingCechComplex U
        ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).obj M)).d 0 1)
      (globalSectionsAlternatingCechRestriction X U
        ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).obj M))
      (globalSectionsAlternatingCechRestriction_d X U
        ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).obj M))) := by
  have hzero : IsIso ((alternatingCechToCech X U
      ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).obj M)).f 0) := by
    rw [alternatingCechToCech, HomologicalComplex.comp_f]
    have := isIso_alternatingCechInclusion_f_zero X U
      ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).obj M)
    infer_instance
  have hone : Mono ((alternatingCechToCech X U
      ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).obj M)).f 1) := by
    rw [alternatingCechToCech, HomologicalComplex.comp_f]
    have := mono_alternatingCechInclusion_f X U
      ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).obj M) 1
    infer_instance
  exact isIso_kernelLift_of_hom _ (uliftSectionsIso _).hom _ _ _
    (globalSectionsCechRestriction_d X U _)
    (globalSectionsAlternatingCechRestriction_comp X U _)
    (isIso_globalSectionsCechRestriction_kernelLift X U hU M)

/-! ### The comparison for a complex of injectives -/

/-- **Alternating Čech acyclicity of an injective sheaf of modules.** The abelian sheaf
underlying an injective sheaf of modules is flasque, and a flasque sheaf has vanishing
positive-degree alternating Čech cohomology. -/
theorem isZero_alternatingCechHomology_of_injective
    {Y : TopCat.{u}} {S : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    {J : Type u} (V : J → Opens Y) (M : SheafOfModules.{u} S) [Injective M]
    (p : ℕ) (hp : 0 < p) :
    IsZero ((alternatingCechComplex V
      ((SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj).obj M)).homology p) := by
  have := Stacks.Cohomology.CechSheaf.underlying_isFlasque (R := S) M
  exact isZero_alternatingCechComplex_homology_of_isFlasque V
    (Stacks.Cohomology.CechSheaf.abSheaf M) p hp

/-- The degree-zero augmentation of Tag 08C0 as a map into the degree-zero row of the flipped
alternating Čech bicomplex. -/
noncomputable def globalSectionsToAlternatingCechRowZero
    (L : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ) :
    (globalSectionsUliftComplexFunctor.{u, u, u} X).obj L ⟶
      rowZero ((alternatingCechBicomplexFunctor U).obj L).flip where
  f n := globalSectionsAlternatingCechRestrictionInt X U (L.X n)
  comm' := by
    rintro n _ rfl
    exact (globalSectionsAlternatingCechRestrictionInt_naturality X U (L.d n (n + 1))).symm

/-- The flipped alternating Čech bicomplex vanishes in negative Čech degree. -/
theorem isZero_alternatingCechBicomplex_flip_X_X_of_neg
    (L : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ) (p q : ℤ) (hq : q < 0) :
    IsZero ((((alternatingCechBicomplexFunctor U).obj L).flip.X p).X q) := by
  change IsZero (((alternatingCechComplex U (L.X p)).extend embeddingUpNat).X q)
  refine HomologicalComplex.isZero_extend_X _ _ _ fun i hi ↦ ?_
  change (i : ℤ) = q at hi
  omega

/-- Over a finite family the flipped alternating Čech bicomplex vanishes in every Čech degree
at least the number of members of the family. -/
theorem isZero_alternatingCechBicomplex_flip_X_X_of_card_le [Finite I]
    (L : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ) (p q : ℤ)
    (hq : (Nat.card I : ℤ) ≤ q) :
    IsZero ((((alternatingCechBicomplexFunctor U).obj L).flip.X p).X q) := by
  have hq0 : 0 ≤ q := le_trans (Int.natCast_nonneg _) hq
  have hcast : embeddingUpNat.f q.toNat = q := by simp [Int.toNat_of_nonneg hq0]
  refine IsZero.of_iso ?_ ((alternatingCechComplex U (L.X p)).extendXIso embeddingUpNat hcast)
  rw [alternatingCechComplex_X]
  refine isZero_alternatingSubgroup_of_card_lt U (L.X p) q.toNat ?_
  have := Int.self_le_toNat q
  omega

/-- Over a finite family the flipped alternating Čech bicomplex has finite diagonals. -/
theorem diagonalFinite_alternatingCechBicomplex_flip [Finite I]
    (L : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ) :
    DiagonalFinite ((alternatingCechBicomplexFunctor U).obj L).flip := by
  intro n
  refine (Set.finite_Icc (n - (Nat.card I : ℤ) + 1) n).subset fun p hp ↦ ⟨?_, ?_⟩
  · by_contra
    exact hp (isZero_alternatingCechBicomplex_flip_X_X_of_card_le X U L p (n - p) (by omega))
  · by_contra
    exact hp (isZero_alternatingCechBicomplex_flip_X_X_of_neg X U L p (n - p) (by omega))

/-- **The alternating Čech comparison for a complex of injectives.** For a finite open covering
of `X`, the canonical map from the complex of global sections of a complex of injective sheaves
of modules to its total alternating Čech complex is a quasi-isomorphism. -/
theorem quasiIso_globalSectionsToAlternatingCech_of_injective
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} [Finite I]
    (hU : (⊤ : Opens X) = iSup U)
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) (hKinj : ∀ n : ℤ, Injective (K.X n)) :
    QuasiIso ((globalSectionsToAlternatingCech X U).app
      ((underlyingPresheafComplexFunctor X R).obj K)) := by
  let L := (underlyingPresheafComplexFunctor X R).obj K
  let DA := (alternatingCechBicomplexFunctor U).obj L
  let α := globalSectionsToAlternatingCechRowZero X U L
  have hexact (p q : ℤ) (hq : q ≠ 0) : ((DA.flip).X p).ExactAt q := by
    by_cases hneg : q < 0
    · exact HomologicalComplex.ExactAt.of_isZero
        (isZero_alternatingCechBicomplex_flip_X_X_of_neg X U L p q hneg)
    · have hq' : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (by omega)
      have hC : (alternatingCechComplex U (L.X p)).ExactAt q.toNat := by
        rw [HomologicalComplex.exactAt_iff_isZero_homology]
        exact isZero_alternatingCechHomology_of_injective U (K.X p) q.toNat (by omega)
      change ((alternatingCechComplex U (L.X p)).extend embeddingUpNat).ExactAt q
      exact ((alternatingCechComplex U (L.X p)).extend_exactAt_iff embeddingUpNat hq').mpr hC
  have hkernel (p : ℤ) :
      ∃ hα : α.f p ≫ ((DA.flip).X p).d 0 1 = 0,
        IsIso (kernel.lift (((DA.flip).X p).d 0 1) (α.f p) hα) := by
    have hr : globalSectionsAlternatingCechRestriction X U (L.X p) ≫
        (alternatingCechComplex U (L.X p)).d 0 1 = 0 :=
      globalSectionsAlternatingCechRestriction_d X U (L.X p)
    have hiso : IsIso (kernel.lift ((alternatingCechComplex U (L.X p)).d 0 1)
        (globalSectionsAlternatingCechRestriction X U (L.X p)) hr) :=
      isIso_globalSectionsAlternatingCechRestriction_kernelLift X U hU (K.X p)
    refine ⟨globalSectionsAlternatingCechRestrictionInt_d X U (L.X p), ?_⟩
    change IsIso (kernel.lift
      (((alternatingCechComplex U (L.X p)).extend embeddingUpNat).d 0 1)
      (globalSectionsAlternatingCechRestriction X U (L.X p) ≫
        ((alternatingCechComplex U (L.X p)).extendXIso embeddingUpNat
          (i := 0) (i' := 0) rfl).inv) _)
    exact isIso_extendZero_kernelLift (alternatingCechComplex U (L.X p)) _ hr _
  exact quasiIso_of_componentwise_resolution_map _ DA α
    ⟨diagonalFinite_alternatingCechBicomplex_flip X U L,
      isZero_alternatingCechBicomplex_flip_X_X_of_neg X U L, hexact, hkernel⟩
    _ fun n ↦ globalSectionsToAlternatingCech_app_f X U L n

end Stacks.Cech

end
