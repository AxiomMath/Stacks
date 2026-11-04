module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.DegreeZeroAndTheSheafCondition
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueCechVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.InjectiveVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.RecoveryA.GlobalSectionsToCech

/-!
# The Čech comparison for a bounded below complex of injectives

Let `(X, O_X)` be a ringed space and let `U : I → Opens X` be an open covering of `X`. For a
bounded below complex `K^•` of injective sheaves of `O_X`-modules the canonical map

`Γ(X, K^•) ⟶ Tot(Č^•(U, K^•))`

of Tag 07M9 from the complex of global sections to the total Čech complex is a
quasi-isomorphism.

## Main definitions

* `Stacks.Cech.underlyingPresheafComplexFunctor`: a complex of sheaves of modules, read as a
  complex of abelian presheaves.

## Main results

* `Stacks.Cech.quasiIso_globalSectionsToCech_of_injective`: the comparison is a
  quasi-isomorphism for a bounded below complex of injectives.
* `Stacks.Cech.isIso_globalSectionsCechRestriction_kernelLift`: Tag 01EG in kernel form, for
  the abelian presheaf underlying a sheaf of modules.
* `Stacks.Cech.isIso_extendZero_kernelLift`: a kernel-form augmentation of a nonnegatively
  graded complex transports to the complex extended by zero to integer degrees.
* `Stacks.Cech.quasiIso_of_componentwise_resolution_map`: a map into a total complex whose
  components factor through the degree-zero summand is the comparison map of Tag 0133.

## Implementation notes

The statement is an instance of the resolution criterion for a total complex, Tag 0133 in the
form `quasiIso_total_of_resolution_flip`: the Čech bicomplex of `K^•`, flipped, has finite
diagonals (because `K^•` is bounded below and the Čech complex is concentrated in nonnegative
degrees), its columns vanish in negative degrees and are exact in every nonzero degree, and in
degree zero the augmentation induces an isomorphism onto the kernel of the first Čech
differential.

The column exactness is Čech acyclicity of the abelian sheaf underlying an injective sheaf of
modules. That sheaf is flasque (`Stacks.Cohomology.CechSheaf.underlying_isFlasque`, the
abelian-group shadow of Tag 01EP) and a flasque sheaf has vanishing positive-degree Čech
cohomology for every family of opens (Tag 09SZ,
`Stacks.Cohomology.FlasqueCech.isZero_cechComplex_homology_of_isFlasque`), so no comparison
with the module-valued Čech complex of Tag 01EP is needed.

In degree zero the criterion asks for an isomorphism onto a kernel rather than for the
isomorphism onto `H^0` that Tag 01EG provides, and it asks for it in the integer-indexed Čech
complex rather than the nonnegatively graded one. `isIso_kernelLift_of_homologyZeroIso` does
the first step — an augmentation that becomes an isomorphism onto `H^0` is an isomorphism onto
the cycles in degree zero, which for a complex indexed from `0` are the kernel of `d^{0,1}` —
and `isIso_extendZero_kernelLift` transports it along the comparison isomorphisms between the
two indexings.

The space and the coefficient universes coincide, as the existing Čech product API requires.

## References

* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
* [Stacks Project, Tag 07M9](https://stacks.math.columbia.edu/tag/07M9)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 01EG](https://stacks.math.columbia.edu/tag/01EG)
* [Stacks Project, Tag 09SZ](https://stacks.math.columbia.edu/tag/09SZ)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape TopologicalSpace Opposite

universe u v

namespace Stacks.Cech

variable (X : TopCat.{u})

/-- A complex of sheaves of modules on `X`, read as a complex of abelian presheaves on `X`. -/
noncomputable abbrev underlyingPresheafComplexFunctor
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    CochainComplex (SheafOfModules.{u} R) ℤ ⥤
      CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ :=
  (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).mapHomologicalComplex (up ℤ)

/-- The integer-indexed Čech complex preserves zero morphisms, as the nonnegatively graded one
does and extension by zero is additive. -/
instance cechComplexFunctorInt_preservesZeroMorphisms
    {C : Type u} [Category.{v} C] [HasFiniteProducts C] {κ : Type u} (U : κ → C)
    [(CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{u}) U).PreservesZeroMorphisms] :
    (cechComplexFunctorInt U).PreservesZeroMorphisms := by
  constructor
  intro A B
  change (embeddingUpNat.extendFunctor AddCommGrpCat.{u}).map
    ((CategoryTheory.cechComplexFunctor U).map 0) = 0
  rw [Functor.map_zero, Functor.map_zero]

/-- **Čech acyclicity of an injective sheaf of modules, for its underlying abelian presheaf.**
The abelian sheaf underlying an injective sheaf of modules is flasque, and a flasque sheaf has
vanishing positive-degree Čech cohomology. -/
private theorem isZero_cechUnderlyingHomology_of_injective
    {Y : TopCat.{u}} {S : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    {κ : Type u} (U : κ → Opens Y) (hU : (⊤ : Opens Y) = ⨆ i, U i)
    (M : SheafOfModules.{u} S) [Injective M] (p : ℕ) (hp : 0 < p) :
    IsZero (((cechComplexFunctor U).obj
      ((SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj).obj M)).homology p) := by
  have := Stacks.Cohomology.CechSheaf.underlying_isFlasque (R := S) M
  exact Stacks.Cohomology.FlasqueCech.isZero_cechComplex_homology_of_isFlasque
    (Stacks.Cohomology.CechSheaf.abSheaf M) ⊤ U hU p hp

/-- The component of the degree-`n` Čech augmentation of Tag 07M9 at a tuple is restriction to
the intersection it indexes. -/
private lemma globalSectionsCechRestriction_π
    {κ : Type u} (U : κ → Opens X) (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ)
    (i : Fin (n + 1) → κ) :
    globalSectionsCechRestriction X U P n ≫
        Pi.π (fun j : Fin (n + 1) → κ => P.obj (op (∏ᶜ fun a => U (j a)))) i =
      P.map (homOfLE (le_top (a := ∏ᶜ fun a => U (i a)))).op :=
  Pi.lift_π _ i

/-- The two descriptions of the degree-zero Čech augmentation of an abelian presheaf — the one
of Tag 07M9 and the one of Tag 01EG — agree: each component of each is the image under the
presheaf of a morphism of opens, and there is only one such morphism. -/
private lemma globalSectionsCechRestriction_eq_cechDegreeZeroRestriction
    {κ : Type u} (U : κ → Opens X) (hU : (⊤ : Opens X) = iSup U)
    (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    globalSectionsCechRestriction X U P 0 =
      Stacks.Cohomology.CechDegreeZero.cechDegreeZeroRestriction P ⊤ U hU := by
  refine Pi.hom_ext (f := fun i : Fin 1 → κ => P.obj (op (∏ᶜ fun a => U (i a)))) _ _ fun i => ?_
  have hthin : P.map (eqToHom (congrArg op hU)) ≫
        P.map (Quiver.Hom.op
          (Pi.π (fun a : Fin 1 => U (i a)) 0 ≫ homOfLE (le_iSup U (i 0)))) =
      P.map (homOfLE (le_top (a := ∏ᶜ fun a => U (i a)))).op :=
    (P.map_comp _ _).symm.trans (congrArg P.map (Subsingleton.elim _ _))
  exact (globalSectionsCechRestriction_π X U P 0 i).trans
    (hthin.symm.trans
      (Stacks.Cohomology.CechDegreeZero.cechDegreeZeroRestriction_π P ⊤ U hU i).symm)

/-- An augmentation which becomes an isomorphism onto `H^0` is an isomorphism onto the kernel
of the first differential. -/
private theorem isIso_kernelLift_of_homologyZeroIso
    {A : AddCommGrpCat.{u}} (C : CochainComplex AddCommGrpCat.{u} ℕ)
    (r : A ⟶ C.X 0) (hr : r ≫ C.d 0 1 = 0)
    (f : A ⟶ C.homology 0) [IsIso f]
    (hf : f ≫ C.homologyι 0 = r ≫ C.pOpcycles 0) :
    IsIso (kernel.lift (C.d 0 1) r hr) := by
  let s : A ⟶ C.cycles 0 := f ≫ C.isoHomologyπ₀.inv
  have harrow : (C.isoHomologyπ₀.inv ≫ C.iCycles 0) ≫ C.pOpcycles 0 =
      C.homologyι 0 := by
    rw [← cancel_epi (C.homologyπ 0)]
    simp only [Category.assoc, C.homology_π_ι]
    simp
  have hs : s ≫ C.iCycles 0 = r := by
    apply (cancel_mono (C.pOpcycles 0)).mp
    dsimp [s]
    simpa only [Category.assoc, harrow] using hf
  have hlim : IsLimit (KernelFork.ofι r hr) :=
    IsKernel.isoKernel (C.d 0 1) r
      (C.cyclesIsKernel (i := 0) (j := 1) (by simp))
      (asIso s) hs
  let e := hlim.conePointUniqueUpToIso (kernelIsKernel (C.d 0 1))
  have he : e.hom = kernel.lift (C.d 0 1) r hr := by
    apply (cancel_mono (kernel.ι (C.d 0 1))).mp
    simpa only [KernelFork.ι_ofι, Fork.ι_ofι, Fork.app_zero_eq_ι, kernel.lift_ι] using
      hlim.conePointUniqueUpToIso_hom_comp
        (kernelIsKernel (C.d 0 1)) WalkingParallelPair.zero
  rw [← he]
  infer_instance

/-- **Tag 01EG in kernel form.** For a sheaf of modules, the degree-zero Čech augmentation of
the underlying abelian presheaf is an isomorphism onto the kernel of the first Čech
differential. -/
theorem isIso_globalSectionsCechRestriction_kernelLift
    {κ : Type u} (U : κ → Opens X) (hU : (⊤ : Opens X) = iSup U)
    {S : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (M : SheafOfModules.{u} S) :
    IsIso (kernel.lift
      (((cechComplexFunctor U).obj
        ((SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj).obj M)).d 0 1)
      (globalSectionsCechRestriction X U
        ((SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj).obj M) 0)
      (globalSectionsCechRestriction_d X U
        ((SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj).obj M))) := by
  let P := (SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj).obj M
  let C := (cechComplexFunctor U).obj P
  have hP : TopCat.Presheaf.IsSheaf P := M.isSheaf
  obtain ⟨f, ⟨hf, hcomp⟩, _⟩ :=
    ((Stacks.Cohomology.CechDegreeZero.isSheaf_iff_existsUnique_cechRestrictionHomologyMap
      P).mp hP) κ ⊤ U hU
  have : IsIso f := hf
  apply isIso_kernelLift_of_homologyZeroIso C
    (globalSectionsCechRestriction X U P 0)
    (globalSectionsCechRestriction_d X U P) f
  simpa only [globalSectionsCechRestriction_eq_cechDegreeZeroRestriction X U hU P] using hcomp

/-- The kernel-form augmentation transported to the integer-indexed Čech complex. -/
theorem isIso_extendZero_kernelLift
    {A : AddCommGrpCat.{u}} (C : CochainComplex AddCommGrpCat.{u} ℕ)
    (r : A ⟶ C.X 0) (hr : r ≫ C.d 0 1 = 0)
    [IsIso (kernel.lift (C.d 0 1) r hr)]
    (hr' : (r ≫ (C.extendXIso embeddingUpNat (i := 0) (i' := 0) rfl).inv) ≫
      (C.extend embeddingUpNat).d 0 1 = 0) :
    IsIso (kernel.lift ((C.extend embeddingUpNat).d 0 1)
      (r ≫ (C.extendXIso embeddingUpNat (i := 0) (i' := 0) rfl).inv) hr') := by
  let e₀ := C.extendXIso embeddingUpNat (i := 0) (i' := 0) rfl
  let e₁ := C.extendXIso embeddingUpNat (i := 1) (i' := 1) rfl
  have hw : C.d 0 1 ≫ e₁.inv = e₀.inv ≫ (C.extend embeddingUpNat).d 0 1 := by
    have hd := C.extend_d_eq embeddingUpNat (i := 0) (j := 1) rfl rfl
    change (C.extend embeddingUpNat).d 0 1 = e₀.hom ≫ C.d 0 1 ≫ e₁.inv at hd
    rw [hd]
    simp
  let k := kernel.map (C.d 0 1) ((C.extend embeddingUpNat).d 0 1)
    e₀.inv e₁.inv hw
  have hk : IsIso k := by
    dsimp [k]
    infer_instance
  have he : kernel.lift (C.d 0 1) r hr ≫ k =
      kernel.lift ((C.extend embeddingUpNat).d 0 1) (r ≫ e₀.inv) hr' := by
    apply (cancel_mono (kernel.ι ((C.extend embeddingUpNat).d 0 1))).mp
    simp [k]
  rw [← he]
  infer_instance

/-- The augmentation of Tag 07M9 as a map into the degree-zero row of the flipped Čech
bicomplex. -/
private noncomputable def globalSectionsToCechRowZero
    {κ : Type u} (U : κ → Opens X)
    (L : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ) :
    (globalSectionsComplexFunctor X).obj L ⟶
      rowZero ((cechBicomplexFunctor U).obj L).flip where
  f n := globalSectionsCechRestrictionInt X U (L.X n)
  comm' := by
    intro n m h
    obtain rfl : m = n + 1 := h.symm
    exact (globalSectionsCechRestrictionInt_naturality X U (L.d n (n + 1))).symm

/-- A map into the total complex whose components are the augmentation followed by the
inclusion of the degree-zero summand is the comparison map of Tag 0133, hence a
quasi-isomorphism. -/
theorem quasiIso_of_componentwise_resolution_map
    {A : Type u} [Category A] [Abelian A]
    (K : CochainComplex A ℤ)
    (DA : HomologicalComplex₂ A (up ℤ) (up ℤ))
    [DA.HasTotal (up ℤ)]
    (α : K ⟶ rowZero DA.flip)
    (h : Hypotheses K DA.flip α)
    (f : K ⟶ DA.total (up ℤ))
    (hf : ∀ n : ℤ, f.f n = α.f n ≫ DA.ιTotal (up ℤ) 0 n n (by simp)) :
    QuasiIso f := by
  obtain ⟨_, g, hg, hq⟩ := quasiIso_total_of_resolution_flip K DA α h
  have hfg : f = g := by
    ext n
    exact (hf n).trans (hg n).symm
  rw [hfg]
  exact hq

/-- **The Čech comparison for a bounded below complex of injectives.** For an open covering of
`X`, the canonical map from the complex of global sections of a bounded below complex of
injective sheaves of modules to its total Čech complex is a quasi-isomorphism. -/
theorem quasiIso_globalSectionsToCech_of_injective
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} {I : Type u}
    (U : I → Opens X) (hU : ⊤ = iSup U)
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) (hK : CochainComplex.plus _ K)
    (hKinj : ∀ n : ℤ, Injective (K.X n)) :
    QuasiIso ((globalSectionsToCech X U).app
      ((underlyingPresheafComplexFunctor X R).obj K)) := by
  let L := (underlyingPresheafComplexFunctor X R).obj K
  let DA := (cechBicomplexFunctor U).obj L
  let α := globalSectionsToCechRowZero X U L
  obtain ⟨a, ha⟩ := (CochainComplex.plus_iff _ K).mp hK
  have hzero_neg (p q : ℤ) (hq : q < 0) :
      IsZero (((DA.flip).X p).X q) := by
    show IsZero ((((cechComplexFunctor U).obj (L.X p)).extend
      embeddingUpNat).X q)
    apply HomologicalComplex.isZero_extend_X
    intro i hi
    change (i : ℤ) = q at hi
    omega
  have hzero_below (p q : ℤ) (hp : p < a) :
      IsZero (((DA.flip).X p).X q) := by
    have hz : IsZero (K.X p) := (CochainComplex.isStrictlyGE_iff K a).mp ha p hp
    have hzL : IsZero (L.X p) :=
      Functor.map_isZero
        (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) hz
    have hzC : IsZero ((cechComplexFunctorInt U).obj (L.X p)) :=
      Functor.map_isZero _ hzL
    exact Functor.map_isZero (HomologicalComplex.eval AddCommGrpCat.{u} (up ℤ) q) hzC
  have hfinite : DiagonalFinite DA.flip := by
    intro n
    refine (Set.finite_Icc a n).subset ?_
    intro p hp
    have hpa : a ≤ p := by
      by_contra h
      exact hp (hzero_below p (n - p) (by omega))
    have hpn : p ≤ n := by
      by_contra h
      exact hp (hzero_neg p (n - p) (by omega))
    exact ⟨hpa, hpn⟩
  have hexact (p q : ℤ) (hq : q ≠ 0) : ((DA.flip).X p).ExactAt q := by
    by_cases hneg : q < 0
    · exact HomologicalComplex.ExactAt.of_isZero (hzero_neg p q hneg)
    · have hpos : 0 < q := by omega
      let C := (cechComplexFunctor U).obj (L.X p)
      have hC : C.ExactAt q.toNat := by
        rw [HomologicalComplex.exactAt_iff_isZero_homology]
        exact isZero_cechUnderlyingHomology_of_injective U hU (K.X p)
          q.toNat (by omega)
      have hq' : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (by omega)
      show (C.extend embeddingUpNat).ExactAt q
      exact (C.extend_exactAt_iff embeddingUpNat hq').mpr hC
  have hkernel (p : ℤ) :
      ∃ hα : α.f p ≫ ((DA.flip).X p).d 0 1 = 0,
        IsIso (kernel.lift (((DA.flip).X p).d 0 1) (α.f p) hα) := by
    let C := (cechComplexFunctor U).obj (L.X p)
    have hr : globalSectionsCechRestriction X U (L.X p) 0 ≫ C.d 0 1 = 0 :=
      globalSectionsCechRestriction_d X U (L.X p)
    have : IsIso (kernel.lift (C.d 0 1)
        (globalSectionsCechRestriction X U (L.X p) 0) hr) :=
      isIso_globalSectionsCechRestriction_kernelLift X U hU (K.X p)
    have hr' : (globalSectionsCechRestriction X U (L.X p) 0 ≫
        (C.extendXIso embeddingUpNat (i := 0) (i' := 0) rfl).inv) ≫
        (C.extend embeddingUpNat).d 0 1 = 0 :=
      globalSectionsCechRestrictionInt_d X U (L.X p)
    have : IsIso (kernel.lift ((C.extend embeddingUpNat).d 0 1)
        (globalSectionsCechRestriction X U (L.X p) 0 ≫
          (C.extendXIso embeddingUpNat (i := 0) (i' := 0) rfl).inv) hr') :=
      isIso_extendZero_kernelLift C _ hr hr'
    refine ⟨globalSectionsCechRestrictionInt_d X U (L.X p), ?_⟩
    show IsIso (kernel.lift ((C.extend embeddingUpNat).d 0 1)
      (globalSectionsCechRestriction X U (L.X p) 0 ≫
        (C.extendXIso embeddingUpNat (i := 0) (i' := 0) rfl).inv) _)
    infer_instance
  have hres : Hypotheses ((globalSectionsComplexFunctor X).obj L) DA.flip α :=
    ⟨hfinite, hzero_neg, hexact, hkernel⟩
  exact quasiIso_of_componentwise_resolution_map
    ((globalSectionsComplexFunctor X).obj L) DA α hres _ (globalSectionsToCech_app_f X U L)

end Stacks.Cech
