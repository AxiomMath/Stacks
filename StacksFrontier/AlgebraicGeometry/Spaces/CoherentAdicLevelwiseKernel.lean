module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicCokernel
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicKernelObject
public import StacksFrontier.CategoryTheory.Abelian.QuotientKernelEpi

/-!
# The kernel in `Coh(F, 𝓘)` of a surjection is levelwise

Let `F` be a Noetherian algebraic space, `𝓘 ⊆ 𝒪_F` a quasi-coherent sheaf of ideals and
`α : E ⟶ E'` a morphism of coherent `𝓘`-adic systems.  The kernel
`AlgebraicGeometry.Space.coherentAdicKernel` is not the levelwise kernel, and
`AlgebraicGeometry.Space.coherentAdicKernelToLevelwiseKernel` is the canonical comparison from
its term at `n` to the kernel of `α_n`.  **This file proves that comparison is surjective as soon
as `α` is surjective in `Coh(F, 𝓘)`.**

That is the only thing missing from the abelian structure of Stacks 089P, and it is where the
Artin–Rees stabilization already performed is consumed: past the second stabilization the term of
the kernel at `n` *is* an adic quotient of a stable kernel image, by
`AlgebraicGeometry.Space.stableKernelImageLimitπ_eventually_isIso`, and a stable kernel image is
by construction the image of the kernel of a component of `α` at a higher level.  So the
comparison is surjective as soon as the levelwise kernels themselves have surjective transition
maps, which is the content of
`AlgebraicGeometry.Space.epi_kernelLevelMap`.

Those transitions are surjective because the transitions of a coherent adic system are quotients
by a power of `𝓘`, and a surjection carries that power of the source onto that power of the
target — the content of `AlgebraicGeometry.Space.idealPowerMultiple_ι_comp_eq_zero_of_epi`.  With
that in hand the statement is a diagram lemma in an abelian category and is
`CategoryTheory.Abelian.epi_kernelLift_of_exact_of_epi`.  Only the one-step transition needs the
diagram lemma; the general one is a composite.

## Main definitions

* `AlgebraicGeometry.Space.kernelLevelMap` — the transition map of the levelwise kernels of `α`.

## Main results

* `AlgebraicGeometry.Space.epi_app_of_epi` — a surjection in `Coh(F, 𝓘)` is surjective at every
  level, not only the lowest.
* `AlgebraicGeometry.Space.epi_kernelLevelMap` — **the levelwise kernels of a surjection have
  surjective transition maps.**
* `AlgebraicGeometry.Space.epi_coherentAdicKernelToLevelwiseKernel` — **for a surjection the
  kernel in `Coh(F, 𝓘)` surjects onto the levelwise kernels**, so the term of the kernel at `n`
  has the kernel of `α_n` as a quotient.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed, as throughout this development: the term at
`n` is the Stacks source's `E_{n + 1}`, which is why the annihilating exponent at level `n` is
`n + 1`.

`AlgebraicGeometry.Space.kernelLevelMap` carries its monotonicity hypothesis as an explicit
argument; two instances at the same pair of levels are therefore the same morphism only up to
proof irrelevance, which is why the statements below are applied to the goal by `exact` rather
than by `rw`.

The Noetherian hypothesis is carried as the explicit arguments `hZ`, `hN` and `hIcart`, as
`AlgebraicGeometry.Space.coherentAdicKernel` needs them; the results about the levelwise kernels
alone need none of the three.

## References

* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 08B3](https://stacks.math.columbia.edu/tag/08B3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    {E E' : CoherentAdicSystems B S hS F hF 𝓘}

/-! ### Surjectivity at every level -/

/-- **A surjection in `Coh(F, 𝓘)` is surjective at every level.**  Stacks 08B3 reads surjectivity
off the lowest level, and the inductive step of its proof propagates it upwards. -/
theorem epi_app_of_epi (α : E ⟶ E') (hα : Epi α) (n : ℕ) : Epi (α.hom.app (op n)) := by
  induction n with
  | zero => exact epi_app_zero_of_epi B S hS F hF 𝓘 α hα
  | succ n ih =>
      exact epi_app_succ_of_epi_app B S hS F hF 𝓘 E.property E'.property α.hom n ih

/-! ### The transition maps of the levelwise kernels -/

/-- Transition maps along `homOfLE` compose to the transition map of the composite. -/
private theorem map_homOfLE_op_comp {C : Type*} [Category C] (G : ℕᵒᵖ ⥤ C) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    G.map (homOfLE hbc).op ≫ G.map (homOfLE hab).op = G.map (homOfLE (hab.trans hbc)).op :=
  (G.map_comp _ _).symm

/-- The transition map along `homOfLE` at equal levels is the identity. -/
private theorem map_homOfLE_op_self {C : Type*} [Category C] (G : ℕᵒᵖ ⥤ C) (n : ℕ) :
    G.map (homOfLE (le_refl n)).op = 𝟙 (G.obj (op n)) :=
  G.map_id _

/-- **The transition map of the levelwise kernels of `α`**: the transition map of `E` carries the
kernel of `α_l` into the kernel of `α_n`, by naturality of `α`. -/
def kernelLevelMap (α : E ⟶ E') (n l : ℕ) (h : n ≤ l) :
    kernel (α.hom.app (op l)) ⟶ kernel (α.hom.app (op n)) :=
  kernel.lift (α.hom.app (op n)) (kernel.ι (α.hom.app (op l)) ≫ E.obj.map (homOfLE h).op)
    (Abelian.kernel_ι_comp_comp_eq_zero (α.hom.app (op l)) (α.hom.app (op n))
      (E.obj.map (homOfLE h).op) (E'.obj.map (homOfLE h).op) (α.hom.naturality (homOfLE h).op))

/-- The transition map of the levelwise kernels lies over the transition map of `E`. -/
theorem kernelLevelMap_ι (α : E ⟶ E') (n l : ℕ) (h : n ≤ l) :
    kernelLevelMap B S hS F hF 𝓘 α n l h ≫ kernel.ι (α.hom.app (op n)) =
      kernel.ι (α.hom.app (op l)) ≫ E.obj.map (homOfLE h).op :=
  kernel.lift_ι _ _ _

/-- The transition map of the levelwise kernels at equal levels is the identity. -/
theorem kernelLevelMap_self (α : E ⟶ E') (n : ℕ) :
    kernelLevelMap B S hS F hF 𝓘 α n n le_rfl = 𝟙 _ := by
  refine (cancel_mono (kernel.ι (α.hom.app (op n)))).mp ?_
  rw [kernelLevelMap_ι, map_homOfLE_op_self, Category.comp_id, Category.id_comp]

/-- The transition maps of the levelwise kernels are functorial. -/
theorem kernelLevelMap_comp (α : E ⟶ E') (n k l : ℕ) (hnk : n ≤ k) (hkl : k ≤ l) :
    kernelLevelMap B S hS F hF 𝓘 α k l hkl ≫ kernelLevelMap B S hS F hF 𝓘 α n k hnk =
      kernelLevelMap B S hS F hF 𝓘 α n l (hnk.trans hkl) := by
  refine (cancel_mono (kernel.ι (α.hom.app (op n)))).mp ?_
  rw [Category.assoc, kernelLevelMap_ι, ← Category.assoc, kernelLevelMap_ι, Category.assoc,
    map_homOfLE_op_comp, kernelLevelMap_ι]

/-- **The one-step transition map of the levelwise kernels of a surjection is surjective.**

The transition `E_{n + 1} ⟶ E_n` is the quotient by `𝓘 ^ (n + 1) E_{n + 1}`, and likewise for
`E'`; since `α_{n + 1}` is surjective it carries `𝓘 ^ (n + 1) E_{n + 1}` onto
`𝓘 ^ (n + 1) E'_{n + 1}`, which is exactly the hypothesis of
`CategoryTheory.Abelian.epi_kernelLift_of_exact_of_epi`. -/
theorem epi_kernelLevelMap_succ (α : E ⟶ E') (hα : Epi α) (n : ℕ) :
    Epi (kernelLevelMap B S hS F hF 𝓘 α n (n + 1) (Nat.le_succ n)) := by
  have _hepi : Epi (α.hom.app (op (n + 1))) := epi_app_of_epi B S hS F hF 𝓘 α hα (n + 1)
  have _hp : Epi (E.obj.map (homOfLE (Nat.le_succ n)).op) :=
    epi_map_le_succ B S hS F hF 𝓘 E.property n
  obtain ⟨e, he⟩ := E'.property.2.2 n
  have hzero : (idealPowerMultiple B S hS F hF 𝓘 (n + 1) (E'.obj.obj (op (n + 1)))).ι ≫
      E'.obj.map (homOfLE (Nat.le_succ n)).op = 0 :=
    idealPowerMultiple_ι_comp_map_succ_eq_zero B S hS F hF 𝓘 E'.property n
  have hcolim : IsColimit (CokernelCofork.ofπ
      (E'.obj.map (homOfLE (Nat.le_succ n)).op) hzero) :=
    IsColimit.ofIsoColimit (cokernelIsCokernel _) (Cofork.ext e he)
  have hex : (ShortComplex.mk
      ((idealPowerMultiple B S hS F hF 𝓘 (n + 1) (E'.obj.obj (op (n + 1)))).ι)
      (E'.obj.map (homOfLE (Nat.le_succ n)).op) hzero).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ hcolim
  have hu' : (idealPowerMultiple B S hS F hF 𝓘 (n + 1) (E'.obj.obj (op (n + 1)))).ι ≫
      cokernel.π ((idealPowerMultiple B S hS F hF 𝓘 (n + 1) (E.obj.obj (op (n + 1)))).ι ≫
        α.hom.app (op (n + 1))) = 0 :=
    idealPowerMultiple_ι_comp_eq_zero_of_epi B S hS F hF 𝓘 (n + 1) (α.hom.app (op (n + 1)))
      (cokernel.π _) (by rw [← Category.assoc]; exact cokernel.condition _)
  exact Abelian.epi_kernelLift_of_exact_of_epi
    ((idealPowerMultiple B S hS F hF 𝓘 (n + 1) (E.obj.obj (op (n + 1)))).ι)
    ((idealPowerMultiple B S hS F hF 𝓘 (n + 1) (E'.obj.obj (op (n + 1)))).ι)
    (α.hom.app (op (n + 1))) (α.hom.app (op n)) (E.obj.map (homOfLE (Nat.le_succ n)).op)
    (E'.obj.map (homOfLE (Nat.le_succ n)).op) (α.hom.naturality (homOfLE (Nat.le_succ n)).op)
    (idealPowerMultiple_ι_comp_map_succ_eq_zero B S hS F hF 𝓘 E.property n) hzero hex hu'

/-- **The levelwise kernels of a surjection have surjective transition maps.**  The general
transition is the composite of the one-step ones. -/
theorem epi_kernelLevelMap (α : E ⟶ E') (hα : Epi α) (n l : ℕ) (h : n ≤ l) :
    Epi (kernelLevelMap B S hS F hF 𝓘 α n l h) := by
  induction l, h using Nat.le_induction with
  | base =>
      have hbase : Epi (kernelLevelMap B S hS F hF 𝓘 α n n le_rfl) := by
        rw [kernelLevelMap_self B S hS F hF 𝓘 α n]
        infer_instance
      exact hbase
  | succ l hl ih =>
      have _hih := ih
      have _hsucc := epi_kernelLevelMap_succ B S hS F hF 𝓘 α hα l
      have hgoal : Epi (kernelLevelMap B S hS F hF 𝓘 α n (l + 1) (hl.trans (Nat.le_succ l))) := by
        rw [← kernelLevelMap_comp B S hS F hF 𝓘 α n l (l + 1) hl (Nat.le_succ l)]
        exact epi_comp _ _
      exact hgoal

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ F)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {E E' : CoherentAdicSystems B S hS F hF 𝓘}

/-! ### The comparison with the levelwise kernel -/

/-- **The surjection of the levelwise kernel at the stabilization level onto the stable kernel
image.**  The stable kernel image at level `m` is by construction the image of the kernel of `α`
at the stabilization level of `E_m`. -/
def kernelToStableKernelImage (α : E ⟶ E') (m : ℕ) :
    kernel (α.hom.app (op (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m))) ⟶
      stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m :=
  Abelian.factorThruImage
    (kernel.ι (α.hom.app (op (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m))) ≫
      E.obj.map (homOfLE (le_kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)).op)

/-- The surjection onto the stable kernel image is surjective, being a canonical factorization
through an image. -/
theorem epi_kernelToStableKernelImage (α : E ⟶ E') (m : ℕ) :
    Epi (kernelToStableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m) :=
  inferInstanceAs (Epi (Abelian.factorThruImage
    (kernel.ι (α.hom.app (op (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m))) ≫
      E.obj.map (homOfLE (le_kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)).op)))

/-- The surjection onto the stable kernel image lies over the transition map of `E`. -/
theorem kernelToStableKernelImage_comp (α : E ⟶ E') (m : ℕ) :
    kernelToStableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m ≫
        stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m =
      kernel.ι (α.hom.app (op (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m))) ≫
        E.obj.map (homOfLE (le_kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)).op :=
  Abelian.image.fac _

/-- The component at `n` of the inclusion of the kernel into `E` factors through the adic quotient
of the stable kernel image at any image level above `n`. -/
theorem coherentAdicKernelι_app_eq (α : E ⟶ E') (n m : ℕ) (h : n ≤ m) :
    (coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart α).hom.app (op n) =
      stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n m ≫
        stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n m h :=
  (stableKernelImageLimitπ_comp_toLevel B S hS F hF 𝓘 hZ hN hIcart α n m h).symm

/-- **The comparison from an adic quotient of a stable kernel image to the levelwise kernel.**
The comparison to `E_n` is annihilated by `α_n`, so it factors through the kernel of `α_n`. -/
def stableKernelImageToLevelwiseKernel (α : E ⟶ E') (n m : ℕ) (h : n ≤ m) :
    idealPowerQuotient B S hS F hF 𝓘 (n + 1)
        (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m) ⟶ kernel (α.hom.app (op n)) :=
  kernel.lift (α.hom.app (op n))
    (stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n m h)
    (stableKernelImageCompletionToLevel_comp_alpha B S hS F hF 𝓘 hZ hN hIcart α n m h)

/-- The comparison with the levelwise kernel lies over the comparison to `E_n`. -/
theorem stableKernelImageToLevelwiseKernel_ι (α : E ⟶ E') (n m : ℕ) (h : n ≤ m) :
    stableKernelImageToLevelwiseKernel B S hS F hF 𝓘 hZ hN hIcart α n m h ≫
        kernel.ι (α.hom.app (op n)) =
      stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n m h :=
  kernel.lift_ι _ _ _

/-- **The transition map of the levelwise kernels factors through the adic quotient of the stable
kernel image.**  The kernel of `α` at the stabilization level surjects onto the stable kernel
image at level `m`; composing with the quotient projection and the comparison to the kernel of
`α_n` recovers the transition `ker α_l ⟶ ker α_n`. -/
theorem kernelToStableKernelImage_comp_toLevelwiseKernel (α : E ⟶ E') (n m : ℕ) (h : n ≤ m) :
    kernelToStableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m ≫
        (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
              (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m)).ι ≫
          stableKernelImageToLevelwiseKernel B S hS F hF 𝓘 hZ hN hIcart α n m h) =
      kernelLevelMap B S hS F hF 𝓘 α n
        (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)
        (h.trans (le_kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)) := by
  refine (cancel_mono (kernel.ι (α.hom.app (op n)))).mp ?_
  rw [kernelLevelMap_ι, Category.assoc, Category.assoc, stableKernelImageToLevelwiseKernel_ι,
    stableKernelImageCompletionToLevel_fac, ← Category.assoc,
    kernelToStableKernelImage_comp B S hS F hF 𝓘 hZ hN hIcart α m, Category.assoc,
    map_homOfLE_op_comp]

/-- **For a surjection the adic quotient of a stable kernel image surjects onto the levelwise
kernel.**  The transition `ker α_l ⟶ ker α_n` is surjective by
`AlgebraicGeometry.Space.epi_kernelLevelMap`, and it factors through that adic quotient. -/
theorem epi_stableKernelImageToLevelwiseKernel (α : E ⟶ E') (hα : Epi α) (n m : ℕ) (h : n ≤ m) :
    Epi (stableKernelImageToLevelwiseKernel B S hS F hF 𝓘 hZ hN hIcart α n m h) := by
  have _hw : Epi (kernelLevelMap B S hS F hF 𝓘 α n
      (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)
      (h.trans (le_kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m))) :=
    epi_kernelLevelMap B S hS F hF 𝓘 α hα n _ _
  have _hs : Epi (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
        (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m)).ι ≫
      stableKernelImageToLevelwiseKernel B S hS F hF 𝓘 hZ hN hIcart α n m h) :=
    epi_of_epi_fac
      (kernelToStableKernelImage_comp_toLevelwiseKernel B S hS F hF 𝓘 hZ hN hIcart α n m h)
  exact epi_of_epi_fac (f := cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
    (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m)).ι) rfl

/-- **For a surjection the levelwise kernels are controlled by the kernel in `Coh(F, 𝓘)`.**  A
morphism out of `E_n` which the inclusion of the kernel annihilates is annihilated by the kernel
of `α_n`.

Past the second stabilization the term of the kernel at `n` is the `(n + 1)`-st adic quotient of
the stable kernel image at an image level `m`, and that adic quotient surjects onto the kernel of
`α_n` by `AlgebraicGeometry.Space.epi_stableKernelImageToLevelwiseKernel`; so the two
annihilation conditions are the same one, read through two epimorphisms.

This is the form in which the abelian structure consumes the stabilization: it says that `α_n` is
a cokernel of the component at `n` of the inclusion of the kernel. -/
theorem kernel_ι_comp_eq_zero_of_epi (α : E ⟶ E') (hα : Epi α) (n : ℕ)
    {T : Modules.{u, u} B S hS F hF} (t : E.obj.obj (op n) ⟶ T)
    (ht : (coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart α).hom.app (op n) ≫ t = 0) :
    kernel.ι (α.hom.app (op n)) ≫ t = 0 := by
  obtain ⟨c, hc⟩ := stableKernelImageLimitπ_eventually_isIso B S hS F hF 𝓘 hZ hN hIcart α n
  have _hiso := hc (n + c) le_rfl
  have _hepiπ : Epi (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n (n + c)) :=
    @IsIso.epi_of_iso _ _ _ _ _ _hiso
  have hnm : n ≤ n + c := Nat.le_add_right n c
  have _hepi : Epi (stableKernelImageToLevelwiseKernel B S hS F hF 𝓘 hZ hN hIcart α n (n + c)
      hnm) :=
    epi_stableKernelImageToLevelwiseKernel B S hS F hF 𝓘 hZ hN hIcart α hα n (n + c) hnm
  have h1 : stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n (n + c) ≫
      (stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n (n + c) hnm ≫ t) = 0 :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ t)
        (coherentAdicKernelι_app_eq B S hS F hF 𝓘 hZ hN hIcart α n (n + c) hnm).symm).trans ht)
  have h2 : stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n (n + c) hnm ≫
      t = 0 :=
    (cancel_epi (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n (n + c))).mp
      (h1.trans comp_zero.symm)
  have h3 : stableKernelImageToLevelwiseKernel B S hS F hF 𝓘 hZ hN hIcart α n (n + c) hnm ≫
      (kernel.ι (α.hom.app (op n)) ≫ t) = 0 :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ t)
        (stableKernelImageToLevelwiseKernel_ι B S hS F hF 𝓘 hZ hN hIcart α n (n + c)
          hnm)).trans h2)
  exact (cancel_epi (stableKernelImageToLevelwiseKernel B S hS F hF 𝓘 hZ hN hIcart α n (n + c)
    hnm)).mp (h3.trans comp_zero.symm)

end AlgebraicGeometry.Space

end
