module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicBiproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicLevelwiseKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicNormalMono

/-!
# The category of coherent adic systems on a Noetherian algebraic space is abelian

Let `F` be a Noetherian algebraic space over a scheme `S` and let `𝓘 ⊆ 𝒪_F` be a quasi-coherent
sheaf of ideals.  **The category `AlgebraicGeometry.Space.CoherentAdicSystems` of coherent
`𝓘`-adic systems on `F` is abelian**, part (1) of Stacks 089P.

The criterion used is the definition itself: a preadditive category with finite products, kernels
and cokernels in which every monomorphism is a kernel and every epimorphism is a cokernel.  Four
of those five are already available without any Noetherian hypothesis —
`AlgebraicGeometry.Space.hasFiniteProducts_coherentAdicSystems`,
`AlgebraicGeometry.Space.hasCokernels_coherentAdicSystems` and preadditivity of a full subcategory
of a functor category — and the kernels are
`AlgebraicGeometry.Space.hasKernels_coherentAdicSystems`.  The two normality conditions are what
this file supplies.

**Every epimorphism is a cokernel.**  The cokernel in `Coh(F, 𝓘)` is levelwise, so it suffices
that at each level `α_n` is a cokernel of the component at `n` of the inclusion of the kernel.
That is exactly `AlgebraicGeometry.Space.kernel_ι_comp_eq_zero_of_epi`: a morphism out of `E_n`
annihilated by the kernel's inclusion is annihilated by the kernel of `α_n`, which the levelwise
abelian structure then descends along `α_n`.

**Every monomorphism is a kernel.**  A monomorphism of `Coh(F, 𝓘)` need not be injective level by
level, so the kernel of the cokernel is compared with `α` directly.  Write `π` for the projection
onto the levelwise cokernel of `α` and `λ` for the induced morphism from `E` to the kernel of `π`.
Then

* `λ` is **surjective**, and this holds for every `α`: by Stacks 08B3 it is enough to check the
  lowest level, where the stabilization identifies the term of the kernel of `π` with an adic
  quotient of a stable kernel image of `π`, and the stable kernel image of `π` at level `m` is the
  levelwise image of `α_m` — the kernel of `π_m` being that image, because the cokernel is
  levelwise.
* `λ` is **injective**, when `α` is: it is then a monomorphism of `Coh(F, 𝓘)`, so its kernel
  object vanishes, and since it is surjective
  `AlgebraicGeometry.Space.kernel_ι_comp_eq_zero_of_epi` turns that into injectivity at every
  level.

So `λ` is an isomorphism and `α` is the kernel of `π`.

## Main definitions

* `AlgebraicGeometry.Space.coherentAdicImageLift` — the morphism from `E` to the kernel of the
  projection onto the cokernel of `α`.
* `AlgebraicGeometry.Space.coherentAdicNormalEpi` and
  `AlgebraicGeometry.Space.coherentAdicNormalMono` — a surjection presented as a cokernel, an
  injection presented as a kernel.
* `AlgebraicGeometry.Space.abelian_coherentAdicSystems` — **`Coh(F, 𝓘)` is abelian.**

## Main results

* `AlgebraicGeometry.Space.epi_coherentAdicImageLift` — **the morphism to the kernel of the
  cokernel projection is surjective**, for every morphism of coherent adic systems.
* `AlgebraicGeometry.Space.isIso_coherentAdicImageLift` — and invertible when the morphism is a
  monomorphism.
* `AlgebraicGeometry.Space.isNormalEpiCategory_coherentAdicSystems` and
  `AlgebraicGeometry.Space.isNormalMonoCategory_coherentAdicSystems` — every epimorphism is a
  cokernel, every monomorphism is a kernel.
* `AlgebraicGeometry.Space.isIso_coimageImageComparison` — the coimage-image comparison of a
  morphism of coherent adic systems is invertible, the form of the abelian structure the Stacks
  Project takes as its definition.

## Implementation notes

The Noetherian hypothesis is carried as the explicit arguments `hZ`, `hN` and `hIcart`, as
`AlgebraicGeometry.Space.hasKernels_coherentAdicSystems` is; `Abelian` is therefore produced by a
definition taking those three arguments rather than by an instance, and every statement below
which mentions a kernel takes them too.

The system is indexed by `ℕᵒᵖ` and is zero-indexed: the term at `n` is the Stacks source's
`E_{n + 1}`, so the lowest level is `Opposite.op 0`.

The levelwise comparison of the kernel of the cokernel projection with the image is made through
`AlgebraicGeometry.Space.cokernelObjIso`, since the component at a level of the projection onto a
levelwise cokernel is the projection onto the cokernel of the component only up to that
identification.

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
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ F)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {E E' : CoherentAdicSystems B S hS F hF 𝓘}

/-! ### Every epimorphism is a cokernel -/

/-- If a composite of morphisms of coherent adic systems vanishes, it does so at every level. -/
private theorem app_comp_eq_zero_of_comp_eq_zero {A A' A'' : CoherentAdicSystems B S hS F hF 𝓘}
    (f : A ⟶ A') (g : A' ⟶ A'') (h : f ≫ g = 0) (n : ℕᵒᵖ) :
    f.hom.app n ≫ g.hom.app n = 0 :=
  congrArg (fun z : A ⟶ A'' => z.hom.app n) h

/-- The levelwise form of the annihilation hypothesis: a morphism of coherent adic systems which
the inclusion of the kernel annihilates does so at every level. -/
theorem coherentAdicKernelι_app_comp_eq_zero (α : E ⟶ E')
    {T : CoherentAdicSystems B S hS F hF 𝓘} (t : E ⟶ T)
    (ht : coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart α ≫ t = 0) (n : ℕ) :
    (coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart α).hom.app (op n) ≫ t.hom.app (op n) = 0 :=
  app_comp_eq_zero_of_comp_eq_zero B S hS F hF 𝓘 _ t ht _

/-- **A morphism of coherent adic systems annihilated by the inclusion of the kernel of a
surjection factors through that surjection.**

At each level the kernel of `α_n` annihilates the morphism, by
`AlgebraicGeometry.Space.kernel_ι_comp_eq_zero_of_epi`, and in the abelian category of
`𝒪_F`-modules a surjection is the cokernel of its kernel; the factorizations are unique at each
level, which makes them natural. -/
theorem exists_desc_of_coherentAdicKernelι_comp_eq_zero (α : E ⟶ E') (hα : Epi α)
    {T : CoherentAdicSystems B S hS F hF 𝓘} (t : E ⟶ T)
    (ht : coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart α ≫ t = 0) :
    ∃ s : E' ⟶ T, α ≫ s = t := by
  have hepi : ∀ X : ℕᵒᵖ, Epi (α.hom.app X) :=
    fun X => epi_app_of_epi B S hS F hF 𝓘 α hα X.unop
  have hz : ∀ X : ℕᵒᵖ, kernel.ι (α.hom.app X) ≫ t.hom.app X = 0 :=
    fun X => kernel_ι_comp_eq_zero_of_epi B S hS F hF 𝓘 hZ hN hIcart α hα X.unop
      (t.hom.app X)
      (coherentAdicKernelι_app_comp_eq_zero B S hS F hF 𝓘 hZ hN hIcart α t ht X.unop)
  refine ⟨ObjectProperty.homMk
    { app := fun X => Abelian.epiDesc (α.hom.app X) (t.hom.app X) (hz X)
      naturality := fun X Y g => ?_ }, ?_⟩
  · refine (cancel_epi (α.hom.app X)).mp ?_
    rw [← Category.assoc, ← α.hom.naturality, Category.assoc, Abelian.comp_epiDesc,
      ← Category.assoc, Abelian.comp_epiDesc]
    exact t.hom.naturality g
  · refine ObjectProperty.hom_ext (IsCoherentAdicSystem B S hS F hF 𝓘) (NatTrans.ext ?_)
    funext X
    exact Abelian.comp_epiDesc (α.hom.app X) (t.hom.app X) (hz X)

/-- **A surjection of coherent adic systems on a Noetherian algebraic space is the cokernel of its
kernel.** -/
@[instance_reducible]
def coherentAdicNormalEpi (α : E ⟶ E') (hα : Epi α) : NormalEpi α where
  W := coherentAdicKernel B S hS F hF 𝓘 hZ hN hIcart α
  g := coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart α
  w := coherentAdicKernelι_comp B S hS F hF 𝓘 hZ hN hIcart α
  isColimit :=
    have : Epi α := hα
    CokernelCofork.IsColimit.ofπ' _ _ fun {_} k hk =>
      ⟨(exists_desc_of_coherentAdicKernelι_comp_eq_zero B S hS F hF 𝓘 hZ hN hIcart α hα k
          hk).choose,
        (exists_desc_of_coherentAdicKernelι_comp_eq_zero B S hS F hF 𝓘 hZ hN hIcart α hα k
          hk).choose_spec⟩

include hZ hN hIcart in
/-- **Every epimorphism of `Coh(F, 𝓘)` is a kernel's cokernel.** -/
theorem isNormalEpiCategory_coherentAdicSystems :
    IsNormalEpiCategory (CoherentAdicSystems B S hS F hF 𝓘) where
  normalEpiOfEpi α _ :=
    ⟨coherentAdicNormalEpi B S hS F hF 𝓘 hZ hN hIcart α inferInstance⟩

/-! ### The kernel of the cokernel projection, level by level -/

/-- A morphism of coherent adic systems is annihilated by the projection onto its cokernel at
every level. -/
theorem coherentAdicCokernelπ_app_comp (α : E ⟶ E') (n : ℕᵒᵖ) :
    α.hom.app n ≫ (coherentAdicCokernelπ B S hS F hF 𝓘 α).hom.app n = 0 :=
  app_comp_eq_zero_of_comp_eq_zero B S hS F hF 𝓘 _ _ (comp_coherentAdicCokernelπ B S hS F hF 𝓘 α) n

/-- **At every level the component of `α` and the component of the projection onto its cokernel
form an exact pair.**  The cokernel in `Coh(F, 𝓘)` is levelwise, so the second component is the
projection onto the cokernel of the first up to `AlgebraicGeometry.Space.cokernelObjIso`. -/
theorem exact_app_coherentAdicCokernelπ (α : E ⟶ E') (n : ℕᵒᵖ) :
    (ShortComplex.mk (α.hom.app n) ((coherentAdicCokernelπ B S hS F hF 𝓘 α).hom.app n)
      (coherentAdicCokernelπ_app_comp B S hS F hF 𝓘 α n)).Exact :=
  Abelian.exact_of_comp_iso_eq_cokernel_π (α.hom.app n)
    ((coherentAdicCokernelπ B S hS F hF 𝓘 α).hom.app n) (cokernelObjIso B S hS F hF α.hom n)
    (app_comp_cokernelObjIso_hom B S hS F hF α.hom n) _

/-- **The canonical morphism from `E_m` to the kernel of the component at `m` of the cokernel
projection.** -/
def coherentAdicCokernelπKernelLift (α : E ⟶ E') (m : ℕ) :
    E.obj.obj (op m) ⟶ kernel ((coherentAdicCokernelπ B S hS F hF 𝓘 α).hom.app (op m)) :=
  kernel.lift _ (α.hom.app (op m)) (coherentAdicCokernelπ_app_comp B S hS F hF 𝓘 α (op m))

/-- The canonical morphism to the kernel of the cokernel projection lies over `α_m`. -/
theorem coherentAdicCokernelπKernelLift_ι (α : E ⟶ E') (m : ℕ) :
    coherentAdicCokernelπKernelLift B S hS F hF 𝓘 α m ≫
        kernel.ι ((coherentAdicCokernelπ B S hS F hF 𝓘 α).hom.app (op m)) =
      α.hom.app (op m) :=
  kernel.lift_ι _ _ _

/-- **The canonical morphism from `E_m` to the kernel of the component at `m` of the cokernel
projection is surjective**, that kernel being the levelwise image of `α_m`. -/
theorem epi_coherentAdicCokernelπKernelLift (α : E ⟶ E') (m : ℕ) :
    Epi (coherentAdicCokernelπKernelLift B S hS F hF 𝓘 α m) :=
  Abelian.epi_kernelLift_of_exact _ (exact_app_coherentAdicCokernelπ B S hS F hF 𝓘 α (op m))

/-! ### The stable kernel images of the cokernel projection -/

/-- **The comparison from the stable kernel image at level `m` of the cokernel projection to the
kernel of its component at `m`.** -/
def stableKernelImageToKernelCokernelπ (α : E ⟶ E') (m : ℕ) :
    stableKernelImage B S hS F hF 𝓘 hZ hN hIcart
        (coherentAdicCokernelπ B S hS F hF 𝓘 α) m ⟶
      kernel ((coherentAdicCokernelπ B S hS F hF 𝓘 α).hom.app (op m)) :=
  kernel.lift _ (stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart
      (coherentAdicCokernelπ B S hS F hF 𝓘 α) m)
    (stableKernelImageIncl_comp B S hS F hF 𝓘 hZ hN hIcart
      (coherentAdicCokernelπ B S hS F hF 𝓘 α) m)

/-- The comparison lies over the two inclusions into `E'_m`. -/
theorem stableKernelImageToKernelCokernelπ_ι (α : E ⟶ E') (m : ℕ) :
    stableKernelImageToKernelCokernelπ B S hS F hF 𝓘 hZ hN hIcart α m ≫
        kernel.ι ((coherentAdicCokernelπ B S hS F hF 𝓘 α).hom.app (op m)) =
      stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart
        (coherentAdicCokernelπ B S hS F hF 𝓘 α) m :=
  kernel.lift_ι _ _ _

/-- The comparison is injective, lying over an inclusion. -/
theorem mono_stableKernelImageToKernelCokernelπ (α : E ⟶ E') (m : ℕ) :
    Mono (stableKernelImageToKernelCokernelπ B S hS F hF 𝓘 hZ hN hIcart α m) :=
  mono_of_mono_fac (stableKernelImageToKernelCokernelπ_ι B S hS F hF 𝓘 hZ hN hIcart α m)

/-- Through the comparison, the factorization of `α` through the stable kernel image is the
canonical morphism to the kernel of the cokernel projection. -/
theorem stableKernelImageLift_comp_comparison (α : E ⟶ E') (m : ℕ) :
    stableKernelImageLift B S hS F hF 𝓘 hZ hN hIcart
          (coherentAdicCokernelπ B S hS F hF 𝓘 α) α
          (comp_coherentAdicCokernelπ B S hS F hF 𝓘 α) m ≫
        stableKernelImageToKernelCokernelπ B S hS F hF 𝓘 hZ hN hIcart α m =
      coherentAdicCokernelπKernelLift B S hS F hF 𝓘 α m := by
  refine (cancel_mono (kernel.ι ((coherentAdicCokernelπ B S hS F hF 𝓘 α).hom.app (op m)))).mp ?_
  rw [Category.assoc, stableKernelImageToKernelCokernelπ_ι, stableKernelImageLift_ι,
    coherentAdicCokernelπKernelLift_ι]

/-- **The stable kernel image of the cokernel projection at level `m` is the image of `α_m`**: the
comparison with the kernel of the component of the cokernel projection is invertible. -/
theorem isIso_stableKernelImageToKernelCokernelπ (α : E ⟶ E') (m : ℕ) :
    IsIso (stableKernelImageToKernelCokernelπ B S hS F hF 𝓘 hZ hN hIcart α m) :=
  have _hm := mono_stableKernelImageToKernelCokernelπ B S hS F hF 𝓘 hZ hN hIcart α m
  have _hk := epi_coherentAdicCokernelπKernelLift B S hS F hF 𝓘 α m
  have _he : Epi (stableKernelImageToKernelCokernelπ B S hS F hF 𝓘 hZ hN hIcart α m) :=
    epi_of_epi_fac (stableKernelImageLift_comp_comparison B S hS F hF 𝓘 hZ hN hIcart α m)
  isIso_of_mono_of_epi _

/-- **`E_m` surjects onto the stable kernel image at level `m` of the cokernel projection.** -/
theorem epi_stableKernelImageLift_cokernelπ (α : E ⟶ E') (m : ℕ) :
    Epi (stableKernelImageLift B S hS F hF 𝓘 hZ hN hIcart
      (coherentAdicCokernelπ B S hS F hF 𝓘 α) α
      (comp_coherentAdicCokernelπ B S hS F hF 𝓘 α) m) := by
  have _hiso := isIso_stableKernelImageToKernelCokernelπ B S hS F hF 𝓘 hZ hN hIcart α m
  have _hk := epi_coherentAdicCokernelπKernelLift B S hS F hF 𝓘 α m
  rw [← epi_comp_iff_of_isIso _
    (stableKernelImageToKernelCokernelπ B S hS F hF 𝓘 hZ hN hIcart α m),
    stableKernelImageLift_comp_comparison]
  exact _hk

/-! ### The morphism to the kernel of the cokernel projection -/

/-- The underlying morphism of inverse systems of
`AlgebraicGeometry.Space.coherentAdicImageLift`. -/
def coherentAdicImageLiftHom (α : E ⟶ E') :
    E.obj ⟶ stableKernelImageLimitSystem B S hS F hF 𝓘 hZ hN hIcart
      (coherentAdicCokernelπ B S hS F hF 𝓘 α) :=
  limit.lift _ (stableKernelImageLiftCone B S hS F hF 𝓘 hZ hN hIcart
    (coherentAdicCokernelπ B S hS F hF 𝓘 α) α (comp_coherentAdicCokernelπ B S hS F hF 𝓘 α))

/-- **The morphism from `E` to the kernel of the projection onto the cokernel of `α`**, the
factorization of `α` through that kernel. -/
def coherentAdicImageLift (α : E ⟶ E') :
    E ⟶ coherentAdicKernel B S hS F hF 𝓘 hZ hN hIcart
      (coherentAdicCokernelπ B S hS F hF 𝓘 α) :=
  ObjectProperty.homMk (coherentAdicImageLiftHom B S hS F hF 𝓘 hZ hN hIcart α)

/-- The factorization of `α` through the kernel of the cokernel projection lies over `α`. -/
theorem coherentAdicImageLift_comp (α : E ⟶ E') :
    coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α ≫
        coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart
          (coherentAdicCokernelπ B S hS F hF 𝓘 α) = α :=
  ObjectProperty.hom_ext (IsCoherentAdicSystem B S hS F hF 𝓘)
    (stableKernelImageLiftCone_lift_fac B S hS F hF 𝓘 hZ hN hIcart
      (coherentAdicCokernelπ B S hS F hF 𝓘 α) α (comp_coherentAdicCokernelπ B S hS F hF 𝓘 α))

/-- **The factorization of `α` through the kernel of the cokernel projection is surjective at the
lowest level.**

Past the stabilization the term at the lowest level of that kernel is an adic quotient of a
stable kernel image of the cokernel projection, and `E` surjects onto that stable kernel image by
`AlgebraicGeometry.Space.epi_stableKernelImageLift_cokernelπ`. -/
theorem epi_coherentAdicImageLiftHom_app_zero (α : E ⟶ E') :
    Epi ((coherentAdicImageLiftHom B S hS F hF 𝓘 hZ hN hIcart α).app (op 0)) := by
  obtain ⟨c, hc⟩ := stableKernelImageLimitπ_eventually_isIso B S hS F hF 𝓘 hZ hN hIcart
    (coherentAdicCokernelπ B S hS F hF 𝓘 α) 0
  have _hiso := hc (0 + c) le_rfl
  have _hl := epi_stableKernelImageLift_cokernelπ B S hS F hF 𝓘 hZ hN hIcart α (0 + c)
  have _hmap : Epi (E.obj.map (homOfLE (le_refl (0 + c))).op) := by
    rw [show (homOfLE (le_refl (0 + c))).op = 𝟙 (op (0 + c)) from rfl, E.obj.map_id]
    infer_instance
  have _hrhs : Epi (E.obj.map (homOfLE (le_refl (0 + c))).op ≫
      stableKernelImageLift B S hS F hF 𝓘 hZ hN hIcart
          (coherentAdicCokernelπ B S hS F hF 𝓘 α) α
          (comp_coherentAdicCokernelπ B S hS F hF 𝓘 α) (0 + c) ≫
        cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (0 + 1)
          (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart
            (coherentAdicCokernelπ B S hS F hF 𝓘 α) (0 + c))).ι) :=
    epi_comp _ _
  have _hQ : Epi (stableKernelImageQuotientLift B S hS F hF 𝓘 hZ hN hIcart
      (coherentAdicCokernelπ B S hS F hF 𝓘 α) α
      (comp_coherentAdicCokernelπ B S hS F hF 𝓘 α) 0 (0 + c)) :=
    epi_of_epi_fac (stableKernelImageQuotientLift_fac B S hS F hF 𝓘 hZ hN hIcart
      (coherentAdicCokernelπ B S hS F hF 𝓘 α) α
      (comp_coherentAdicCokernelπ B S hS F hF 𝓘 α) 0 (0 + c) (0 + c) (Nat.zero_le _)
      (le_refl (0 + c)))
  have hπ : (coherentAdicImageLiftHom B S hS F hF 𝓘 hZ hN hIcart α).app (op 0) ≫
      stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart
        (coherentAdicCokernelπ B S hS F hF 𝓘 α) 0 (0 + c) =
      stableKernelImageQuotientLift B S hS F hF 𝓘 hZ hN hIcart
        (coherentAdicCokernelπ B S hS F hF 𝓘 α) α
        (comp_coherentAdicCokernelπ B S hS F hF 𝓘 α) 0 (0 + c) :=
    congrArg (fun g => g.app (op 0))
      (limit.lift_π (stableKernelImageLiftCone B S hS F hF 𝓘 hZ hN hIcart
        (coherentAdicCokernelπ B S hS F hF 𝓘 α) α
        (comp_coherentAdicCokernelπ B S hS F hF 𝓘 α)) (op (0 + c)))
  rw [← epi_comp_iff_of_isIso _ (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart
    (coherentAdicCokernelπ B S hS F hF 𝓘 α) 0 (0 + c)), hπ]
  exact _hQ

/-- **The factorization of `α` through the kernel of the projection onto its cokernel is
surjective**, for every morphism of coherent adic systems.  By Stacks 08B3 it is enough that it be
surjective at the lowest level. -/
theorem epi_coherentAdicImageLift (α : E ⟶ E') :
    Epi (coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α) :=
  epi_of_epi_app_zero B S hS F hF 𝓘 (coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α)
    (epi_coherentAdicImageLiftHom_app_zero B S hS F hF 𝓘 hZ hN hIcart α)

/-! ### Every monomorphism is a kernel -/

/-- **For a monomorphism the factorization through the kernel of the cokernel projection is
invertible.**

It is surjective by `AlgebraicGeometry.Space.epi_coherentAdicImageLift`, and injective: being a
factor of a monomorphism it is a monomorphism of `Coh(F, 𝓘)`, so the inclusion of its kernel
vanishes, and `AlgebraicGeometry.Space.kernel_ι_comp_eq_zero_of_epi` — available because it is
surjective — turns that into the vanishing of the levelwise kernels. -/
theorem isIso_coherentAdicImageLift (α : E ⟶ E') (hα : Mono α) :
    IsIso (coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α) := by
  have hepi : Epi (coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α) :=
    epi_coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α
  have _hα : Mono α := hα
  have hmono : Mono (coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α) :=
    mono_of_mono_fac (coherentAdicImageLift_comp B S hS F hF 𝓘 hZ hN hIcart α)
  have hι0 : coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart
      (coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α) = 0 :=
    zero_of_comp_mono _ (coherentAdicKernelι_comp B S hS F hF 𝓘 hZ hN hIcart
      (coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α))
  have happ : ∀ n : ℕ,
      IsIso ((coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α).hom.app (op n)) := by
    intro n
    have _hepin : Epi ((coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α).hom.app (op n)) :=
      epi_app_of_epi B S hS F hF 𝓘 (coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α) hepi n
    have hz : (coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart
          (coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α)).hom.app (op n) ≫
        𝟙 (E.obj.obj (op n)) = 0 :=
      app_comp_eq_zero_of_comp_eq_zero B S hS F hF 𝓘 _ (𝟙 E) ((Category.comp_id _).trans hι0) _
    have hk := kernel_ι_comp_eq_zero_of_epi B S hS F hF 𝓘 hZ hN hIcart
      (coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α) hepi n (𝟙 (E.obj.obj (op n))) hz
    have _hmonon : Mono ((coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α).hom.app (op n)) :=
      Abelian.mono_of_kernel_ι_eq_zero _ ((Category.comp_id _).symm.trans hk)
    exact isIso_of_mono_of_epi _
  have _happ : ∀ X : ℕᵒᵖ,
      IsIso ((coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α).hom.app X) :=
    fun X => happ X.unop
  have _hhom : IsIso (coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α).hom :=
    NatIso.isIso_of_isIso_app _
  exact ⟨ObjectProperty.homMk
      (inv (coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α).hom),
    ObjectProperty.hom_ext (IsCoherentAdicSystem B S hS F hF 𝓘) (IsIso.hom_inv_id _),
    ObjectProperty.hom_ext (IsCoherentAdicSystem B S hS F hF 𝓘) (IsIso.inv_hom_id _)⟩

/-- **A monomorphism of coherent adic systems on a Noetherian algebraic space is the kernel of the
projection onto its cokernel.** -/
@[instance_reducible]
def coherentAdicNormalMono (α : E ⟶ E') (hα : Mono α) : NormalMono α where
  Z := coherentAdicCokernel B S hS F hF 𝓘 α
  g := coherentAdicCokernelπ B S hS F hF 𝓘 α
  w := comp_coherentAdicCokernelπ B S hS F hF 𝓘 α
  isLimit :=
    have _hiso := isIso_coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α hα
    IsLimit.ofIsoLimit
      (coherentAdicKernelIsLimit B S hS F hF 𝓘 hZ hN hIcart
        (coherentAdicCokernelπ B S hS F hF 𝓘 α))
      (Fork.ext (asIso (coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α)).symm
        ((congrArg (fun z => inv (coherentAdicImageLift B S hS F hF 𝓘 hZ hN hIcart α) ≫ z)
            (coherentAdicImageLift_comp B S hS F hF 𝓘 hZ hN hIcart α).symm).trans
          (IsIso.inv_hom_id_assoc _ _)))

include hZ hN hIcart in
/-- **Every monomorphism of `Coh(F, 𝓘)` is a cokernel's kernel.** -/
theorem isNormalMonoCategory_coherentAdicSystems :
    IsNormalMonoCategory (CoherentAdicSystems B S hS F hF 𝓘) where
  normalMonoOfMono α _ :=
    ⟨coherentAdicNormalMono B S hS F hF 𝓘 hZ hN hIcart α inferInstance⟩

/-! ### The abelian structure -/

/-- **The category `Coh(F, 𝓘)` of coherent adic systems on a Noetherian algebraic space is
abelian.**

It is preadditive, has finite products, kernels and cokernels, and every monomorphism is a kernel
and every epimorphism a cokernel. -/
@[stacks 089P "the category is abelian", instance_reducible]
def abelian_coherentAdicSystems : Abelian (CoherentAdicSystems B S hS F hF 𝓘) :=
  have _hk := hasKernels_coherentAdicSystems B S hS F hF 𝓘 hZ hN hIcart
  have _hm := isNormalMonoCategory_coherentAdicSystems B S hS F hF 𝓘 hZ hN hIcart
  have _he := isNormalEpiCategory_coherentAdicSystems B S hS F hF 𝓘 hZ hN hIcart
  { }

/-- **The coimage-image comparison of a morphism of coherent adic systems on a Noetherian
algebraic space is invertible**, which is the form in which the Stacks Project states the abelian
structure. -/
theorem isIso_coimageImageComparison (α : E ⟶ E') :
    letI := abelian_coherentAdicSystems B S hS F hF 𝓘 hZ hN hIcart
    IsIso (Abelian.coimageImageComparison α) :=
  let := abelian_coherentAdicSystems B S hS F hF 𝓘 hZ hN hIcart
  inferInstance

end AlgebraicGeometry.Space

end
