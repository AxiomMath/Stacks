module

public import Mathlib.CategoryTheory.Abelian.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Transition

/-!
# Levelwise criteria for morphisms of ℓ-adic sheaves

A morphism of ℓ-adic sheaves is an epimorphism exactly when all its components are, and it is a
monomorphism, an isomorphism, a kernel or a cokernel as soon as all its components are. In
particular a morphism with monomorphic components is the kernel of its levelwise cokernel, and
an epimorphism whose levelwise kernel comparisons are epimorphisms is a cokernel.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.epi_iff_app_epi`: epimorphisms are detected levelwise.
* `Stacks.EtaleCohomology.LAdicSheaf.mono_of_app_mono` and `.isIso_iff_app_isIso`:
  monomorphisms and isomorphisms are reflected, respectively detected, levelwise.
* `Stacks.EtaleCohomology.LAdicSheaf.isLimit_kernelFork_of_app` and
  `.isColimit_cokernelCofork_of_app`: a fork or cofork which is a kernel, respectively cokernel,
  at every finite level is one in the category of ℓ-adic sheaves.
* `Stacks.EtaleCohomology.LAdicSheaf.normalMono_of_app_mono`: a morphism with monomorphic
  components is the kernel of its levelwise cokernel.
* `Stacks.EtaleCohomology.LAdicSheaf.normalEpi_of_epi_kernelLift`: an epimorphism admitting a
  morphism whose levelwise kernel comparisons are epimorphisms is the cokernel of that
  morphism.

## References

* [Stacks Project, Tag 03UO](https://stacks.math.columbia.edu/tag/03UO)
* [Stacks Project, Tag 03UM](https://stacks.math.columbia.edu/tag/03UM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [Fact ℓ.Prime] [IsNoetherian X.1]

namespace LAdicSheaf

variable {B X ℓ}

/-- A composite of morphisms of ℓ-adic sheaves vanishes levelwise when it vanishes. -/
public theorem comp_eq_zero_app {F G H : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (g : G ⟶ H)
    (w : f ≫ g = 0) (n : ℕ) : f.app n ≫ g.app n = 0 := by
  simpa only [LAdicSheaf.comp_app, AlgebraicGeometry.SmallEtale.LAdicSheaf.Hom.zero_app] using
    congrArg (fun t : F ⟶ H => t.app n) w

variable (B X ℓ)

/-- Evaluation of an ℓ-adic sheaf at a finite level, as a functor. -/
public def levelEvaluation (n : ℕ) :
    LAdicSheaf.{u, u + 1} B X ℓ ⥤ FiniteLevelSheaf B X ℓ n where
  obj F := F.level n
  map f := f.app n

variable {B X ℓ}

/-- A morphism of ℓ-adic sheaves all of whose components are monomorphisms is a
monomorphism. -/
public theorem mono_of_app_mono {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (hf : ∀ n, Mono (f.app n)) : Mono f :=
  ⟨fun {H} _ _ w => AlgebraicGeometry.SmallEtale.LAdicSheaf.Hom.ext _ _ _ fun n =>
    (hf n).right_cancellation _ _ (congrArg (fun t : H ⟶ G => t.app n) w)⟩

/-- A morphism of ℓ-adic sheaves is an epimorphism exactly when all its components are, the
cokernel being computed levelwise. -/
public theorem epi_iff_app_epi {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) :
    Epi f ↔ ∀ n, Epi (f.app n) := by
  constructor
  · intro hf n
    have hzero : cokernelSystemπ f = 0 := by
      apply (cancel_epi f).1
      simpa using comp_cokernelSystemπ f
    exact Preadditive.epi_of_cokernel_zero
      (congrArg (fun t : G ⟶ cokernelSystem f => t.app n) hzero)
  · exact fun hf => ⟨fun {H} _ _ w => AlgebraicGeometry.SmallEtale.LAdicSheaf.Hom.ext _ _ _
      fun n => (hf n).left_cancellation _ _ (congrArg (fun t : F ⟶ H => t.app n) w)⟩

/-- The inverse of a morphism of ℓ-adic sheaves whose components are all isomorphisms. -/
public def inverseOfAppIsIso {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (hf : ∀ n, IsIso (f.app n)) : G ⟶ F where
  app n := inv (f.app n)
  naturality n := by
    have := hf n
    have := hf (n + 1)
    apply (cancel_epi (f.app (n + 1))).1
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    rw [f.naturality n, Category.assoc, ← Functor.map_comp]
    simp

/-- A morphism of ℓ-adic sheaves is an isomorphism exactly when all its components are. -/
public theorem isIso_iff_app_isIso {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) :
    IsIso f ↔ ∀ n, IsIso (f.app n) :=
  ⟨fun _ n => (levelEvaluation B X ℓ n).map_isIso f, fun hf =>
    ⟨⟨inverseOfAppIsIso f hf,
      AlgebraicGeometry.SmallEtale.LAdicSheaf.Hom.ext _ _ _ fun n =>
        have := hf n
        IsIso.hom_inv_id (f.app n),
      AlgebraicGeometry.SmallEtale.LAdicSheaf.Hom.ext _ _ _ fun n =>
        have := hf n
        IsIso.inv_hom_id (f.app n)⟩⟩⟩

/-- The lift into a levelwise kernel of a morphism killing the same map. -/
public def kernelLiftOfApp {K F G : LAdicSheaf.{u, u + 1} B X ℓ} (i : K ⟶ F) (f : F ⟶ G)
    (w : i ≫ f = 0)
    (hi : ∀ n, IsLimit (KernelFork.ofι (i.app n) (comp_eq_zero_app i f w n)))
    {H : LAdicSheaf.{u, u + 1} B X ℓ} (h : H ⟶ F) (wh : h ≫ f = 0) : H ⟶ K where
  app n := (KernelFork.IsLimit.lift' (hi n) (h.app n) (comp_eq_zero_app h f wh n)).1
  naturality n := by
    have : Mono (i.app n) := Fork.IsLimit.mono (hi n)
    have hfac (m : ℕ) :
        (KernelFork.IsLimit.lift' (hi m) (h.app m) (comp_eq_zero_app h f wh m)).1 ≫ i.app m =
          h.app m :=
      (KernelFork.IsLimit.lift' (hi m) (h.app m) _).2
    apply (cancel_mono ((restrictScalarsFunctor B X ℓ n).map (i.app n))).1
    rw [Category.assoc, ← i.naturality n, ← Category.assoc, hfac, Category.assoc,
      ← Functor.map_comp, hfac]
    exact h.naturality n

/-- A fork of morphisms of ℓ-adic sheaves which is a kernel at every finite level is a
kernel. -/
public def isLimit_kernelFork_of_app {K F G : LAdicSheaf.{u, u + 1} B X ℓ} (i : K ⟶ F)
    (f : F ⟶ G) (w : i ≫ f = 0)
    (hi : ∀ n, IsLimit (KernelFork.ofι (i.app n) (comp_eq_zero_app i f w n))) :
    IsLimit (KernelFork.ofι i w) :=
  have : Mono i := mono_of_app_mono i fun n => Fork.IsLimit.mono (hi n)
  KernelFork.IsLimit.ofι' i w fun h wh => ⟨kernelLiftOfApp i f w hi h wh,
    AlgebraicGeometry.SmallEtale.LAdicSheaf.Hom.ext _ _ _
      fun n => (KernelFork.IsLimit.lift' (hi n) (h.app n) _).2⟩

/-- A morphism of ℓ-adic sheaves whose components are monomorphisms is the kernel of its
levelwise cokernel. -/
@[instance_reducible, stacks 03UO "monomorphisms with monomorphic components are kernels, \
of the levelwise cokernel"]
public def normalMono_of_app_mono {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (hf : ∀ n, Mono (f.app n)) : NormalMono f where
  Z := cokernelSystem f
  g := cokernelSystemπ f
  w := comp_cokernelSystemπ f
  isLimit := isLimit_kernelFork_of_app f (cokernelSystemπ f) (comp_cokernelSystemπ f) (fun n => by
    have := hf n
    exact Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ (cokernel.π (f.app n)) (cokernel.condition (f.app n)))
      (cokernelIsCokernel (f.app n)))

/-- The descent out of a levelwise cokernel of a morphism killed by the same map. -/
public def cokernelDescOfApp {F G Q : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (p : G ⟶ Q)
    (w : f ≫ p = 0)
    (hp : ∀ n, IsColimit (CokernelCofork.ofπ (p.app n) (comp_eq_zero_app f p w n)))
    {H : LAdicSheaf.{u, u + 1} B X ℓ} (h : G ⟶ H) (wh : f ≫ h = 0) : Q ⟶ H where
  app n := (CokernelCofork.IsColimit.desc' (hp n) (h.app n) (comp_eq_zero_app f h wh n)).1
  naturality n := by
    have : Epi (p.app (n + 1)) := Cofork.IsColimit.epi (hp (n + 1))
    have hfac (m : ℕ) : p.app m ≫
        (CokernelCofork.IsColimit.desc' (hp m) (h.app m) (comp_eq_zero_app f h wh m)).1 =
          h.app m :=
      (CokernelCofork.IsColimit.desc' (hp m) (h.app m) _).2
    apply (cancel_epi (p.app (n + 1))).1
    rw [← Category.assoc, hfac, ← Category.assoc, p.naturality n, Category.assoc,
      ← Functor.map_comp, hfac]
    exact h.naturality n

/-- A cofork of morphisms of ℓ-adic sheaves which is a cokernel at every finite level is a
cokernel. -/
public def isColimit_cokernelCofork_of_app {F G Q : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (p : G ⟶ Q) (w : f ≫ p = 0)
    (hp : ∀ n, IsColimit (CokernelCofork.ofπ (p.app n) (comp_eq_zero_app f p w n))) :
    IsColimit (CokernelCofork.ofπ p w) :=
  have : Epi p := (epi_iff_app_epi p).2 fun n => Cofork.IsColimit.epi (hp n)
  CokernelCofork.IsColimit.ofπ' p w fun h wh => ⟨cokernelDescOfApp f p w hp h wh,
    AlgebraicGeometry.SmallEtale.LAdicSheaf.Hom.ext _ _ _
      fun n => (CokernelCofork.IsColimit.desc' (hp n) (h.app n) _).2⟩

/-- An epimorphism of ℓ-adic sheaves is the cokernel of a morphism killed by it whose levelwise
kernel comparisons are epimorphisms. -/
@[instance_reducible, stacks 03UO "epimorphisms whose levelwise kernel comparisons are \
epimorphisms are cokernels, \
of the morphism those comparisons compare to"]
public def normalEpi_of_epi_kernelLift {K F G : LAdicSheaf.{u, u + 1} B X ℓ} (i : K ⟶ F)
    (f : F ⟶ G) [Epi f] (w : i ≫ f = 0)
    (hi : ∀ n, Epi (kernel.lift (f.app n) (i.app n) (comp_eq_zero_app i f w n))) :
    NormalEpi f where
  W := K
  g := i
  w := w
  isColimit := isColimit_cokernelCofork_of_app i f w (fun n => by
    have := (epi_iff_app_epi f).1 inferInstance n
    have := hi n
    exact isCokernelEpiComp
      (Abelian.epiIsCokernelOfKernel
        (KernelFork.ofι (kernel.ι (f.app n)) (kernel.condition (f.app n)))
        (kernelIsKernel (f.app n)))
      (kernel.lift (f.app n) (i.app n) (comp_eq_zero_app i f w n))
      (kernel.lift_ι _ _ _).symm)

end LAdicSheaf

end Stacks.EtaleCohomology

end
