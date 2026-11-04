module

public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Subobject.Limits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.LevelConstructibility

/-!
# The levels of the kernel of a morphism of ℓ-adic sheaves

The kernel of a morphism `Φ = {φₙ}` of ℓ-adic sheaves is not its levelwise kernel: scalar
reduction is not left exact, so the compatibility condition of Tag 03UM fails for
`{Ker(φₙ)}`. Its levels are instead the intersections `⋂_{m ≥ n} Im(Ker(φₘ) → Ker(φₙ))`.

The maps `Ker(φₘ) → Ker(φₙ)` are the iterated mates of the transition maps between levelwise
kernels, `Stacks.EtaleCohomology.LAdicSheaf.rawKernelReduction`; their images form a descending
chain of subobjects of `Ker(φₙ)`, whose intersection is the wide pullback of that chain over
`Ker(φₙ)`. As a subobject of the constructible sheaf `Ker(φₙ)` it is constructible.

## Main definitions

* `Stacks.EtaleCohomology.FiniteLevelSheaf.iteratedReduction`: scalar reduction from level `n + k`
  to level `n`.
* `Stacks.EtaleCohomology.LAdicSheaf.iteratedKernelReduction`: the induced map from the reduction
  of `Ker(φₙ₊ₖ)` to `Ker(φₙ)`.
* `Stacks.EtaleCohomology.LAdicSheaf.rawKernelImage`: its image, as a subobject of `Ker(φₙ)`.
* `Stacks.EtaleCohomology.LAdicSheaf.stableKernelLevel` and `.stableKernelι`: the intersection of
  those images, and its inclusion into `Ker(φₙ)`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.rawKernelImage_antitone`: the images form a descending
  chain.
* `Stacks.EtaleCohomology.LAdicSheaf.stableKernelι_mono` and `.le_stableKernel_iff`: the
  inclusion is a monomorphism and the subobject it names is the infimum of the chain.
* `Stacks.EtaleCohomology.LAdicSheaf.isConstructible_stableKernelLevel`: each level of the kernel
  is a constructible sheaf.
* `Stacks.EtaleCohomology.LAdicSheaf.stableKernelι_isIso_of_epi`: when every mate of a
  transition map is an epimorphism, the intersection is the whole levelwise kernel.

## References

* [Stacks Project, Tag 03UO](https://stacks.math.columbia.edu/tag/03UO)
* [Stacks Project, Tag 03UM](https://stacks.math.columbia.edu/tag/03UM)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u u₁ u₂ v₁

namespace Stacks.EtaleCohomology

/-- The base map of a wide pullback of monomorphisms is a monomorphism. -/
public theorem widePullback_base_mono {C : Type u₁} [Category.{v₁} C] {J : Type u₂}
    {F : C} {G : J → C} (i : ∀ j, G j ⟶ F) [∀ j, Mono (i j)] [HasWidePullback F G i] :
    Mono (WidePullback.base i) := by
  refine ⟨fun g h w => WidePullback.hom_ext i g h (fun j => (cancel_mono (i j)).1 ?_) w⟩
  simpa only [Category.assoc, WidePullback.π_arrow] using w

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

namespace FiniteLevelSheaf

/-- Scalar reduction from level `n + k` down to level `n`. -/
public def iteratedReduction (n : ℕ) :
    (k : ℕ) → FiniteLevelSheaf.{u, u + 1} B X ℓ (n + k) ⥤ FiniteLevelSheaf.{u, u + 1} B X ℓ n
  | 0 => 𝟭 _
  | k + 1 => scalarReductionFunctor B X ℓ (n + k) ⋙ iteratedReduction n k

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- Iterated scalar reduction is a left adjoint. -/
public theorem iteratedReduction_isLeftAdjoint (n k : ℕ) :
    (iteratedReduction B X ℓ n k).IsLeftAdjoint := by
  induction k with
  | zero => exact inferInstanceAs (𝟭 (FiniteLevelSheaf.{u, u + 1} B X ℓ n)).IsLeftAdjoint
  | succ k hk =>
    have : (scalarReductionFunctor B X ℓ (n + k)).IsLeftAdjoint :=
      (scalarAdjunction B X ℓ (n + k)).isLeftAdjoint
    show (scalarReductionFunctor B X ℓ (n + k) ⋙ iteratedReduction B X ℓ n k).IsLeftAdjoint
    infer_instance

end FiniteLevelSheaf

variable [Fact ℓ.Prime] [IsNoetherian X.1]

namespace LAdicSheaf

variable {B X ℓ}

/-- The map from the iterated reduction of the levelwise kernel at level `n + k` to the levelwise
kernel at level `n`, obtained by composing the mates of the transition maps. -/
public def iteratedKernelReduction {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (n : ℕ) :
    (k : ℕ) →
      (FiniteLevelSheaf.iteratedReduction B X ℓ n k).obj (kernel (f.app (n + k))) ⟶
        kernel (f.app n)
  | 0 => 𝟙 _
  | k + 1 => (FiniteLevelSheaf.iteratedReduction B X ℓ n k).map (rawKernelReduction f (n + k)) ≫
      iteratedKernelReduction f n k

/-- The image of `Ker(φₙ₊ₖ)` in `Ker(φₙ)`, as a subobject. -/
public def rawKernelImage {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (n k : ℕ) :
    Subobject (kernel (f.app n)) :=
  imageSubobject (iteratedKernelReduction f n k)

/-- The images of the levelwise kernels above level `n` form a descending chain of subobjects of
the levelwise kernel at level `n`. -/
public theorem rawKernelImage_antitone {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (n : ℕ) :
    Antitone (rawKernelImage f n) :=
  antitone_nat_of_succ_le fun _ => imageSubobject_comp_le _ _

/-- When every mate of a transition map between levelwise kernels above level `n` is an
epimorphism, so is every iterate. -/
public theorem iteratedKernelReduction_epi {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (n : ℕ) (h : ∀ k, Epi (rawKernelReduction f (n + k))) (k : ℕ) :
    Epi (iteratedKernelReduction f n k) := by
  induction k with
  | zero => exact inferInstanceAs (Epi (𝟙 (kernel (f.app n))))
  | succ k hk =>
    have := h k
    have : (FiniteLevelSheaf.iteratedReduction B X ℓ n k).IsLeftAdjoint :=
      FiniteLevelSheaf.iteratedReduction_isLeftAdjoint B X ℓ n k
    show Epi ((FiniteLevelSheaf.iteratedReduction B X ℓ n k).map (rawKernelReduction f (n + k))
      ≫ iteratedKernelReduction f n k)
    infer_instance

/-- The level `n` of the kernel of a morphism of ℓ-adic sheaves: the intersection
`⋂_{k} Im(Ker(φₙ₊ₖ) → Ker(φₙ))`, realised as the wide pullback of the images over the levelwise
kernel. -/
public def stableKernelLevel {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (n : ℕ) :
    FiniteLevelSheaf.{u, u + 1} B X ℓ n :=
  widePullback (kernel (f.app n)) (fun k => (Subobject.underlying).obj (rawKernelImage f n k))
    (fun k => (rawKernelImage f n k).arrow)

/-- The inclusion of the kernel level into the levelwise kernel. -/
public def stableKernelι {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (n : ℕ) :
    stableKernelLevel f n ⟶ kernel (f.app n) :=
  WidePullback.base (fun k => (rawKernelImage f n k).arrow)

/-- The inclusion of the kernel level into the levelwise kernel is a monomorphism. -/
public instance stableKernelι_mono {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (n : ℕ) :
    Mono (stableKernelι f n) :=
  widePullback_base_mono _

/-- The projection of the kernel level onto the `k`-th image. -/
public def stableKernelProjection {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (n k : ℕ) :
    stableKernelLevel f n ⟶ (Subobject.underlying).obj (rawKernelImage f n k) :=
  WidePullback.π (fun k => (rawKernelImage f n k).arrow) k

/-- The projection of the kernel level onto an image, followed by the inclusion of that image, is
the inclusion of the kernel level. -/
@[simp]
public theorem stableKernelProjection_arrow {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (n k : ℕ) :
    stableKernelProjection f n k ≫ (rawKernelImage f n k).arrow = stableKernelι f n :=
  WidePullback.π_arrow _ _

/-- A map into the levelwise kernel that factors through every image factors through the kernel
level. -/
public def stableKernelLift {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (n : ℕ)
    {H : FiniteLevelSheaf.{u, u + 1} B X ℓ n} (h : H ⟶ kernel (f.app n))
    (l : ∀ k, H ⟶ (Subobject.underlying).obj (rawKernelImage f n k))
    (hl : ∀ k, l k ≫ (rawKernelImage f n k).arrow = h) :
    H ⟶ stableKernelLevel f n :=
  WidePullback.lift h l hl

/-- The lift through the kernel level, followed by its inclusion, is the given map. -/
@[simp]
public theorem stableKernelLift_ι {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (n : ℕ)
    {H : FiniteLevelSheaf.{u, u + 1} B X ℓ n} (h : H ⟶ kernel (f.app n))
    (l : ∀ k, H ⟶ (Subobject.underlying).obj (rawKernelImage f n k))
    (hl : ∀ k, l k ≫ (rawKernelImage f n k).arrow = h) :
    stableKernelLift f n h l hl ≫ stableKernelι f n = h :=
  WidePullback.lift_base _ _ _ _

/-- The lift through the kernel level is the unique map over the given one. -/
public theorem stableKernelLift_unique {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (n : ℕ)
    {H : FiniteLevelSheaf.{u, u + 1} B X ℓ n} (h : H ⟶ kernel (f.app n))
    (l : ∀ k, H ⟶ (Subobject.underlying).obj (rawKernelImage f n k))
    (hl : ∀ k, l k ≫ (rawKernelImage f n k).arrow = h)
    (m : H ⟶ stableKernelLevel f n) (hm : m ≫ stableKernelι f n = h) :
    m = stableKernelLift f n h l hl := by
  refine (cancel_mono (stableKernelι f n)).1 ?_
  rw [hm, stableKernelLift_ι]

/-- A subobject of the levelwise kernel is contained in the kernel level exactly when it is
contained in every image. -/
public theorem le_stableKernel_iff {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (n : ℕ)
    (S : Subobject (kernel (f.app n))) :
    S ≤ Subobject.mk (stableKernelι f n) ↔ ∀ k, S ≤ rawKernelImage f n k := by
  refine ⟨fun h k => h.trans (Subobject.mk_le_of_comm (stableKernelProjection f n k)
      (stableKernelProjection_arrow f n k)), fun h => Subobject.le_mk_of_comm
      (stableKernelLift f n S.arrow (fun k => S.ofLE (rawKernelImage f n k) (h k))
        (fun k => Subobject.ofLE_arrow (h k)))
      (stableKernelLift_ι f n _ _ _)⟩

/-- The inclusion of the kernel level into the source is killed by the morphism. -/
public theorem stableKernel_comp_eq_zero {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (n : ℕ) : (stableKernelι f n ≫ kernel.ι (f.app n)) ≫ f.app n = 0 := by
  simp only [Category.assoc, kernel.condition, comp_zero]

/-- Each level of the kernel of a morphism of ℓ-adic sheaves is a constructible sheaf. -/
@[stacks 09BH "part (3), subsheaf, applied to the intersection of the images of the levelwise \
kernels inside a levelwise kernel"]
public theorem isConstructible_stableKernelLevel {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (n : ℕ) :
    IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (n + 1))) (stableKernelLevel f n) :=
  FiniteLevelSheaf.isConstructible_of_mono B X ℓ n (stableKernelι f n)
    (isConstructible_kernel_app f n)

/-- When every mate of a transition map between levelwise kernels above level `n` is an
epimorphism, the chain of images is constant and the kernel level is the whole levelwise
kernel. -/
public theorem stableKernelι_isIso_of_epi {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (n : ℕ) (h : ∀ k, Epi (rawKernelReduction f (n + k))) :
    IsIso (stableKernelι f n) := by
  have (k : ℕ) : Epi (iteratedKernelReduction f n k) :=
    iteratedKernelReduction_epi f n h k
  have (k : ℕ) : IsIso (rawKernelImage f n k).arrow := by
    have : Epi (image.ι (iteratedKernelReduction f n k)) :=
      epi_of_epi_fac (image.fac (iteratedKernelReduction f n k))
    have : IsIso (image.ι (iteratedKernelReduction f n k)) := isIso_of_mono_of_epi _
    show IsIso (imageSubobject (iteratedKernelReduction f n k)).arrow
    rw [← imageSubobject_arrow (iteratedKernelReduction f n k)]
    infer_instance
  let r := stableKernelLift f n (𝟙 _) (fun k => inv (rawKernelImage f n k).arrow)
    (fun k => IsIso.inv_hom_id _)
  have hr : r ≫ stableKernelι f n = 𝟙 _ := stableKernelLift_ι f n _ _ _
  refine ⟨⟨r, (cancel_mono (stableKernelι f n)).1 ?_, hr⟩⟩
  rw [Category.assoc, hr, Category.comp_id, Category.id_comp]

/-- For an epimorphism of ℓ-adic sheaves the kernel level is the whole levelwise kernel. -/
public theorem stableKernelι_isIso_of_lAdic_epi {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    [Epi f] (n : ℕ) : IsIso (stableKernelι f n) :=
  stableKernelι_isIso_of_epi f n (fun k => rawKernelReduction_epi f (n + k))

end LAdicSheaf

end Stacks.EtaleCohomology

end
