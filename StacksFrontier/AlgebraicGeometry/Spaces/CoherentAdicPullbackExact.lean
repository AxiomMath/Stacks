module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact

/-!
# Part (3) of Stacks 089P: the inverse image along a flat morphism is exact

Let `f : X' ⟶ X` be a flat morphism of Noetherian algebraic spaces over a scheme `S`, let
`𝓘 ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals and let `𝓘' = f⁻¹𝓘 · 𝒪_{X'}`.  **This file proves
part (3) of Stacks 089P: the functor `f^* : Coh(X, 𝓘) ⥤ Coh(X', 𝓘')` of
`AlgebraicGeometry.Space.coherentAdicPullback` is exact.**

Right exactness is already `AlgebraicGeometry.Space.coherentAdicPullback_rightExact`, and needs
no flatness: termwise inverse image is a left adjoint and cokernels in `Coh(X, 𝓘)` are the
levelwise ones.  What flatness supplies is left exactness, and for an additive functor between
abelian categories which is already right exact that is exactly the preservation of
monomorphisms (`CategoryTheory.Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono`: a
short exact sequence goes to an exact one by right exactness, so only injectivity of the first
morphism has to be added).  So the whole of part (3) is: `f^*` carries a monomorphism of
`Coh(X, 𝓘)` to a monomorphism.

A monomorphism of `Coh(X, 𝓘)` is *not* injective level by level — see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicNormalMono` — so that statement is not termwise
flatness.  What it is, is a statement about the stable kernel images of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicStableKernelImage`.  A morphism `α` is a
monomorphism exactly when the kernel object `AlgebraicGeometry.Space.coherentAdicKernel` vanishes,
and that object is levelwise the eventually constant limit of the adic quotients of the stable
kernel images, so `α` is a monomorphism exactly when, for each level `n`, the `(n + 1)`-st adic
quotient of the stable kernel image at some sufficiently high image level vanishes.  Both
ingredients of that description are carried by an exact functor:

* the stable kernel image is the abelian image of a kernel inclusion followed by a transition
  morphism, and an exact functor carries kernels to kernels and images to images, so
  `AlgebraicGeometry.Space.mapStableKernelImageIso` identifies the inverse image of a stable
  kernel image with the stable kernel image of the inverse image.  The stabilization level is a
  choice (`AlgebraicGeometry.Space.kernelStableLevel`) and the two choices are unrelated, so the
  comparison is made at a level above both, where
  `AlgebraicGeometry.Space.stableKernelImageIso` identifies either stable kernel image with the
  kernel image at that level;
* the adic quotient is a cokernel, and `AlgebraicGeometry.Space.IdealPowerMultipleCompatible` —
  the hypothesis pinning down `𝓘'` as the inverse image ideal — turns the cokernel of the
  inverse image into the right one, which is
  `AlgebraicGeometry.Space.exists_functor_idealPowerQuotient_iso`.

Only vanishing has to be transported, so no compatibility of those isomorphisms with the
inclusions or the transition morphisms is needed, and the eventually constant limit never has to
be commuted past the functor: the limit projections are invertible at every sufficiently high
image level on both sides, and a level high enough for both is the maximum of the two bounds.

## Main definitions

* `Stacks.ExactImage.isoImageOfEpiOfMono` — in an abelian category an epi-mono factorisation of a
  morphism identifies the middle object with the image of that morphism.
* `Stacks.ExactImage.mapImageKernelIso` — an exact functor between abelian categories carries the
  image of a kernel inclusion followed by a morphism to the corresponding image downstream.
* `AlgebraicGeometry.Space.mapKernelImageAtIso` and
  `AlgebraicGeometry.Space.mapStableKernelImageIso` — **the inverse image of a kernel image, and
  of a stable kernel image, is the kernel image, respectively the stable kernel image, of the
  inverse image.**

## Main results

* `AlgebraicGeometry.Space.mono_iff_isZero_coherentAdicKernel` — a morphism of coherent adic
  systems on a Noetherian algebraic space is injective exactly when its kernel object vanishes.
* `AlgebraicGeometry.Space.isZero_idealPowerQuotient_stableKernelImage_of_mono` and
  `AlgebraicGeometry.Space.mono_of_forall_isZero_idealPowerQuotient_stableKernelImage` — the
  description of injectivity by the vanishing of the adic quotients of the stable kernel images.
* `AlgebraicGeometry.Space.mono_coherentAdicMap_map` — **an exact functor on modules compatible
  with the ideal-power multiples transports monomorphisms of coherent adic systems.**
* `AlgebraicGeometry.Space.preservesFiniteLimits_coherentAdicMap` and
  `AlgebraicGeometry.Space.coherentAdicMap_exact` — **the induced functor
  `Coh(X, 𝓘) ⥤ Coh(X', 𝓘')` is exact.**
* `AlgebraicGeometry.Space.coherentAdicPullback_exact_of_preservesCoherence` — **part (3) of
  Stacks 089P: the inverse image functor along a flat morphism of Noetherian algebraic spaces is
  exact**, with coherence of the inverse image carried as a witness.  The form which discharges
  that witness from the Noetherian hypotheses, and carries the tag, is
  `AlgebraicGeometry.Space.coherentAdicPullback_exact` of
  `StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullbackExactNoetherian`.

## Implementation notes

The Noetherian hypotheses of the source appear as `hZ`, `hN` and `hN'`, and quasi-coherence of the
two sheaves of ideals as `hIcart` and `hIcart'`; they are what makes both categories abelian, by
part (1) of the same tag, and they are the explicit-argument form in which
`AlgebraicGeometry.Space.coherentAdicKernel` takes them.

Two further hypotheses, `hw` and `hcoh`, are inherited from
`AlgebraicGeometry.Space.coherentAdicPullback` itself and are not about flatness; they are what
pins down `𝓘'` as the inverse image ideal `f⁻¹𝓘 · 𝒪_{X'}` and what makes termwise inverse image
preserve coherence, and without them the functor whose exactness is at issue cannot be
constructed.  The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullback` explain why each is a hypothesis
there.  Flatness enters only through
`AlgebraicGeometry.Space.preservesFiniteLimits_modulePullback_of_isFlat_hom`.

Of those two, `hcoh` is *not* a hypothesis of the source: a morphism of Noetherian algebraic
spaces has coherent inverse images, and `AlgebraicGeometry.Space.isCoherent_modulePullback`
proves it from the local Noetherianity contained in `hN'`.  The discharge is applied in the
downstream module `StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullbackExactNoetherian`,
which is where part (3) carries its tag.

## References

* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂ u

namespace Stacks.ExactImage

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- **An epimorphism-monomorphism factorisation of a morphism of an abelian category identifies
the middle object with the image of that morphism.**  The comparison is the lift of the
monomorphism through the kernel of the cokernel projection; it is a monomorphism because that
monomorphism is one, and an epimorphism because the canonical morphism onto the image is one. -/
def isoImageOfEpiOfMono {A I Y : C} (φ : A ⟶ Y) (p : A ⟶ I) (i : I ⟶ Y) [Epi p] [Mono i]
    (fac : p ≫ i = φ) : I ≅ Abelian.image φ :=
  have hz : i ≫ cokernel.π φ = 0 :=
    (cancel_epi p).1 (by rw [← Category.assoc, fac, cokernel.condition, comp_zero])
  have hk : kernel.lift (cokernel.π φ) i hz ≫ Abelian.image.ι φ = i := kernel.lift_ι _ _ _
  have _hm : Mono (kernel.lift (cokernel.π φ) i hz) := mono_of_mono_fac hk
  have hpk : p ≫ kernel.lift (cokernel.π φ) i hz = Abelian.factorThruImage φ := by
    rw [← cancel_mono (Abelian.image.ι φ), Category.assoc, hk, fac, Abelian.image.fac]
  have _he : Epi (kernel.lift (cokernel.π φ) i hz) :=
    have _h : Epi (p ≫ kernel.lift (cokernel.π φ) i hz) := by
      rw [hpk]
      infer_instance
    epi_of_epi p _
  have _hi : IsIso (kernel.lift (cokernel.π φ) i hz) := isIso_of_mono_of_epi _
  asIso (kernel.lift (cokernel.π φ) i hz)

/-- **An exact functor between abelian categories carries the image of a kernel inclusion followed
by a morphism to the image of the kernel inclusion of the image of the morphism followed by the
image of that further morphism.**  The functor carries the kernel to the kernel, and carries the
epi-mono factorisation of the composite through its image to an epi-mono factorisation. -/
def mapImageKernelIso (L : C ⥤ D) [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A Y Z : C} (v : A ⟶ Y) (w : A ⟶ Z) :
    L.obj (Abelian.image (kernel.ι v ≫ w)) ≅
      Abelian.image (kernel.ι (L.map v) ≫ L.map w) :=
  isoImageOfEpiOfMono (kernel.ι (L.map v) ≫ L.map w)
    ((PreservesKernel.iso (G := L) (f := v)).inv ≫
      L.map (Abelian.factorThruImage (kernel.ι v ≫ w)))
    (L.map (Abelian.image.ι (kernel.ι v ≫ w)))
    (by rw [Category.assoc, ← L.map_comp, Abelian.image.fac, L.map_comp, ← Category.assoc,
      PreservesKernel.iso_inv_ι])

end Stacks.ExactImage

namespace Stacks

/-- A functor preserving zero morphisms carries a zero object to a zero object. -/
theorem isZero_map_obj {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (L : C ⥤ D) [L.PreservesZeroMorphisms] {M : C}
    (h : IsZero M) : IsZero (L.obj M) :=
  (IsZero.iff_id_eq_zero _).2 (by
    rw [← L.map_id, (IsZero.iff_id_eq_zero M).1 h, L.map_zero])

end Stacks

namespace AlgebraicGeometry.Space

/-! ### Vanishing of a coherent adic system -/

section Vanishing

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- A coherent adic system which vanishes vanishes at every level. -/
theorem isZero_coherentAdicSystem_obj {E : CoherentAdicSystems B S hS F hF 𝓘} (h : IsZero E)
    (n : ℕᵒᵖ) : IsZero (E.obj.obj n) :=
  (IsZero.iff_id_eq_zero (E.obj.obj n)).2
    (congrArg (fun z : E ⟶ E => z.hom.app n) ((IsZero.iff_id_eq_zero E).1 h))

/-- A coherent adic system which vanishes at every level vanishes: the inclusion of `Coh(F, 𝓘)`
into the inverse systems of `𝒪_F`-modules is fully faithful, and a functor into a category with a
zero object vanishes exactly when all its values do. -/
theorem isZero_coherentAdicSystem_of_forall_isZero_obj
    {E : CoherentAdicSystems B S hS F hF 𝓘} (h : ∀ n : ℕᵒᵖ, IsZero (E.obj.obj n)) : IsZero E :=
  IsZero.of_full_of_faithful_of_isZero
    (ObjectProperty.ι (IsCoherentAdicSystem B S hS F hF 𝓘)) E (Functor.isZero _ h)

end Vanishing

/-! ### Injectivity by the vanishing of the stable kernel images -/

section Mono

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ F)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {E E' : CoherentAdicSystems B S hS F hF 𝓘}

/-- **A morphism of coherent adic systems on a Noetherian algebraic space is injective exactly
when its kernel object vanishes.** -/
theorem mono_iff_isZero_coherentAdicKernel (α : E ⟶ E') :
    Mono α ↔ IsZero (coherentAdicKernel B S hS F hF 𝓘 hZ hN hIcart α) := by
  refine ⟨fun hα => ?_, fun h => ?_⟩
  · have h0 : coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart α = 0 := by
      rw [← cancel_mono α, zero_comp]
      exact coherentAdicKernelι_comp B S hS F hF 𝓘 hZ hN hIcart α
    have _hm : Mono (coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart α) :=
      ⟨fun _ _ hfg => Fork.IsLimit.hom_ext
        (coherentAdicKernelIsLimit B S hS F hF 𝓘 hZ hN hIcart α) hfg⟩
    rw [IsZero.iff_id_eq_zero,
      ← cancel_mono (coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart α), Category.id_comp,
      zero_comp, h0]
  · rw [Preadditive.mono_iff_cancel_zero]
    intro Z g hg
    obtain ⟨t, hfac⟩ : ∃ t : Z ⟶ coherentAdicKernel B S hS F hF 𝓘 hZ hN hIcart α,
        t ≫ coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart α = g :=
      ⟨(coherentAdicKernelIsLimit B S hS F hF 𝓘 hZ hN hIcart α).lift (KernelFork.ofι g hg),
        (coherentAdicKernelIsLimit B S hS F hF 𝓘 hZ hN hIcart α).fac
          (KernelFork.ofι g hg) WalkingParallelPair.zero⟩
    rw [← hfac, h.eq_of_tgt t 0, zero_comp]

/-- **The adic quotients of the stable kernel images of an injective morphism of coherent adic
systems vanish**, at every image level at which the projection from the kernel object is
invertible. -/
theorem isZero_idealPowerQuotient_stableKernelImage_of_mono (α : E ⟶ E') (hα : Mono α)
    (n m : ℕ) (hiso : IsIso (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n m)) :
    IsZero (idealPowerQuotient B S hS F hF 𝓘 (n + 1)
      (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m)) :=
  have hk : IsZero (coherentAdicKernel B S hS F hF 𝓘 hZ hN hIcart α) :=
    (mono_iff_isZero_coherentAdicKernel B S hS F hF 𝓘 hZ hN hIcart α).1 hα
  have hobj : IsZero ((coherentAdicKernel B S hS F hF 𝓘 hZ hN hIcart α).obj.obj (op n)) :=
    isZero_coherentAdicSystem_obj B S hS F hF 𝓘 hk (op n)
  (Iso.isZero_iff (asIso (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n m))).1 hobj

/-- **A morphism of coherent adic systems on a Noetherian algebraic space whose stable kernel
images have vanishing adic quotients is injective.**  At each level it is enough to exhibit one
image level at which the projection from the kernel object is invertible and the adic quotient
vanishes. -/
theorem mono_of_forall_isZero_idealPowerQuotient_stableKernelImage (α : E ⟶ E')
    (h : ∀ n : ℕ, ∃ m : ℕ,
      IsIso (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n m) ∧
      IsZero (idealPowerQuotient B S hS F hF 𝓘 (n + 1)
        (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m))) :
    Mono α := by
  refine (mono_iff_isZero_coherentAdicKernel B S hS F hF 𝓘 hZ hN hIcart α).2
    (isZero_coherentAdicSystem_of_forall_isZero_obj B S hS F hF 𝓘 fun n => ?_)
  obtain ⟨m, hiso, hz⟩ := h n.unop
  exact (Iso.isZero_iff
    (asIso (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n.unop m))).2 hz

end Mono

/-! ### Transport of the stable kernel images along an exact functor -/

section Transport

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS}
    (L : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS X'.1 X'.2)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule)
    (𝓘' : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X'.1 X'.2).O))).Submodule)
    [L.PreservesZeroMorphisms] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ X.1) (hN' : IsNoetherian B S hS hZ X'.1)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (hIcart' : IsCartesianOnAffineCharts 𝓘'.toSheafOfModules)
    (hw : IdealPowerMultipleCompatible B S hS L 𝓘 𝓘')
    (hcoh : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 M →
      IsCoherent B S hS X'.1 X'.2 (L.obj M))
    {E E' : CoherentAdicSystems B S hS X.1 X.2 𝓘}

/-- **The inverse image of a kernel image is the kernel image of the inverse image.**  The kernel
image is the abelian image of a kernel inclusion followed by a transition morphism of the system,
and an exact functor carries both to the corresponding data downstream. -/
def mapKernelImageAtIso (α : E ⟶ E') (m l : ℕ) (h : m ≤ l) :
    L.obj (kernelImageAt B S hS X.1 X.2 𝓘 α m l h) ≅
      kernelImageAt B S hS X'.1 X'.2 𝓘'
        ((coherentAdicMap B S hS L 𝓘 𝓘' hw hcoh).map α) m l h :=
  Stacks.ExactImage.mapImageKernelIso L (α.hom.app (op l)) (E.obj.map (homOfLE h).op)

/-- **The inverse image of a stable kernel image is the stable kernel image of the inverse
image.**

The stabilization levels of `α` and of its transport are independent choices, so the comparison is
made at their maximum, where `AlgebraicGeometry.Space.stableKernelImageIso` identifies either
stable kernel image with the kernel image at that level. -/
def mapStableKernelImageIso (α : E ⟶ E') (m : ℕ) :
    L.obj (stableKernelImage B S hS X.1 X.2 𝓘 hZ hN hIcart α m) ≅
      stableKernelImage B S hS X'.1 X'.2 𝓘' hZ hN' hIcart'
        ((coherentAdicMap B S hS L 𝓘 𝓘' hw hcoh).map α) m :=
  (L.mapIso (stableKernelImageIso B S hS X.1 X.2 𝓘 hZ hN hIcart α m
      (max (kernelStableLevel B S hS X.1 X.2 𝓘 hZ hN hIcart α m)
        (kernelStableLevel B S hS X'.1 X'.2 𝓘' hZ hN' hIcart'
          ((coherentAdicMap B S hS L 𝓘 𝓘' hw hcoh).map α) m))
      (le_max_left _ _))).symm ≪≫
    mapKernelImageAtIso B S hS L 𝓘 𝓘' hw hcoh α m
      (max (kernelStableLevel B S hS X.1 X.2 𝓘 hZ hN hIcart α m)
        (kernelStableLevel B S hS X'.1 X'.2 𝓘' hZ hN' hIcart'
          ((coherentAdicMap B S hS L 𝓘 𝓘' hw hcoh).map α) m)) _ ≪≫
    stableKernelImageIso B S hS X'.1 X'.2 𝓘' hZ hN' hIcart'
      ((coherentAdicMap B S hS L 𝓘 𝓘' hw hcoh).map α) m
      (max (kernelStableLevel B S hS X.1 X.2 𝓘 hZ hN hIcart α m)
        (kernelStableLevel B S hS X'.1 X'.2 𝓘' hZ hN' hIcart'
          ((coherentAdicMap B S hS L 𝓘 𝓘' hw hcoh).map α) m))
      (le_max_right _ _)

/-! ### Exactness of the induced functor -/

include hZ hN hN' hIcart hIcart' in
/-- **An exact functor on modules compatible with the ideal-power multiples transports
monomorphisms of coherent adic systems.**

Injectivity is the vanishing of the adic quotients of the stable kernel images; the functor
carries each stable kernel image to the corresponding one and each adic quotient to the
corresponding one, and a level high enough for both limit projections to be invertible is the
maximum of the two bounds. -/
theorem mono_coherentAdicMap_map (α : E ⟶ E') (hα : Mono α) :
    Mono ((coherentAdicMap B S hS L 𝓘 𝓘' hw hcoh).map α) := by
  refine mono_of_forall_isZero_idealPowerQuotient_stableKernelImage B S hS X'.1 X'.2 𝓘'
    hZ hN' hIcart' ((coherentAdicMap B S hS L 𝓘 𝓘' hw hcoh).map α) fun n => ?_
  obtain ⟨c, hc⟩ := stableKernelImageLimitπ_eventually_isIso B S hS X.1 X.2 𝓘 hZ hN hIcart α n
  obtain ⟨c', hc'⟩ := stableKernelImageLimitπ_eventually_isIso B S hS X'.1 X'.2 𝓘' hZ hN' hIcart'
    ((coherentAdicMap B S hS L 𝓘 𝓘' hw hcoh).map α) n
  obtain ⟨m, h, h'⟩ : ∃ m, n + c ≤ m ∧ n + c' ≤ m := ⟨n + max c c', by omega, by omega⟩
  refine ⟨m, hc' m h', ?_⟩
  obtain ⟨e, -⟩ := exists_functor_idealPowerQuotient_iso B S hS L 𝓘 𝓘' (n + 1)
    (stableKernelImage B S hS X.1 X.2 𝓘 hZ hN hIcart α m)
    (hw (n + 1) (stableKernelImage B S hS X.1 X.2 𝓘 hZ hN hIcart α m))
  exact (Iso.isZero_iff (idealPowerQuotientIsoOfIso B S hS X'.1 X'.2 𝓘' (n + 1)
      (mapStableKernelImageIso B S hS L 𝓘 𝓘' hZ hN hN' hIcart hIcart' hw hcoh α m))).1
    ((Iso.isZero_iff e).1 (Stacks.isZero_map_obj L
      (isZero_idealPowerQuotient_stableKernelImage_of_mono B S hS X.1 X.2 𝓘 hZ hN hIcart α hα
        n m (hc m h))))

include hZ hN hN' hIcart hIcart' in
/-- **The induced functor `Coh(X, 𝓘) ⥤ Coh(X', 𝓘')` of an exact functor on modules compatible
with the ideal-power multiples is left exact.**

For an additive functor between abelian categories which preserves finite colimits, left exactness
is the preservation of monomorphisms: a short exact sequence is carried to an exact one by right
exactness, and the first morphism stays injective. -/
theorem preservesFiniteLimits_coherentAdicMap :
    PreservesFiniteLimits (coherentAdicMap B S hS L 𝓘 𝓘' hw hcoh) := by
  let := abelian_coherentAdicSystems B S hS X.1 X.2 𝓘 hZ hN hIcart
  let := abelian_coherentAdicSystems B S hS X'.1 X'.2 𝓘' hZ hN' hIcart'
  have hcol : PreservesFiniteColimits (coherentAdicMap B S hS L 𝓘 𝓘' hw hcoh) :=
    (rightExactFunctor_iff _).mp (coherentAdicMap_rightExact B S hS L 𝓘 𝓘' hw hcoh)
  have _hbip : PreservesBinaryBiproducts (coherentAdicMap B S hS L 𝓘 𝓘' hw hcoh) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have _hadd : (coherentAdicMap B S hS L 𝓘 𝓘' hw hcoh).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  refine (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).2 fun T hT => ?_
  exact ⟨((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).1 hcol T hT).1,
    mono_coherentAdicMap_map B S hS L 𝓘 𝓘' hZ hN hN' hIcart hIcart' hw hcoh T.f hT.mono_f⟩

include hZ hN hN' hIcart hIcart' in
/-- **The induced functor `Coh(X, 𝓘) ⥤ Coh(X', 𝓘')` of an exact functor on modules compatible
with the ideal-power multiples is exact.** -/
theorem coherentAdicMap_exact :
    exactFunctor (CoherentAdicSystems B S hS X.1 X.2 𝓘)
        (CoherentAdicSystems B S hS X'.1 X'.2 𝓘')
      (coherentAdicMap B S hS L 𝓘 𝓘' hw hcoh) :=
  (exactFunctor_iff _).2
    ⟨preservesFiniteLimits_coherentAdicMap B S hS L 𝓘 𝓘' hZ hN hN' hIcart hIcart' hw hcoh,
      (rightExactFunctor_iff _).mp (coherentAdicMap_rightExact B S hS L 𝓘 𝓘' hw hcoh)⟩

end Transport

/-! ### Part (3) of Stacks 089P, with coherence of the inverse image as a witness -/

section Pullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS} (f : X' ⟶ X)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule)
    (𝓘' : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X'.1 X'.2).O))).Submodule)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ X.1) (hN' : IsNoetherian B S hS hZ X'.1)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (hIcart' : IsCartesianOnAffineCharts 𝓘'.toSheafOfModules)
    (hw : IdealPowerMultipleCompatible B S hS (modulePullback B S hS f) 𝓘 𝓘')
    (hcoh : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 M →
      IsCoherent B S hS X'.1 X'.2 ((modulePullback B S hS f).obj M))

include hZ hN hN' hIcart hIcart' in
/-- **Part (3) of Stacks 089P: the inverse image functor along a flat morphism of Noetherian
algebraic spaces is exact.**  For a flat morphism `f : X' ⟶ X` of Noetherian algebraic spaces, a
quasi-coherent sheaf of ideals `𝓘 ⊆ 𝒪_X` and `𝓘' = f⁻¹𝓘 · 𝒪_{X'}`, the functor
`f^* : Coh(X, 𝓘) ⥤ Coh(X', 𝓘')` preserves finite limits and finite colimits.

Right exactness is `AlgebraicGeometry.Space.coherentAdicPullback_rightExact` and needs no
flatness.  Flatness makes the inverse image of `𝒪_X`-modules left exact, by
`AlgebraicGeometry.Space.preservesFiniteLimits_modulePullback_of_isFlat_hom`, and left exactness
of `f^*` on coherent adic systems follows by
`AlgebraicGeometry.Space.coherentAdicMap_exact`.

The witness `hcoh` that termwise inverse image preserves coherence is a hypothesis *here only*:
it is a consequence of the Noetherian hypotheses already present, by
`AlgebraicGeometry.Space.isCoherent_modulePullback`, and the form of part (3) which discharges it
and carries the tag is `AlgebraicGeometry.Space.coherentAdicPullback_exact` of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullbackExactNoetherian`. -/
theorem coherentAdicPullback_exact_of_preservesCoherence (hf : IsFlat B S hS f.hom) :
    exactFunctor (CoherentAdicSystems B S hS X.1 X.2 𝓘)
        (CoherentAdicSystems B S hS X'.1 X'.2 𝓘')
      (coherentAdicPullback B S hS f 𝓘 𝓘' hw hcoh) :=
  have _hz := preservesZeroMorphisms_modulePullback B S hS f
  have _hc := preservesFiniteColimits_modulePullback B S hS f
  have _hl := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS f hf
  coherentAdicMap_exact B S hS (modulePullback B S hS f) 𝓘 𝓘' hZ hN hN' hIcart hIcart' hw hcoh

include hZ hN hN' hIcart hIcart' in
/-- **The inverse image functor along a flat morphism of Noetherian algebraic spaces preserves
finite limits**, the half of part (3) of Stacks 089P which flatness supplies, with coherence of
the inverse image as the witness `hcoh`. -/
theorem preservesFiniteLimits_coherentAdicPullback_of_preservesCoherence
    (hf : IsFlat B S hS f.hom) :
    PreservesFiniteLimits (coherentAdicPullback B S hS f 𝓘 𝓘' hw hcoh) :=
  ((exactFunctor_iff _).1 (coherentAdicPullback_exact_of_preservesCoherence
    B S hS f 𝓘 𝓘' hZ hN hN' hIcart hIcart' hw hcoh hf)).1

end Pullback

end AlgebraicGeometry.Space

end
