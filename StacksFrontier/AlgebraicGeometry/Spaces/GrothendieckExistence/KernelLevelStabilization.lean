module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicStableKernelQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicLevelwiseKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionAlgebraization

/-!
# The levelwise kernels of a surjection of coherent adic systems stabilize

Let `F` be a Noetherian algebraic space, `𝓘 ⊆ 𝒪_F` a quasi-coherent sheaf of ideals and
`π : E ⟶ E'` a surjection in `Coh(F, 𝓘)` whose levelwise kernels `ker π_n` are all annihilated
by one power `𝓘 ^ t`.  This file proves that the transition maps `ker π_l ⟶ ker π_m` of the
levelwise kernels are isomorphisms for all `m₀ ≤ m ≤ l`, and deduces that the squares formed by
`π_l`, `π_m` and the transition maps of `E` and `E'` are pullback squares in that range.

In module terms, writing `E_n = M / I ⁿ⁺¹ M` with kernel `K` of the completed map, the statement
says that `K ∩ I ᵐ⁺¹ M = 0` for `m ≥ m₀`.

## Main results

* `AlgebraicGeometry.Space.kernelImageAtIsoKernelOfEpi` — for a surjection the image in `E_m` of
  the kernel at a higher level is the kernel at level `m`.
* `AlgebraicGeometry.Space.exists_isIso_kernelLevelMap_of_epi` — **the transition maps of the
  levelwise kernels are eventually isomorphisms.**
* `CategoryTheory.Abelian.isPullback_of_isIso_kernelMap` — a commutative square in an abelian
  category whose top arrow is an epimorphism and which induces an isomorphism on the kernels of
  its horizontal arrows is a pullback square.
* `AlgebraicGeometry.Space.exists_isPullback_transition_of_epi` — the squares of a surjection
  are eventually pullback squares.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and zero-indexed: the term at `n` is the Stacks source's
`E_{n + 1}`.

## References

* [Stacks Project, Tag 08BB](https://stacks.math.columbia.edu/tag/08BB)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Abelian

variable {C : Type*} [Category* C] [Abelian C]

/-- **A commutative square with an epimorphic top arrow inducing an isomorphism on the kernels
of its horizontal arrows is a pullback square.** -/
theorem isPullback_of_isIso_kernelMap {X₁ X₂ X₃ X₄ : C} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
    {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (w : t ≫ r = l ≫ b) [Epi t]
    [IsIso (kernel.map t b l r w)] : IsPullback t l r b := by
  let φ : X₁ ⟶ pullback r b := pullback.lift t l w
  have hφ₁ : φ ≫ pullback.fst r b = t := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ pullback.snd r b = l := pullback.lift_snd _ _ _
  have hmap : kernel.map t b l r w ≫ kernel.ι b = kernel.ι t ≫ l := kernel.lift_ι _ _ _
  have hmono : Mono φ := by
    refine Preadditive.mono_of_cancel_zero _ fun {T} x hx => ?_
    have ht : x ≫ t = 0 := by rw [← hφ₁, ← Category.assoc, hx, zero_comp]
    have hl : x ≫ l = 0 := by rw [← hφ₂, ← Category.assoc, hx, zero_comp]
    have hy : kernel.lift t x ht ≫ kernel.map t b l r w = 0 := by
      refine (cancel_mono (kernel.ι b)).1 ?_
      rw [Category.assoc, hmap, ← Category.assoc, kernel.lift_ι, hl, zero_comp]
    have hy0 : kernel.lift t x ht = 0 := by
      rw [← Category.comp_id (kernel.lift t x ht), ← IsIso.hom_inv_id (kernel.map t b l r w),
        ← Category.assoc, hy, zero_comp]
    rw [← kernel.lift_ι t x ht, hy0, zero_comp]
  have hepi : Epi φ := by
    rw [epi_iff_surjective_up_to_refinements]
    intro A z
    obtain ⟨A₁, π₁, hπ₁, x, hx⟩ :=
      surjective_up_to_refinements_of_epi t (z ≫ pullback.fst r b)
    have hk : (x ≫ l - π₁ ≫ z ≫ pullback.snd r b) ≫ b = 0 := by
      have h1 : x ≫ l ≫ b = π₁ ≫ z ≫ pullback.snd r b ≫ b := by
        rw [← w, ← Category.assoc, ← hx, Category.assoc, Category.assoc, pullback.condition]
      rw [Preadditive.sub_comp, Category.assoc, Category.assoc, Category.assoc, h1, sub_self]
    let k : A₁ ⟶ kernel t :=
      kernel.lift b (x ≫ l - π₁ ≫ z ≫ pullback.snd r b) hk ≫ inv (kernel.map t b l r w)
    have hkι : k ≫ kernel.ι t ≫ l = x ≫ l - π₁ ≫ z ≫ pullback.snd r b := by
      show (kernel.lift b (x ≫ l - π₁ ≫ z ≫ pullback.snd r b) hk ≫
        inv (kernel.map t b l r w)) ≫ kernel.ι t ≫ l = _
      rw [← hmap, Category.assoc, IsIso.inv_hom_id_assoc, kernel.lift_ι]
    have hkt : k ≫ kernel.ι t ≫ t = 0 := by rw [kernel.condition, comp_zero]
    refine ⟨A₁, π₁, hπ₁, x - k ≫ kernel.ι t, ?_⟩
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hφ₁, Preadditive.sub_comp, Category.assoc, hkt,
        sub_zero, ← hx]
    · rw [Category.assoc, Category.assoc, hφ₂, Preadditive.sub_comp, Category.assoc, hkι]
      abel
  have : IsIso φ := isIso_of_mono_of_epi φ
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso φ) hφ₁ hφ₂

/-- In an abelian category the image of a morphism `f` factoring as `e ≫ i`, an epimorphism
followed by a monomorphism, is the source of `i`, over the target. -/
def imageIsoOfFac {X Y Z : C} (e : X ⟶ Y) (i : Y ⟶ Z) (f : X ⟶ Z) (hf : e ≫ i = f) [Epi e]
    [Mono i] : Y ≅ Abelian.image f := by
  have hz : i ≫ cokernel.π f = 0 := by
    refine (cancel_epi e).1 ?_
    rw [← Category.assoc, hf, cokernel.condition, comp_zero]
  have hu : kernel.lift (cokernel.π f) i hz ≫ Abelian.image.ι f = i := kernel.lift_ι _ _ _
  have hmono : Mono (kernel.lift (cokernel.π f) i hz) := mono_of_mono_fac hu
  have hfu : e ≫ kernel.lift (cokernel.π f) i hz = Abelian.factorThruImage f := by
    refine (cancel_mono (Abelian.image.ι f)).1 ?_
    rw [Category.assoc, hu, hf, Abelian.image.fac]
  have hepiu : Epi (kernel.lift (cokernel.π f) i hz) := by
    have : Epi (e ≫ kernel.lift (cokernel.π f) i hz) := by
      rw [hfu]; infer_instance
    exact epi_of_epi e _
  have : IsIso (kernel.lift (cokernel.π f) i hz) := isIso_of_mono_of_epi _
  exact asIso (kernel.lift (cokernel.π f) i hz)

/-- The isomorphism `CategoryTheory.Abelian.imageIsoOfFac` lies over `Z`: followed by the inclusion
of the image of `f`, its forward map is `i`. -/
theorem imageIsoOfFac_hom_comp {X Y Z : C} (e : X ⟶ Y) (i : Y ⟶ Z) (f : X ⟶ Z)
    (hf : e ≫ i = f) [Epi e] [Mono i] :
    (imageIsoOfFac e i f hf).hom ≫ Abelian.image.ι f = i :=
  kernel.lift_ι _ _ _

end CategoryTheory.Abelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    {E E' : CoherentAdicSystems B S hS F hF 𝓘}

/-! ### Kernel images of a surjection -/

/-- **For a surjection `π` the image in `E_m` of the kernel of `π_l`, `l ≥ m`, is the kernel of
`π_m`.** -/
def kernelImageAtIsoKernelOfEpi (π : E ⟶ E') (hπ : Epi π) (m l : ℕ) (h : m ≤ l) :
    kernel (π.hom.app (op m)) ≅ kernelImageAt B S hS F hF 𝓘 π m l h :=
  have := epi_kernelLevelMap B S hS F hF 𝓘 π hπ m l h
  Abelian.imageIsoOfFac (kernelLevelMap B S hS F hF 𝓘 π m l h) (kernel.ι (π.hom.app (op m)))
    (kernel.ι (π.hom.app (op l)) ≫ E.obj.map (homOfLE h).op)
    (kernelLevelMap_ι B S hS F hF 𝓘 π m l h)

/-- The identification of `AlgebraicGeometry.Space.kernelImageAtIsoKernelOfEpi` lies over the
inclusions into `E_m`. -/
theorem kernelImageAtIsoKernelOfEpi_hom_comp (π : E ⟶ E') (hπ : Epi π) (m l : ℕ) (h : m ≤ l) :
    (kernelImageAtIsoKernelOfEpi B S hS F hF 𝓘 π hπ m l h).hom ≫
        kernelImageAtIncl B S hS F hF 𝓘 π m l h =
      kernel.ι (π.hom.app (op m)) :=
  have := epi_kernelLevelMap B S hS F hF 𝓘 π hπ m l h
  Abelian.imageIsoOfFac_hom_comp (kernelLevelMap B S hS F hF 𝓘 π m l h)
    (kernel.ι (π.hom.app (op m))) (kernel.ι (π.hom.app (op l)) ≫ E.obj.map (homOfLE h).op)
    (kernelLevelMap_ι B S hS F hF 𝓘 π m l h)

variable (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ F)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)

/-- For a surjection the stable kernel image at level `m` is the kernel of `π_m`, over `E_m`. -/
def stableKernelImageIsoKernelOfEpi (π : E ⟶ E') (hπ : Epi π) (m : ℕ) :
    kernel (π.hom.app (op m)) ≅ stableKernelImage B S hS F hF 𝓘 hZ hN hIcart π m :=
  kernelImageAtIsoKernelOfEpi B S hS F hF 𝓘 π hπ m
    (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart π m)
    (le_kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart π m)

/-- The identification of `AlgebraicGeometry.Space.stableKernelImageIsoKernelOfEpi` lies over the
inclusions into `E_m`. -/
theorem stableKernelImageIsoKernelOfEpi_hom_comp (π : E ⟶ E') (hπ : Epi π) (m : ℕ) :
    (stableKernelImageIsoKernelOfEpi B S hS F hF 𝓘 hZ hN hIcart π hπ m).hom ≫
        stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart π m =
      kernel.ι (π.hom.app (op m)) :=
  kernelImageAtIsoKernelOfEpi_hom_comp B S hS F hF 𝓘 π hπ m _ _

/-- **The transition maps of the levelwise kernels of a surjection are eventually
isomorphisms**, when those kernels are annihilated by one power `𝓘 ^ t`. -/
theorem exists_isIso_kernelLevelMap_of_epi (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ F) (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (π : E ⟶ E') (hπ : Epi π) (t : ℕ) (ht : 0 < t)
    (hker : ∀ k : ℕ, idealPowerMultiple B S hS F hF 𝓘 t (kernel (π.hom.app (op k))) = ⊥) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (l : ℕ) (h : m ≤ l),
      IsIso (kernelLevelMap B S hS F hF 𝓘 π m l h) := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by lia⟩
  obtain ⟨c, hc⟩ :=
    stableKernelImageQuotientMap_eventually_isIso B S hS F hF 𝓘 hZ hN hIcart π n
  refine ⟨n + c, fun m hm l h => ?_⟩
  have hq := hc m hm l h
  let σ := stableKernelImageIsoKernelOfEpi B S hS F hF 𝓘 hZ hN hIcart π hπ
  have hbot : ∀ k : ℕ, idealPowerMultiple B S hS F hF 𝓘 (n + 1)
      (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart π k) = ⊥ := fun k =>
    idealPowerMultiple_eq_bot_of_iso B S hS F hF 𝓘 (σ k) (n + 1) (hker k)
  have hπ' := fun k => isIso_π_idealPowerMultiple_of_eq_bot B S hS F hF 𝓘 (n + 1) _ (hbot k)
  have hproj : IsIso (stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart π m l h) := by
    have hfac := π_comp_idealPowerQuotientMapOfHom B S hS F hF 𝓘 (n + 1)
      (stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart π m l h)
    have : stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart π m l h =
        cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
            (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart π l)).ι ≫
          idealPowerQuotientMapOfHom B S hS F hF 𝓘 (n + 1)
            (stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart π m l h) ≫
          inv (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
            (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart π m)).ι) := by
      rw [← Category.assoc, hfac, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [this]
    infer_instance
  have hkey : kernelLevelMap B S hS F hF 𝓘 π m l h =
      (σ l).hom ≫ stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart π m l h ≫ (σ m).inv := by
    rw [← Category.assoc ((σ l).hom), Iso.eq_comp_inv]
    refine (cancel_mono (stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart π m)).1 ?_
    rw [Category.assoc, Category.assoc, stableKernelImage_project_comp,
      stableKernelImageIsoKernelOfEpi_hom_comp, ← Category.assoc,
      stableKernelImageIsoKernelOfEpi_hom_comp, kernelLevelMap_ι]
  rw [hkey]
  infer_instance

/-- **The squares of a surjection of coherent adic systems are eventually pullback squares.**
Under the hypotheses of `AlgebraicGeometry.Space.exists_isIso_kernelLevelMap_of_epi`, from some
level `m₀` on, the square formed by `π_l`, `π_m` and the transition maps `E_l ⟶ E_m`,
`E'_l ⟶ E'_m` is a pullback square of `𝒪_F`-modules. -/
theorem exists_isPullback_transition_of_epi (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ F) (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (π : E ⟶ E') (hπ : Epi π) (t : ℕ) (ht : 0 < t)
    (hker : ∀ k : ℕ, idealPowerMultiple B S hS F hF 𝓘 t (kernel (π.hom.app (op k))) = ⊥) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (l : ℕ) (h : m ≤ l),
      IsPullback (π.hom.app (op l)) (E.obj.map (homOfLE h).op) (E'.obj.map (homOfLE h).op)
        (π.hom.app (op m)) := by
  obtain ⟨m₀, hm₀⟩ := exists_isIso_kernelLevelMap_of_epi B S hS F hF 𝓘 hZ hN hIcart π hπ t ht hker
  refine ⟨m₀, fun m hm l h => ?_⟩
  have := epi_app_of_epi B S hS F hF 𝓘 π hπ l
  have w : π.hom.app (op l) ≫ E'.obj.map (homOfLE h).op =
      E.obj.map (homOfLE h).op ≫ π.hom.app (op m) := (π.hom.naturality _).symm
  have hk : kernel.map (π.hom.app (op l)) (π.hom.app (op m)) (E.obj.map (homOfLE h).op)
      (E'.obj.map (homOfLE h).op) w = kernelLevelMap B S hS F hF 𝓘 π m l h := by
    refine (cancel_mono (kernel.ι (π.hom.app (op m)))).1 ?_
    rw [kernelLevelMap_ι, kernel.lift_ι]
  have : IsIso (kernel.map (π.hom.app (op l)) (π.hom.app (op m)) (E.obj.map (homOfLE h).op)
      (E'.obj.map (homOfLE h).op) w) := by
    rw [hk]; exact hm₀ m hm l h
  exact Abelian.isPullback_of_isIso_kernelMap w

end AlgebraicGeometry.Space

end
