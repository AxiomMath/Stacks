module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicStableKernelLimit

/-!
# The kernel in `Coh(F, 𝓘)` on a Noetherian algebraic space

Let `F` be a Noetherian algebraic space, `𝓘 ⊆ 𝒪_F` a quasi-coherent sheaf of ideals and
`α : E ⟶ E'` a morphism of coherent `𝓘`-adic systems.  The object
`AlgebraicGeometry.Space.coherentAdicKernel` — the limit over the image level of the double system
of the completed stable kernel images — is a coherent adic system.  **This file proves that it is
the kernel of `α` in `Coh(F, 𝓘)`, and concludes that `Coh(F, 𝓘)` has all kernels.**

The kernel is *not* the levelwise kernel; the module documentation of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicKernel` explains which clause of a coherent adic
system the levelwise kernel fails.

The universal property is proved directly, as at scheme level.  A morphism `β : H ⟶ E` of
coherent adic systems killed by `α` factors through every stable kernel image: at a level `l`
above the stabilization level of `E_m` the component `β_l` factors through `ker(α_l)` and hence
through its image in `E_m`, and the transition `H_l ⟶ H_m` is an epimorphism while the stable
kernel image is a subobject of `E_m`, so the factorization descends to `H_m`.  Composing with the
projection onto the `(n + 1)`-st adic quotient and descending once more along the transitions of
`H` — possible because the target is annihilated by `𝓘 ^ (n + 1)` — produces a cone on the double
system, whose limiting morphism is the required factorization.  Uniqueness holds because a
morphism of coherent adic systems into the limit system is determined by its composite with the
inclusion into `E`: the comparison
`AlgebraicGeometry.Space.stableKernelImageCompletionToLevel` at equal levels is a monomorphism,
the stable kernel image at level `n` being already annihilated by `𝓘 ^ (n + 1)` and hence equal to
its own `(n + 1)`-st adic quotient.

## Main definitions

* `AlgebraicGeometry.Space.coherentAdicKernelι` — the inclusion of the kernel into the source.
* `AlgebraicGeometry.Space.stableKernelImageLift` — the factorization of a morphism killed by `α`
  through a stable kernel image.
* `AlgebraicGeometry.Space.stableKernelImageCompletionToLevel` — the comparison from an adic
  quotient of a stable kernel image to a term of `E`.
* `AlgebraicGeometry.Space.stableKernelImageLimitIncl` — the inclusion of the limit system
  into `E`.
* `AlgebraicGeometry.Space.stableKernelImageLiftCone` — the cone on the double system built from a
  morphism killed by `α`.

## Main results

* `AlgebraicGeometry.Space.coherentAdicKernelι_comp` and
  `AlgebraicGeometry.Space.coherentAdicKernelIsLimit` — **the universal property of the
  kernel.**
* `AlgebraicGeometry.Space.hasKernel_coherentAdicSystems` and
  `AlgebraicGeometry.Space.hasKernels_coherentAdicSystems` — **`Coh(F, 𝓘)` has all kernels** on a
  Noetherian algebraic space.
* `AlgebraicGeometry.Space.coherentAdicKernelToLevelwiseKernel` — the canonical comparison from a
  term of the kernel to the kernel of the corresponding component of `α`.

## Implementation notes

The Noetherian hypothesis is carried as the pair of explicit arguments `hZ`, `hN` spelling
`AlgebraicGeometry.Space.IsNoetherian`, together with quasi-coherence of `𝓘` in the form
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`.  `HasKernels` is therefore a *theorem*
taking those three arguments rather than an instance: `AlgebraicGeometry.Space.IsNoetherian` is
not a typeclass, and `AlgebraicGeometry.Space.CoherentAdicSystems` itself carries no such
hypothesis.

Every statement below names the transition maps of the double system by the maps they are on the
adic quotients — `AlgebraicGeometry.Space.idealPowerQuotientMapOfHom` in the image level and
`AlgebraicGeometry.Space.idealPowerQuotientMapOfLE` in the quotient level — rather than as
`CategoryTheory.Functor.map` of
`AlgebraicGeometry.Space.stableKernelImageCompletionDiagram`.  The two spellings agree by `rfl`,
but only the first keeps the *types* appearing in a composite syntactically equal, which is what
`rw` needs; the identifications with the diagram are made once, inside the proofs, where
`CategoryTheory.Limits.limit.w` and the naturality of
`CategoryTheory.Limits.limit.π` are brought in.

The system is indexed by `ℕᵒᵖ` and is zero-indexed: the term at `n` is the Stacks source's
`E_{n + 1}`.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
* [Stacks Project, Tag 08B4](https://stacks.math.columbia.edu/tag/08B4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-! ### Annihilation along a morphism -/

/-- **A morphism into a module annihilated by `𝓘 ^ j` annihilates `𝓘 ^ k` of its source** for
`j ≤ k`: the morphism is linear on sections, and `𝓘 ^ k` is contained in `𝓘 ^ j`. -/
theorem idealPowerMultiple_ι_comp_eq_zero_of_le (j k : ℕ) (hjk : j ≤ k)
    {M P : Modules.{u, u} B S hS F hF} (g : M ⟶ P)
    (hP : idealPowerMultiple B S hS F hF 𝓘 j P = ⊥) :
    (idealPowerMultiple B S hS F hF 𝓘 k M).ι ≫ g = 0 := by
  have hann := (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 j P).mp hP
  refine (idealPowerMultiple_ι_comp_eq_zero_iff B S hS F hF 𝓘 k g).mpr fun U r hr x => ?_
  rw [(g.val.app (op U)).hom.map_smul r x]
  exact hann U r (Ideal.pow_le_pow_right hjk hr) _

/-- **The projection onto the quotient by a vanishing submodule is an isomorphism.** -/
theorem isIso_cokernel_π_of_eq_bot {M : Modules.{u, u} B S hS F hF} (P : M.Submodule)
    (h : P = ⊥) : IsIso (cokernel.π P.ι) :=
  cokernel.π_of_zero (submodule_ι_eq_zero_of_eq_bot B S hS F hF h)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ F)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {E E' : CoherentAdicSystems B S hS F hF 𝓘}

/-! ### Descending a morphism along the transitions of a coherent adic system -/

/-- The transition of a functor on `ℕᵒᵖ` at equal levels is the identity. -/
private theorem map_homOfLE_refl {C : Type*} [Category C] (G : ℕᵒᵖ ⥤ C) (n : ℕ) :
    G.map (homOfLE (le_refl n)).op = 𝟙 (G.obj (op n)) := by
  rw [← G.map_id]; rfl

/-- Transitions of a functor on `ℕᵒᵖ` compose to the transition between the outer levels. -/
private theorem map_homOfLE_comp {C : Type*} [Category C] (G : ℕᵒᵖ ⥤ C) {i j k : ℕ}
    (h₁ : i ≤ j) (h₂ : j ≤ k) :
    G.map (homOfLE h₂).op ≫ G.map (homOfLE h₁).op = G.map (homOfLE (h₁.trans h₂)).op := by
  rw [← G.map_comp]; rfl

/-- The transitions of a coherent adic system are epimorphisms. -/
private theorem epi_map_homOfLE (H : CoherentAdicSystems B S hS F hF 𝓘) {j k : ℕ} (h : j ≤ k) :
    Epi (H.obj.map (homOfLE h).op) := by
  induction k, h using Nat.le_induction with
  | base => rw [map_homOfLE_refl]; infer_instance
  | succ k h ih =>
    have := epi_map_le_succ B S hS F hF 𝓘 H.property k
    rw [← map_homOfLE_comp H.obj h (Nat.le_succ k)]
    infer_instance

/-- **A morphism to a module annihilated by `𝓘 ^ (n + 1)` descends along the transitions of a
coherent adic system.**  For `n ≤ m` every morphism out of `H_m` with such a target factors
through the transition `H_m ⟶ H_n`.

One step of the induction is the quotient clause: `H_m` is `H_{m+1} / 𝓘 ^ (m + 1) H_{m+1}`, and a
morphism into a module annihilated by `𝓘 ^ (n + 1) ⊇ 𝓘 ^ (m + 1)` kills the subsheaf being
divided out. -/
theorem exists_coherentAdicSystemDesc (H : CoherentAdicSystems B S hS F hF 𝓘) (n m : ℕ)
    (h : n ≤ m) {P : Modules.{u, u} B S hS F hF}
    (hP : idealPowerMultiple B S hS F hF 𝓘 (n + 1) P = ⊥) (f : H.obj.obj (op m) ⟶ P) :
    ∃ g : H.obj.obj (op n) ⟶ P, H.obj.map (homOfLE h).op ≫ g = f := by
  induction m, h using Nat.le_induction with
  | base =>
    exact ⟨f, by rw [map_homOfLE_refl, Category.id_comp]⟩
  | succ m h ih =>
    have hz : (idealPowerMultiple B S hS F hF 𝓘 (m + 1) (H.obj.obj (op (m + 1)))).ι ≫ f = 0 :=
      idealPowerMultiple_ι_comp_eq_zero_of_le B S hS F hF 𝓘 (n + 1) (m + 1) (by omega) f hP
    obtain ⟨d, hd⟩ := exists_desc_of_transition B S hS F hF 𝓘 H.property m f hz
    obtain ⟨g, hg⟩ := ih d
    refine ⟨g, ?_⟩
    rw [← map_homOfLE_comp H.obj h (Nat.le_succ m), Category.assoc, hg, hd]

/-! ### Factoring a morphism killed by `α` through a stable kernel image -/

/-- **A morphism killed by `α` factors through every stable kernel image.**  At the stabilization
level `l` of `E_m` the component `β_l` factors through `ker(α_l)` and hence through the image of
`ker(α_l)` in `E_m`, which is the stable kernel image; the transition `H_l ⟶ H_m` is an
epimorphism, so the factorization descends to `H_m` by the lifting property of a strong
epimorphism against the monomorphism `S_m ⟶ E_m`. -/
theorem exists_stableKernelImageLift (α : E ⟶ E') {H : CoherentAdicSystems B S hS F hF 𝓘}
    (β : H ⟶ E) (hβ : β ≫ α = 0) (m : ℕ) :
    ∃ f : H.obj.obj (op m) ⟶ stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m,
      f ≫ stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m = β.hom.app (op m) := by
  have h : m ≤ kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m :=
    le_kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m
  have hepi := epi_map_homOfLE B S hS F hF 𝓘 H h
  have hz : β.hom.app (op (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)) ≫
      α.hom.app (op (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)) = 0 :=
    congrArg (fun f : H ⟶ E' =>
      f.hom.app (op (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m))) hβ
  have ha : (kernel.lift (α.hom.app (op (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)))
          (β.hom.app (op (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m))) hz ≫
        Abelian.factorThruImage
          (kernel.ι (α.hom.app (op (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m))) ≫
            E.obj.map (homOfLE h).op)) ≫
        stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m =
      H.obj.map (homOfLE h).op ≫ β.hom.app (op m) := by
    change (_ ≫ Abelian.factorThruImage _) ≫ Abelian.image.ι _ = _
    rw [Category.assoc, Abelian.image.fac, ← Category.assoc, kernel.lift_ι]
    exact (β.hom.naturality (homOfLE h).op).symm
  have hstrong : StrongEpi (H.obj.map (homOfLE h).op) := strongEpi_of_epi _
  have hsq : CommSq (kernel.lift (α.hom.app
        (op (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m)))
          (β.hom.app (op (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m))) hz ≫
      Abelian.factorThruImage
        (kernel.ι (α.hom.app (op (kernelStableLevel B S hS F hF 𝓘 hZ hN hIcart α m))) ≫
          E.obj.map (homOfLE h).op))
      (H.obj.map (homOfLE h).op)
      (stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m) (β.hom.app (op m)) := ⟨ha⟩
  have hlift : hsq.HasLift :=
    (StrongEpi.llp (f := H.obj.map (homOfLE h).op)
      (stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m)).sq_hasLift hsq
  exact ⟨hsq.lift, hsq.fac_right⟩

/-- The chosen factorization of a morphism killed by `α` through the stable kernel image at a
level. -/
def stableKernelImageLift (α : E ⟶ E') {H : CoherentAdicSystems B S hS F hF 𝓘} (β : H ⟶ E)
    (hβ : β ≫ α = 0) (m : ℕ) :
    H.obj.obj (op m) ⟶ stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m :=
  (exists_stableKernelImageLift B S hS F hF 𝓘 hZ hN hIcart α β hβ m).choose

/-- The factorization through the stable kernel image lies over the component of `β`. -/
theorem stableKernelImageLift_ι (α : E ⟶ E') {H : CoherentAdicSystems B S hS F hF 𝓘} (β : H ⟶ E)
    (hβ : β ≫ α = 0) (m : ℕ) :
    stableKernelImageLift B S hS F hF 𝓘 hZ hN hIcart α β hβ m ≫
        stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m = β.hom.app (op m) :=
  (exists_stableKernelImageLift B S hS F hF 𝓘 hZ hN hIcart α β hβ m).choose_spec

/-- The factorizations through the stable kernel images form a morphism of inverse systems: both
composites with the inclusion into `E_n` are the component of `β` precomposed with a transition of
`H`, and the inclusion is a monomorphism. -/
theorem stableKernelImageLift_naturality (α : E ⟶ E')
    {H : CoherentAdicSystems B S hS F hF 𝓘} (β : H ⟶ E) (hβ : β ≫ α = 0) (n m : ℕ) (h : n ≤ m) :
    H.obj.map (homOfLE h).op ≫ stableKernelImageLift B S hS F hF 𝓘 hZ hN hIcart α β hβ n =
      stableKernelImageLift B S hS F hF 𝓘 hZ hN hIcart α β hβ m ≫
        stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α n m h := by
  refine (cancel_mono (stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α n)).mp ?_
  rw [Category.assoc, stableKernelImageLift_ι, Category.assoc,
    stableKernelImage_project_comp, ← Category.assoc, stableKernelImageLift_ι]
  exact β.hom.naturality _

/-! ### The comparison from an adic quotient to a term of `E` -/

/-- **The comparison from the `(n + 1)`-st adic quotient of the stable kernel image at level
`m ≥ n` to `E_n`**, induced by the inclusion into `E_m` followed by the transition map of `E`,
which annihilates `𝓘 ^ (n + 1)` of its source because `E_n` is annihilated by `𝓘 ^ (n + 1)`. -/
def stableKernelImageCompletionToLevel (α : E ⟶ E') (n m : ℕ) (h : n ≤ m) :
    idealPowerQuotient B S hS F hF 𝓘 (n + 1)
        (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m) ⟶ E.obj.obj (op n) :=
  cokernel.desc _ (stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m ≫
      E.obj.map (homOfLE h).op)
    (idealPowerMultiple_ι_comp_eq_zero_of_le B S hS F hF 𝓘 (n + 1) (n + 1) le_rfl _
      (E.property.2.1 n))

/-- On representatives the comparison to `E_n` is the inclusion of the stable kernel image
followed by the transition map of `E`. -/
theorem stableKernelImageCompletionToLevel_fac (α : E ⟶ E') (n m : ℕ) (h : n ≤ m) :
    cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
          (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m)).ι ≫
        stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n m h =
      stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α m ≫ E.obj.map (homOfLE h).op :=
  cokernel.π_desc _ _ _

/-- The comparison to `E_n` is annihilated by `α_n`: the stable kernel image is. -/
theorem stableKernelImageCompletionToLevel_comp_alpha (α : E ⟶ E') (n m : ℕ) (h : n ≤ m) :
    stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n m h ≫
      α.hom.app (op n) = 0 := by
  refine (cancel_epi (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
    (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m)).ι)).mp ?_
  rw [comp_zero, ← Category.assoc, stableKernelImageCompletionToLevel_fac, Category.assoc,
    α.hom.naturality, ← Category.assoc, stableKernelImageIncl_comp, zero_comp]

/-- The comparisons to `E_n` are compatible with the transitions of the double system in the image
level. -/
theorem stableKernelImageCompletionToLevel_transition (α : E ⟶ E') (n k m : ℕ) (hnk : n ≤ k)
    (hkm : k ≤ m) :
    idealPowerQuotientMapOfHom B S hS F hF 𝓘 (n + 1)
          (stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α k m hkm) ≫
        stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n k hnk =
      stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n m (hnk.trans hkm) := by
  refine (cancel_epi (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
    (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m)).ι)).mp ?_
  rw [← Category.assoc, π_comp_idealPowerQuotientMapOfHom, Category.assoc,
    stableKernelImageCompletionToLevel_fac, ← Category.assoc, stableKernelImage_project_comp,
    Category.assoc, map_homOfLE_comp, stableKernelImageCompletionToLevel_fac]

/-- The comparisons to the terms of `E` are compatible with the transitions of the completion in
the quotient level. -/
theorem stableKernelImageCompletionToLevel_naturality (α : E ⟶ E') (n k m : ℕ) (hnk : n ≤ k)
    (hkm : k ≤ m) :
    idealPowerQuotientMapOfLE B S hS F hF 𝓘 (Nat.add_le_add_right hnk 1)
          (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m) ≫
        stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n m (hnk.trans hkm) =
      stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α k m hkm ≫
        E.obj.map (homOfLE hnk).op := by
  refine (cancel_epi (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (k + 1)
    (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m)).ι)).mp ?_
  rw [← Category.assoc, π_comp_idealPowerQuotientMapOfLE,
    stableKernelImageCompletionToLevel_fac, ← Category.assoc,
    stableKernelImageCompletionToLevel_fac, Category.assoc, map_homOfLE_comp]

/-- **At equal levels the comparison to `E_n` is a monomorphism.**  The stable kernel image at
level `n` is annihilated by `𝓘 ^ (n + 1)`, so the projection onto its `(n + 1)`-st adic quotient
is an isomorphism, and the comparison becomes the inclusion of the stable kernel image into `E_n`
precomposed with that isomorphism. -/
theorem stableKernelImageCompletionToLevel_mono (α : E ⟶ E') (n : ℕ) :
    Mono (stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n n le_rfl) := by
  have hiso : IsIso (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
      (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α n)).ι) :=
    isIso_cokernel_π_of_eq_bot B S hS F hF _
      (stableKernelImage_idealPowerMultiple_eq_bot B S hS F hF 𝓘 hZ hN hIcart α n)
  have hr : cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
        (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α n)).ι ≫
      stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n n le_rfl =
      stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α n := by
    rw [stableKernelImageCompletionToLevel_fac, map_homOfLE_refl, Category.comp_id]
  have he : stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n n le_rfl =
      inv (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
          (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α n)).ι) ≫
        stableKernelImageIncl B S hS F hF 𝓘 hZ hN hIcart α n := by
    rw [← hr, IsIso.inv_hom_id_assoc]
  rw [he]
  infer_instance

/-! ### The inclusion of the limit system into the source -/

/-- The composite of a projection of the limit system with a comparison to `E_n` does not depend
on the image level: the projections are compatible with the transitions of the double system, and
so are the comparisons. -/
theorem stableKernelImageLimitπ_comp_toLevel (α : E ⟶ E') (n m : ℕ) (h : n ≤ m) :
    stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n m ≫
        stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n m h =
      stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n n ≫
        stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n n le_rfl := by
  have hw : stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n m ≫
        idealPowerQuotientMapOfHom B S hS F hF 𝓘 (n + 1)
          (stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α n m h) =
      stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n n :=
    congrArg (fun g => g.app (op n))
      (limit.w (stableKernelImageCompletionDiagram B S hS F hF 𝓘 hZ hN hIcart α) (homOfLE h).op)
  rw [← stableKernelImageCompletionToLevel_transition B S hS F hF 𝓘 hZ hN hIcart α n n m le_rfl h,
    ← Category.assoc, hw]

/-- **The inclusion of the limit system into the source system**, the comparison to `E_n` at equal
levels composed with the projection of the limit. -/
def stableKernelImageLimitIncl (α : E ⟶ E') :
    stableKernelImageLimitSystem B S hS F hF 𝓘 hZ hN hIcart α ⟶ E.obj where
  app n := stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n.unop n.unop ≫
    stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n.unop n.unop le_rfl
  naturality {k n} f := by
    have h : n.unop ≤ k.unop := leOfHom f.unop
    have hnπ : (stableKernelImageLimitSystem B S hS F hF 𝓘 hZ hN hIcart α).map
          (homOfLE h).op ≫ stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n.unop k.unop =
        stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α k.unop k.unop ≫
          idealPowerQuotientMapOfLE B S hS F hF 𝓘 (Nat.add_le_add_right h 1)
            (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α k.unop) :=
      (limit.π (stableKernelImageCompletionDiagram B S hS F hF 𝓘 hZ hN hIcart α) k).naturality
        (homOfLE h).op
    change (stableKernelImageLimitSystem B S hS F hF 𝓘 hZ hN hIcart α).map (homOfLE h).op ≫
      (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n.unop n.unop ≫
        stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n.unop n.unop le_rfl) = _
    rw [← stableKernelImageLimitπ_comp_toLevel B S hS F hF 𝓘 hZ hN hIcart α n.unop k.unop h,
      ← Category.assoc, hnπ, Category.assoc,
      stableKernelImageCompletionToLevel_naturality B S hS F hF 𝓘 hZ hN hIcart α
        n.unop k.unop k.unop h le_rfl, ← Category.assoc]
    congr 2

/-- The inclusion of the limit system into the source is killed by `α`: it factors through the
stable kernel images, which `α` annihilates. -/
theorem stableKernelImageLimitIncl_comp (α : E ⟶ E') :
    stableKernelImageLimitIncl B S hS F hF 𝓘 hZ hN hIcart α ≫ α.hom = 0 := by
  refine NatTrans.ext (funext fun n => ?_)
  change (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n.unop n.unop ≫
    stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n.unop n.unop le_rfl) ≫
      α.hom.app n = 0
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α
    n.unop n.unop ≫ z)
      (stableKernelImageCompletionToLevel_comp_alpha B S hS F hF 𝓘 hZ hN hIcart α
        n.unop n.unop le_rfl)).trans comp_zero

/-- **A morphism of coherent adic systems into the limit system is determined by its composite
with the inclusion into `E`.**  At the quotient level `n` the two candidates agree after
projection to the image level `n` — the comparison to `E_n` being a monomorphism — and every other
projection is reached from that one by a transition of the double system, after precomposing with
a transition of the source, which is an epimorphism. -/
theorem stableKernelImageLimitIncl_hom_ext (α : E ⟶ E') (H : CoherentAdicSystems B S hS F hF 𝓘)
    (a b : H.obj ⟶ stableKernelImageLimitSystem B S hS F hF 𝓘 hZ hN hIcart α)
    (h : a ≫ stableKernelImageLimitIncl B S hS F hF 𝓘 hZ hN hIcart α =
      b ≫ stableKernelImageLimitIncl B S hS F hF 𝓘 hZ hN hIcart α) : a = b := by
  refine limit.hom_ext fun m => NatTrans.ext (funext fun n => ?_)
  have hn : n.unop ≤ max n.unop m.unop := le_max_left _ _
  have hm : m.unop ≤ max n.unop m.unop := le_max_right _ _
  have hepi := epi_map_homOfLE B S hS F hF 𝓘 H hn
  have hd : a.app (op (max n.unop m.unop)) ≫ stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart
        α (max n.unop m.unop) (max n.unop m.unop) =
      b.app (op (max n.unop m.unop)) ≫ stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart
        α (max n.unop m.unop) (max n.unop m.unop) := by
    have hmono := stableKernelImageCompletionToLevel_mono B S hS F hF 𝓘 hZ hN hIcart α
      (max n.unop m.unop)
    refine (cancel_mono (stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α
      (max n.unop m.unop) (max n.unop m.unop) le_rfl)).mp ?_
    rw [Category.assoc, Category.assoc]
    exact congrArg (fun g => g.app (op (max n.unop m.unop))) h
  have hw : stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α (max n.unop m.unop)
          (max n.unop m.unop) ≫
        idealPowerQuotientMapOfHom B S hS F hF 𝓘 (max n.unop m.unop + 1)
          (stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α m.unop
            (max n.unop m.unop) hm) =
      stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α (max n.unop m.unop) m.unop :=
    congrArg (fun g => g.app (op (max n.unop m.unop)))
      (limit.w (stableKernelImageCompletionDiagram B S hS F hF 𝓘 hZ hN hIcart α) (homOfLE hm).op)
  have hnπ : (stableKernelImageLimitSystem B S hS F hF 𝓘 hZ hN hIcart α).map (homOfLE hn).op ≫
        stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n.unop m.unop =
      stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α (max n.unop m.unop) m.unop ≫
        idealPowerQuotientMapOfLE B S hS F hF 𝓘 (Nat.add_le_add_right hn 1)
          (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m.unop) :=
    (limit.π (stableKernelImageCompletionDiagram B S hS F hF 𝓘 hZ hN hIcart α) m).naturality
      (homOfLE hn).op
  have key : ∀ c : H.obj ⟶ stableKernelImageLimitSystem B S hS F hF 𝓘 hZ hN hIcart α,
      H.obj.map (homOfLE hn).op ≫ c.app n ≫
          stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n.unop m.unop =
        (c.app (op (max n.unop m.unop)) ≫
            stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α (max n.unop m.unop)
              (max n.unop m.unop)) ≫
          (idealPowerQuotientMapOfHom B S hS F hF 𝓘 (max n.unop m.unop + 1)
              (stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α m.unop
                (max n.unop m.unop) hm) ≫
            idealPowerQuotientMapOfLE B S hS F hF 𝓘 (Nat.add_le_add_right hn 1)
              (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m.unop)) := by
    intro c
    rw [← Category.assoc, c.naturality (homOfLE hn).op, Category.assoc, hnπ, ← hw]
    simp only [Category.assoc]
  refine (cancel_epi (H.obj.map (homOfLE hn).op)).mp ?_
  change H.obj.map (homOfLE hn).op ≫ a.app n ≫
      stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n.unop m.unop =
    H.obj.map (homOfLE hn).op ≫ b.app n ≫
      stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n.unop m.unop
  rw [key a, key b, hd]

/-! ### The cone built from a morphism killed by `α` -/

/-- The canonical morphism from the `n`-th term of a system `H` mapping to `E` by a morphism
killed by `α` to the `(n + 1)`-st adic quotient of the stable kernel image at level `m`: the
factorization through the stable kernel image at level `m`, composed with the quotient projection,
descended along the transitions of `H`. -/
def stableKernelImageQuotientLift (α : E ⟶ E') {H : CoherentAdicSystems B S hS F hF 𝓘}
    (β : H ⟶ E) (hβ : β ≫ α = 0) (n m : ℕ) :
    H.obj.obj (op n) ⟶ idealPowerQuotient B S hS F hF 𝓘 (n + 1)
      (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m) :=
  (exists_coherentAdicSystemDesc B S hS F hF 𝓘 H n (max n m) (le_max_left _ _)
    (idealPowerMultiple_idealPowerQuotient_eq_bot B S hS F hF 𝓘 (n + 1)
      (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m))
    (H.obj.map (homOfLE (le_max_right n m)).op ≫
      stableKernelImageLift B S hS F hF 𝓘 hZ hN hIcart α β hβ m ≫
        cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
          (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m)).ι)).choose

/-- The defining property of `AlgebraicGeometry.Space.stableKernelImageQuotientLift`, at any level
`l` above both `n` and `m`. -/
theorem stableKernelImageQuotientLift_fac (α : E ⟶ E')
    {H : CoherentAdicSystems B S hS F hF 𝓘} (β : H ⟶ E) (hβ : β ≫ α = 0) (n m l : ℕ)
    (hn : n ≤ l) (hm : m ≤ l) :
    H.obj.map (homOfLE hn).op ≫
        stableKernelImageQuotientLift B S hS F hF 𝓘 hZ hN hIcart α β hβ n m =
      H.obj.map (homOfLE hm).op ≫
        stableKernelImageLift B S hS F hF 𝓘 hZ hN hIcart α β hβ m ≫
          cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
            (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m)).ι := by
  have h := (exists_coherentAdicSystemDesc B S hS F hF 𝓘 H n (max n m) (le_max_left _ _)
    (idealPowerMultiple_idealPowerQuotient_eq_bot B S hS F hF 𝓘 (n + 1)
      (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m))
    (H.obj.map (homOfLE (le_max_right n m)).op ≫
      stableKernelImageLift B S hS F hF 𝓘 hZ hN hIcart α β hβ m ≫
        cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
          (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m)).ι)).choose_spec
  change H.obj.map (homOfLE (le_max_left n m)).op ≫
    stableKernelImageQuotientLift B S hS F hF 𝓘 hZ hN hIcart α β hβ n m = _ at h
  have ht : max n m ≤ l := max_le hn hm
  rw [← map_homOfLE_comp H.obj (le_max_left n m) ht, Category.assoc, h, ← Category.assoc,
    map_homOfLE_comp]

/-- The morphisms `AlgebraicGeometry.Space.stableKernelImageQuotientLift` at a fixed image level
are natural in the quotient level. -/
theorem stableKernelImageQuotientLift_naturality (α : E ⟶ E')
    {H : CoherentAdicSystems B S hS F hF 𝓘} (β : H ⟶ E) (hβ : β ≫ α = 0) (n k m : ℕ)
    (h : n ≤ k) :
    H.obj.map (homOfLE h).op ≫
        stableKernelImageQuotientLift B S hS F hF 𝓘 hZ hN hIcart α β hβ n m =
      stableKernelImageQuotientLift B S hS F hF 𝓘 hZ hN hIcart α β hβ k m ≫
        idealPowerQuotientMapOfLE B S hS F hF 𝓘 (Nat.add_le_add_right h 1)
          (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m) := by
  have hk : k ≤ max k m := le_max_left _ _
  have hm : m ≤ max k m := le_max_right _ _
  have hepi := epi_map_homOfLE B S hS F hF 𝓘 H hk
  refine (cancel_epi (H.obj.map (homOfLE hk).op)).mp ?_
  rw [← Category.assoc, ← H.obj.map_comp]
  change H.obj.map (homOfLE (h.trans hk)).op ≫ _ = _
  rw [stableKernelImageQuotientLift_fac B S hS F hF 𝓘 hZ hN hIcart α β hβ n m _
      (h.trans hk) hm,
    reassoc_of% stableKernelImageQuotientLift_fac B S hS F hF 𝓘 hZ hN hIcart α β hβ k m _ hk hm]
  exact congrArg (fun z => H.obj.map (homOfLE hm).op ≫
      stableKernelImageLift B S hS F hF 𝓘 hZ hN hIcart α β hβ m ≫ z)
    (π_comp_idealPowerQuotientMapOfLE B S hS F hF 𝓘 (Nat.add_le_add_right h 1)
      (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m)).symm

/-- The morphisms `AlgebraicGeometry.Space.stableKernelImageQuotientLift` at a fixed quotient level
are compatible with the transitions of the double system in the image level. -/
theorem stableKernelImageQuotientLift_transition (α : E ⟶ E')
    {H : CoherentAdicSystems B S hS F hF 𝓘} (β : H ⟶ E) (hβ : β ≫ α = 0) (n k m : ℕ)
    (h : k ≤ m) :
    stableKernelImageQuotientLift B S hS F hF 𝓘 hZ hN hIcart α β hβ n m ≫
        idealPowerQuotientMapOfHom B S hS F hF 𝓘 (n + 1)
          (stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α k m h) =
      stableKernelImageQuotientLift B S hS F hF 𝓘 hZ hN hIcart α β hβ n k := by
  have hn : n ≤ max n m := le_max_left _ _
  have hm : m ≤ max n m := le_max_right _ _
  have hepi := epi_map_homOfLE B S hS F hF 𝓘 H hn
  refine (cancel_epi (H.obj.map (homOfLE hn).op)).mp ?_
  rw [← Category.assoc, stableKernelImageQuotientLift_fac B S hS F hF 𝓘 hZ hN hIcart α β hβ
      n m _ hn hm,
    stableKernelImageQuotientLift_fac B S hS F hF 𝓘 hZ hN hIcart α β hβ n k _ hn (h.trans hm),
    Category.assoc, Category.assoc]
  rw [π_comp_idealPowerQuotientMapOfHom, ← Category.assoc
      (stableKernelImageLift B S hS F hF 𝓘 hZ hN hIcart α β hβ m),
    ← stableKernelImageLift_naturality B S hS F hF 𝓘 hZ hN hIcart α β hβ k m h,
    ← map_homOfLE_comp H.obj h hm]
  simp only [Category.assoc]

/-- **The cone on the double system built from a morphism killed by `α`**, with summit the source
system of that morphism. -/
def stableKernelImageLiftCone (α : E ⟶ E') {H : CoherentAdicSystems B S hS F hF 𝓘} (β : H ⟶ E)
    (hβ : β ≫ α = 0) :
    Cone (stableKernelImageCompletionDiagram B S hS F hF 𝓘 hZ hN hIcart α) where
  pt := H.obj
  π :=
    { app m :=
        { app n := stableKernelImageQuotientLift B S hS F hF 𝓘 hZ hN hIcart α β hβ
            n.unop m.unop
          naturality {n k} f := stableKernelImageQuotientLift_naturality B S hS F hF 𝓘 hZ hN
            hIcart α β hβ k.unop n.unop m.unop (leOfHom f.unop) }
      naturality {m k} f := by
        refine NatTrans.ext (funext fun n => ?_)
        change (𝟙 _) ≫ stableKernelImageQuotientLift B S hS F hF 𝓘 hZ hN hIcart α β hβ
          n.unop k.unop = _
        rw [Category.id_comp]
        exact (stableKernelImageQuotientLift_transition B S hS F hF 𝓘 hZ hN hIcart α β hβ
          n.unop k.unop m.unop (leOfHom f.unop)).symm }

/-- The limiting morphism of `AlgebraicGeometry.Space.stableKernelImageLiftCone` is a
factorization of `β` through the inclusion of the limit system into `E`. -/
theorem stableKernelImageLiftCone_lift_fac (α : E ⟶ E')
    {H : CoherentAdicSystems B S hS F hF 𝓘} (β : H ⟶ E) (hβ : β ≫ α = 0) :
    limit.lift _ (stableKernelImageLiftCone B S hS F hF 𝓘 hZ hN hIcart α β hβ) ≫
        stableKernelImageLimitIncl B S hS F hF 𝓘 hZ hN hIcart α = β.hom := by
  refine NatTrans.ext (funext fun n => ?_)
  change (limit.lift _ (stableKernelImageLiftCone B S hS F hF 𝓘 hZ hN hIcart α β hβ)).app n ≫
    (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n.unop n.unop ≫
      stableKernelImageCompletionToLevel B S hS F hF 𝓘 hZ hN hIcart α n.unop n.unop le_rfl) = _
  have hl : (limit.lift _
          (stableKernelImageLiftCone B S hS F hF 𝓘 hZ hN hIcart α β hβ)).app n ≫
        stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n.unop n.unop =
      stableKernelImageQuotientLift B S hS F hF 𝓘 hZ hN hIcart α β hβ n.unop n.unop :=
    congrArg (fun g => g.app n)
      (limit.lift_π (stableKernelImageLiftCone B S hS F hF 𝓘 hZ hN hIcart α β hβ) n)
  have hf := stableKernelImageQuotientLift_fac B S hS F hF 𝓘 hZ hN hIcart α β hβ
    n.unop n.unop n.unop le_rfl le_rfl
  simp only [map_homOfLE_refl, Category.id_comp] at hf
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [hl, hf]
  refine (Category.assoc _ _ _).trans ?_
  rw [stableKernelImageCompletionToLevel_fac, map_homOfLE_refl, Category.comp_id]
  exact stableKernelImageLift_ι B S hS F hF 𝓘 hZ hN hIcart α β hβ n.unop

/-! ### The universal property -/

/-- **The inclusion of the kernel into the source system.** -/
def coherentAdicKernelι (α : E ⟶ E') :
    coherentAdicKernel B S hS F hF 𝓘 hZ hN hIcart α ⟶ E :=
  ObjectProperty.homMk (stableKernelImageLimitIncl B S hS F hF 𝓘 hZ hN hIcart α)

/-- **The inclusion of the kernel is killed by `α`.** -/
theorem coherentAdicKernelι_comp (α : E ⟶ E') :
    coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart α ≫ α = 0 :=
  ObjectProperty.hom_ext (IsCoherentAdicSystem B S hS F hF 𝓘)
    (stableKernelImageLimitIncl_comp B S hS F hF 𝓘 hZ hN hIcart α)

/-- **The universal property of the kernel of a morphism of coherent adic systems.**  A morphism
`β : H ⟶ E` killed by `α` factors uniquely through
`AlgebraicGeometry.Space.coherentAdicKernelι`. -/
def coherentAdicKernelIsLimit (α : E ⟶ E') :
    IsLimit (KernelFork.ofι (coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart α)
      (coherentAdicKernelι_comp B S hS F hF 𝓘 hZ hN hIcart α)) :=
  KernelFork.IsLimit.ofι _ _
    (fun β hβ => ObjectProperty.homMk
      (limit.lift _ (stableKernelImageLiftCone B S hS F hF 𝓘 hZ hN hIcart α β hβ)))
    (fun β hβ => ObjectProperty.hom_ext (IsCoherentAdicSystem B S hS F hF 𝓘)
      (stableKernelImageLiftCone_lift_fac B S hS F hF 𝓘 hZ hN hIcart α β hβ))
    (fun β hβ _a ha => ObjectProperty.hom_ext (IsCoherentAdicSystem B S hS F hF 𝓘)
      (stableKernelImageLimitIncl_hom_ext B S hS F hF 𝓘 hZ hN hIcart α _ _ _
        ((congrArg InducedCategory.Hom.hom ha).trans
          (stableKernelImageLiftCone_lift_fac B S hS F hF 𝓘 hZ hN hIcart α β hβ).symm)))

include hZ hN hIcart in
/-- **A morphism of coherent adic systems on a Noetherian algebraic space has a kernel in
`Coh(F, 𝓘)`.** -/
theorem hasKernel_coherentAdicSystems (α : E ⟶ E') : HasKernel α :=
  ⟨⟨⟨_, coherentAdicKernelIsLimit B S hS F hF 𝓘 hZ hN hIcart α⟩⟩⟩

include hZ hN hIcart in
/-- **The category `Coh(F, 𝓘)` of coherent adic systems on a Noetherian algebraic space has all
kernels.** -/
theorem hasKernels_coherentAdicSystems : HasKernels (CoherentAdicSystems B S hS F hF 𝓘) where
  has_limit α := hasKernel_coherentAdicSystems B S hS F hF 𝓘 hZ hN hIcart α

/-! ### The relation with the levelwise kernels -/

/-- **The canonical comparison from the `n`-th term of the kernel to the kernel of `α_n`.**  The
kernel in `Coh(F, 𝓘)` is not the levelwise kernel and this comparison need not be invertible; what
holds is that it lies over the inclusions into `E_n`. -/
def coherentAdicKernelToLevelwiseKernel (α : E ⟶ E') (n : ℕ) :
    (coherentAdicKernel B S hS F hF 𝓘 hZ hN hIcart α).obj.obj (op n) ⟶
      kernel (α.hom.app (op n)) :=
  kernel.lift _ ((coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart α).hom.app (op n))
    (congrArg (fun f : coherentAdicKernel B S hS F hF 𝓘 hZ hN hIcart α ⟶ E' =>
        f.hom.app (op n))
      (coherentAdicKernelι_comp B S hS F hF 𝓘 hZ hN hIcart α))

/-- The comparison with the levelwise kernel lies over the inclusion of the kernel into `E_n`. -/
theorem coherentAdicKernelToLevelwiseKernel_ι (α : E ⟶ E') (n : ℕ) :
    coherentAdicKernelToLevelwiseKernel B S hS F hF 𝓘 hZ hN hIcart α n ≫
        kernel.ι (α.hom.app (op n)) =
      (coherentAdicKernelι B S hS F hF 𝓘 hZ hN hIcart α).hom.app (op n) :=
  kernel.lift_ι _ _ _

end AlgebraicGeometry.Space

end
