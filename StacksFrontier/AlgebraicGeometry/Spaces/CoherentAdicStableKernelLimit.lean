module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicStableKernelQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFunctor

/-!
# The limit of the completed stable kernel images on an algebraic space

Let `F` be a Noetherian algebraic space, `𝓘 ⊆ 𝒪_F` a quasi-coherent sheaf of ideals and
`α : E ⟶ E'` a morphism of coherent `𝓘`-adic systems.  The stable kernel images
`AlgebraicGeometry.Space.stableKernelImage` form an inverse system
`AlgebraicGeometry.Space.stableKernelImageSystem` of coherent `𝒪_F`-modules which is *not* a
coherent adic system.  Applying the completion of Stacks 08B4 to each of its terms turns each of
them into one, and the transition maps of the stable kernel images make these completions into a
double system indexed by `ℕᵒᵖ × ℕᵒᵖ`.

The limit of this double system over the image level is a coherent adic system. By the second
stabilization `AlgebraicGeometry.Space.stableKernelImageQuotientMap_eventually_isIso`, for each
quotient level `n` the projection of the limit onto the `n`-th term of the completion of the
stable kernel image at any sufficiently high image level is an isomorphism, and all three
defining clauses of a coherent adic system transport along such an isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.idealPowerQuotientIsoOfIso` — the adic quotients of two isomorphic
  modules are isomorphic, compatibly with the quotient projections.
* `AlgebraicGeometry.Space.stableKernelImageCompletionDiagram` — the double system of the
  completed stable kernel images, the composite of the system of stable kernel images with the
  completion functor of Stacks 08B4.
* `AlgebraicGeometry.Space.stableKernelImageQuotientDiagram` — its slice at a fixed quotient
  level.
* `AlgebraicGeometry.Space.stableKernelImageLimitSystem` — the limit of the double system over
  the image level, and `AlgebraicGeometry.Space.stableKernelImageLimitπ` its projections.
* `AlgebraicGeometry.Space.coherentAdicKernel` — the kernel object: the limit system together
  with the proof that it is a coherent adic system.

## Main results

* `AlgebraicGeometry.Space.stableKernelImageLimitπ_eventually_isIso` — past the second
  stabilization the limit system is one of the completions, level by level.
* `AlgebraicGeometry.Space.stableKernelImageLimit_isCoherent` and
  `AlgebraicGeometry.Space.stableKernelImageLimit_isCoherentAdicSystem` — the limit of the
  double system is a coherent adic system.

## Implementation notes

The double system is indexed by `ℕᵒᵖ` twice and is zero-indexed in both variables: the quotient
level `n` represents the Stacks source's `𝓘 ^ (n + 1)` and the image level `m` its `E_{m + 1}`.

The completion is taken in the form `AlgebraicGeometry.Space.adicQuotientFunctor`, the functor
underlying `AlgebraicGeometry.Space.completionFunctor` (Stacks 08B4) before its target is cut
down to the coherent adic systems.  That functor carries no hypotheses, so the double system and
its limit are built with none; the three clauses of a coherent adic system are then supplied
directly — coherence of the terms of a completion by
`AlgebraicGeometry.Space.isCoherent_idealPowerQuotient`, annihilation by
`AlgebraicGeometry.Space.idealPowerMultiple_idealPowerQuotient_eq_bot` and the quotient clause by
`AlgebraicGeometry.Space.idealPowerQuotientQuotientIso`, which is exactly how
`AlgebraicGeometry.Space.isCoherentAdicSystem_adicQuotientSystem` assembles them.  Working with
the underlying functor also makes the identification of the terms of the double system with the
adic quotients of the stable kernel images hold by `rfl`, so no `eqToHom` appears.

The local Noetherianity needed for coherence of an adic quotient is extracted from the Noetherian
hypothesis `hN` as the `Fact` instance those statements are phrased with, and quasi-coherence of
`𝓘` from `hIcart` by Descent, Proposition 03DX(2); neither is a separate argument.

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

/-! ### Adic quotients of isomorphic modules -/

/-- The adic quotients of two isomorphic modules are isomorphic.  The isomorphism is the map
induced on the quotients, which is functorial, and
`AlgebraicGeometry.Space.π_comp_idealPowerQuotientMapOfHom` records that it lies over the
quotient projections. -/
def idealPowerQuotientIsoOfIso (k : ℕ) {M N : Modules.{u, u} B S hS F hF} (e : M ≅ N) :
    idealPowerQuotient B S hS F hF 𝓘 k M ≅ idealPowerQuotient B S hS F hF 𝓘 k N where
  hom := idealPowerQuotientMapOfHom B S hS F hF 𝓘 k e.hom
  inv := idealPowerQuotientMapOfHom B S hS F hF 𝓘 k e.inv
  hom_inv_id := by
    rw [← idealPowerQuotientMapOfHom_comp, e.hom_inv_id, idealPowerQuotientMapOfHom_id]
  inv_hom_id := by
    rw [← idealPowerQuotientMapOfHom_comp, e.inv_hom_id, idealPowerQuotientMapOfHom_id]

/-- The forward map of `AlgebraicGeometry.Space.idealPowerQuotientIsoOfIso` is the map induced on
the adic quotients. -/
@[simp]
theorem idealPowerQuotientIsoOfIso_hom (k : ℕ) {M N : Modules.{u, u} B S hS F hF} (e : M ≅ N) :
    (idealPowerQuotientIsoOfIso B S hS F hF 𝓘 k e).hom =
      idealPowerQuotientMapOfHom B S hS F hF 𝓘 k e.hom :=
  rfl

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ F)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {E E' : CoherentAdicSystems B S hS F hF 𝓘}

/-! ### The double system and its limit -/

/-- The double system of the completed stable kernel images.  The image level `m` indexes the
completions of the stable kernel images, each of which is itself an inverse system in the
quotient level. -/
def stableKernelImageCompletionDiagram (α : E ⟶ E') :
    ℕᵒᵖ ⥤ (ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF) :=
  stableKernelImageSystem B S hS F hF 𝓘 hZ hN hIcart α ⋙ adicQuotientFunctor B S hS F hF 𝓘

/-- The term of the double system at image level `m` and quotient level `n` is the `(n + 1)`-st
adic quotient of the stable kernel image at level `m`. -/
theorem stableKernelImageCompletionDiagram_obj_obj (α : E ⟶ E') (m n : ℕ) :
    ((stableKernelImageCompletionDiagram B S hS F hF 𝓘 hZ hN hIcart α).obj (op m)).obj (op n) =
      idealPowerQuotient B S hS F hF 𝓘 (n + 1)
        (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m) :=
  rfl

/-- The slice of the double system at a fixed quotient level `n`: the inverse system, in the
image level, of the `(n + 1)`-st adic quotients of the stable kernel images. -/
def stableKernelImageQuotientDiagram (α : E ⟶ E') (n : ℕ) :
    ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF :=
  stableKernelImageCompletionDiagram B S hS F hF 𝓘 hZ hN hIcart α ⋙
    (evaluation ℕᵒᵖ (Modules.{u, u} B S hS F hF)).obj (op n)

/-- The transition maps of the slice diagram are the maps induced on the adic quotients by the
transition maps of the stable kernel images. -/
theorem stableKernelImageQuotientDiagram_map (α : E ⟶ E') (n k m : ℕ) (h : k ≤ m) :
    (stableKernelImageQuotientDiagram B S hS F hF 𝓘 hZ hN hIcart α n).map (homOfLE h).op =
      idealPowerQuotientMapOfHom B S hS F hF 𝓘 (n + 1)
        (stableKernelImage_project B S hS F hF 𝓘 hZ hN hIcart α k m h) :=
  rfl

/-- The limit of the double system over the image level, an inverse system in the quotient
level. -/
def stableKernelImageLimitSystem (α : E ⟶ E') : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF :=
  limit (stableKernelImageCompletionDiagram B S hS F hF 𝓘 hZ hN hIcart α)

/-- The projection of the limit system onto the `(n + 1)`-st adic quotient of the stable kernel
image at image level `m`. -/
abbrev stableKernelImageLimitπ (α : E ⟶ E') (n m : ℕ) :
    (stableKernelImageLimitSystem B S hS F hF 𝓘 hZ hN hIcart α).obj (op n) ⟶
      idealPowerQuotient B S hS F hF 𝓘 (n + 1)
        (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m) :=
  (limit.π (stableKernelImageCompletionDiagram B S hS F hF 𝓘 hZ hN hIcart α) (op m)).app (op n)

/-- The terms of the limit system are the limits of the slice diagrams: limits in a functor
category are computed pointwise. -/
def stableKernelImageLimitSystem_objIso (α : E ⟶ E') (n : ℕ) :
    (stableKernelImageLimitSystem B S hS F hF 𝓘 hZ hN hIcart α).obj (op n) ≅
      limit (stableKernelImageQuotientDiagram B S hS F hF 𝓘 hZ hN hIcart α n) :=
  limitObjIsoLimitCompEvaluation
    (stableKernelImageCompletionDiagram B S hS F hF 𝓘 hZ hN hIcart α) (op n)

/-- A uniform stabilization bound makes the slice diagram eventually constant: `ℕᵒᵖ` has at most
one morphism between any two objects, so every morphism into `op (n + c)` is the one named by the
hypothesis. -/
theorem stableKernelImageQuotientDiagram_eventuallyConstant (α : E ⟶ E') (n c : ℕ)
    (h : ∀ m : ℕ, n + c ≤ m → ∀ l : ℕ, ∀ hml : m ≤ l,
      IsIso ((stableKernelImageQuotientDiagram B S hS F hF 𝓘 hZ hN hIcart α n).map
        (homOfLE hml).op)) :
    (stableKernelImageQuotientDiagram B S hS F hF 𝓘 hZ hN hIcart α n).IsEventuallyConstantTo
      (op (n + c)) := by
  intro i g
  have hl : n + c ≤ i.unop := leOfHom g.unop
  have hg : g = (homOfLE hl).op := Subsingleton.elim _ _
  subst hg
  exact h (n + c) le_rfl i.unop hl

/-- Past the second stabilization the limit system is one of the completions, level by
level.  For each quotient level `n` there is a constant `c` such that the projection of the
limit system onto the `(n + 1)`-st adic quotient of the stable kernel image at any image level
`m ≥ n + c` is an isomorphism. -/
theorem stableKernelImageLimitπ_eventually_isIso (α : E ⟶ E') (n : ℕ) :
    ∃ c : ℕ, ∀ m : ℕ, n + c ≤ m →
      IsIso (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n m) := by
  obtain ⟨c, hc⟩ := stableKernelImageQuotientMap_eventually_isIso B S hS F hF 𝓘 hZ hN hIcart α n
  have h := stableKernelImageQuotientDiagram_eventuallyConstant B S hS F hF 𝓘 hZ hN hIcart α n c
    fun m hm l hml => hc m hm l hml
  refine ⟨c, fun m hm => ?_⟩
  have hiso : IsIso (limit.π
      (stableKernelImageQuotientDiagram B S hS F hF 𝓘 hZ hN hIcart α n) (op m)) :=
    (h.precomp (homOfLE hm).op).isIso_π_of_isLimit (limit.isLimit _)
  change IsIso ((limit.π
    (stableKernelImageCompletionDiagram B S hS F hF 𝓘 hZ hN hIcart α) (op m)).app (op n))
  rw [← limitObjIsoLimitCompEvaluation_hom_π]
  change IsIso ((stableKernelImageLimitSystem_objIso B S hS F hF 𝓘 hZ hN hIcart α n).hom ≫
    limit.π (stableKernelImageQuotientDiagram B S hS F hF 𝓘 hZ hN hIcart α n) (op m))
  infer_instance

/-- At some image level the projections of the limit system onto the `(n + 1)`-st and
`(n + 2)`-nd adic quotients are both isomorphisms. -/
private theorem exists_isIso_limitπ_succ (α : E ⟶ E') (n : ℕ) :
    ∃ m : ℕ, IsIso (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n m) ∧
      IsIso (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α (n + 1) m) := by
  obtain ⟨c, hc⟩ := stableKernelImageLimitπ_eventually_isIso B S hS F hF 𝓘 hZ hN hIcart α n
  obtain ⟨d, hd⟩ := stableKernelImageLimitπ_eventually_isIso B S hS F hF 𝓘 hZ hN hIcart α (n + 1)
  exact ⟨n + c + d + 1, hc _ (by omega), hd _ (by omega)⟩

/-! ### The limit of the double system is a coherent adic system -/

/-- Every term of the limit system is coherent, being isomorphic to a term of one of the
completions of the stable kernel images. -/
theorem stableKernelImageLimit_isCoherent (α : E ⟶ E') (n : ℕ) :
    IsCoherent B S hS F hF
      ((stableKernelImageLimitSystem B S hS F hF 𝓘 hZ hN hIcart α).obj (op n)) := by
  have : Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hN.2.2⟩
  obtain ⟨m, _, -⟩ := exists_isIso_limitπ_succ B S hS F hF 𝓘 hZ hN hIcart α n
  refine (isCoherent.{u, u} B S hS F hF).prop_of_iso
    (asIso (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n m)).symm ?_
  exact isCoherent_idealPowerQuotient B S hS F hF 𝓘
    (isQuasicoherentOnSite_of_isCartesianOnAffineCharts _ hIcart) _
    (isCoherent_stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m) (n + 1)

/-- The limit of the double system of completed stable kernel images is a coherent adic
system.  By the second stabilization
`AlgebraicGeometry.Space.stableKernelImageQuotientMap_eventually_isIso`, each term of the limit
is isomorphic to an adic quotient of a stable kernel image, and all three defining clauses
transport along such isomorphisms.

For the quotient clause the two levels `n` and `n + 1` must be compared inside *one* completion,
so the image level is taken above both stabilization bounds; the projections of the limit are
then isomorphisms at both levels and are compatible with the transition maps, being components of
a natural transformation. -/
theorem stableKernelImageLimit_isCoherentAdicSystem (α : E ⟶ E') :
    IsCoherentAdicSystem B S hS F hF 𝓘
      (stableKernelImageLimitSystem B S hS F hF 𝓘 hZ hN hIcart α) := by
  refine ⟨stableKernelImageLimit_isCoherent B S hS F hF 𝓘 hZ hN hIcart α, fun n => ?_,
    fun n => ?_⟩
  · obtain ⟨m, hiso, -⟩ := exists_isIso_limitπ_succ B S hS F hF 𝓘 hZ hN hIcart α n
    have : Mono (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n m) :=
      @IsIso.mono_of_iso _ _ _ _ _ hiso
    exact idealPowerMultiple_eq_bot_of_mono B S hS F hF 𝓘
      (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n m) (n + 1)
      (idealPowerMultiple_idealPowerQuotient_eq_bot B S hS F hF 𝓘 (n + 1) _)
  · obtain ⟨m, h₀, h₁⟩ := exists_isIso_limitπ_succ B S hS F hF 𝓘 hZ hN hIcart α n
    refine ⟨idealPowerQuotientIsoOfIso B S hS F hF 𝓘 (n + 1)
        (asIso (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α (n + 1) m)) ≪≫
      idealPowerQuotientQuotientIso B S hS F hF 𝓘 (Nat.le_succ (n + 1))
          (stableKernelImage B S hS F hF 𝓘 hZ hN hIcart α m) ≪≫
        (asIso (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α n m)).symm, ?_⟩
    rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, idealPowerQuotientIsoOfIso_hom]
    simp only [← Category.assoc]
    rw [π_comp_idealPowerQuotientMapOfHom,
      Category.assoc
        (asIso (stableKernelImageLimitπ B S hS F hF 𝓘 hZ hN hIcart α (n + 1) m)).hom,
      π_comp_idealPowerQuotientQuotientIso_hom, Iso.comp_inv_eq]
    exact ((limit.π (stableKernelImageCompletionDiagram B S hS F hF 𝓘 hZ hN hIcart α)
      (op m)).naturality (homOfLE (Nat.le_succ n)).op).symm

/-! ### The kernel object -/

/-- The kernel of a morphism of coherent adic systems on a Noetherian algebraic space, the
limit of the double system of the completed stable kernel images. -/
def coherentAdicKernel (α : E ⟶ E') : CoherentAdicSystems B S hS F hF 𝓘 :=
  ⟨stableKernelImageLimitSystem B S hS F hF 𝓘 hZ hN hIcart α,
    stableKernelImageLimit_isCoherentAdicSystem B S hS F hF 𝓘 hZ hN hIcart α⟩

/-- The underlying inverse system of the kernel object is the limit system. -/
theorem coherentAdicKernel_obj (α : E ⟶ E') :
    (coherentAdicKernel B S hS F hF 𝓘 hZ hN hIcart α).obj =
      stableKernelImageLimitSystem B S hS F hF 𝓘 hZ hN hIcart α :=
  rfl

end AlgebraicGeometry.Space

end
