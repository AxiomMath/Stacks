module

public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Transition
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.TransitionKernelTwistVanishing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Adjunction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjective
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.LongExactSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generation of a coherent adic system by the completion of a coherent module

This file carries the **first paragraph of the proof of [Stacks, Tag 0885]**: granted the uniform
`H¹`-vanishing of [Stacks, Tag 0884], every object of `Coh(X, 𝓘)` receives an epimorphism from
the completion of a coherent `𝒪_X`-module. That statement is the hypothesis `hGen` of
`Stacks.Algebraization.isEquivalence_completionFunctor_of_exists_epi`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProjective.lean`), which is the
source's last paragraph; together the two give
Grothendieck existence for a projective morphism.

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `f : X ⟶ Spec A` proper, `L` an invertible
`𝒪_X`-module ample relative to `f` and `𝓘 = I · 𝒪_X`. Let `(F_n)` be an object of `Coh(X, 𝓘)`.
The vanishing taken as the hypothesis `hvan` is

  `H¹(X, Ker(F_{n+1} ⟶ F_n) ⊗ L ^⊗ d) = 0`  for every `n ≥ 0` and every `d ≥ d₀`,

*one `d₀` for the whole system* — verbatim the conclusion of
`Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule`, so that the two
statements compose with no transport. Everything else is discharged here.

## The route

1. **Ampleness.** Over the affine base `Spec A`, relative ampleness is ampleness
   ([Stacks, Tag 01VK], `Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple`).
2. **Serre's global generation.** `X` is locally Noetherian because `f` is of finite type over a
   Noetherian base, so the lowest term `F_1` of the system — the term at `op 0`, the system being
   zero-indexed — is coherent, hence quasi-coherent of finite type. Clause (8) of
   [Stacks, Tag 01Q3] (`Stacks.AmpleLocalGeneration.isQuotientOfNegativeTwists_of_isAmple`,
   unconditional) presents it as a quotient of a finite direct sum
   `Q = ⊕_{j} L ^⊗ (-d_j)` with every `d_j ≥ d₀`.
3. **Lifting through the tower.** Each transition map `F_{n+1} ⟶ F_n` is an epimorphism with
   kernel `Ker(F_{n+1} ⟶ F_n)`, so it sits in a short exact sequence. A morphism out of
   `L ^⊗ (-d)` lifts along it as soon as `H¹(X, Ker ⊗ L ^⊗ d)` vanishes, which `hvan` supplies
   at every `d_j`; lifting is inherited by the finite direct sum `Q`. Recursion on `n` then turns
   the epimorphism `q₀ : Q ⟶ F_1` into a compatible system `q_n : Q ⟶ F_n`.
4. **The adjunction.** A compatible system is a cone, hence a morphism `Q ⟶ lim F_n`, and
   `Stacks.Algebraization.completionHomLimitEquiv` ([Stacks, Tag 0880], unconditional) turns it
   into a morphism `Q^∧ ⟶ (F_n)` of `Coh(X, 𝓘)` — `Q` is coherent, being a finite direct sum of
   invertible modules on a locally Noetherian scheme.
5. **Surjectivity.** The normalisation
   `Stacks.Algebraization.completionProjection_homToAdicSystem` identifies the composite of the
   projection `Q ⟶ (Q^∧)_1` with the component of that morphism at the lowest level as `q₀`,
   which is an epimorphism; so the component is one, and [Stacks, Tag 087Y]
   (`Stacks.Coherent.epi_iff_epi_app_zero`, unconditional) upgrades it to an epimorphism of
   `Coh(X, 𝓘)`.

## Main results

* `Stacks.Algebraization.exists_epi_completionFunctor_of_vanishing` — the generation step, with
  the uniform `H¹`-vanishing of [Stacks, Tag 0884] as the single hypothesis `hvan`.

## Implementation notes

**The lifting property is isolated as `Stacks.Algebraization.LiftsAlong`.** Writing `Hom(Q, -)`
as a product of groups of global sections and chasing the resulting diagram is avoided: what the
argument needs of `Q` is only that every morphism out of it lifts along the transition maps, and
that property is manifestly stable under isomorphism of `Q` (`liftsAlong_of_iso`), under finite
direct sums (`liftsAlong_of_isBilimit` — a morphism out of a bilimit is its family of components),
and transportable along a fully faithful functor (`liftsAlong_of_isEquivalence`). The cohomology
enters once, for `Q = 𝒪_X`, where a morphism out of the structure sheaf *is* a global section
(`AlgebraicGeometry.Scheme.Modules.sectionsTopEquiv` and `SheafOfModules.unitHomEquiv`) and the
long exact sequence applies directly
(`Stacks.SerreAffinenessCriterion.surjective_app_of_isZero_hgroup_one`, unconditional — no
quasi-coherence, no hypothesis on `X`).

**The twist is cancelled with the addition law, not with the monoidal structure.** Tensoring on
the right by `L ^⊗ d` is an autoequivalence of `X.Modules`
(`Stacks.AmpleCohomologicalCriterion.isEquivalence_tensorRight`) carrying `L ^⊗ (-d)` to `𝒪_X`,
and the identification is `Stacks.Ample.tensorPowModuleAddIso` followed by
`Stacks.Ample.tensorPowModuleZeroIso`, both stated with
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf`. So no monoidal instance on `X.Modules`
has to be activated in this file, and no `eqToHom` gymnastics beyond the single `eqToIso` for
`-d + d = 0`.

**Why the lifting is stated for a *family* of degrees.** Clause (8) of Tag 01Q3 returns a direct
sum `⊕_j L ^⊗ (-d_j)` indexed by `Fin r` with the degrees only bounded below by the requested
`n₀`, not equal to it. Nothing is lost: the lift is produced summand by summand, and `hvan` holds
at every `d ≥ d₀`, so taking `n₀ = d₀` serves every summand at once. Taking the index type in
`Type 0` is what makes the coherence of the direct sum available.

**Sections as compatible families.** `SheafOfModules.unitHomEquiv` lands in
`SheafOfModules.sections`, a family of sections over every open; the long exact sequence gives
surjectivity of the sections over `⊤` only. `AlgebraicGeometry.Scheme.Modules.sectionsTopEquiv`
is the bridge, `⊤` being terminal in the lattice of opens, and
`surjective_sectionsMap_of_isZero_hgroup` is the translation.

**No tag attribute is attached.** This is one paragraph of the proof of Stacks 0885, not the
statement of a numbered result; the tag sits on
`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjective` and its H-projective
companion in `StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProjective.lean`.

## References

* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 0884](https://stacks.math.columbia.edu/tag/0884)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 087Y](https://stacks.math.columbia.edu/tag/087Y)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)

universe u

namespace Stacks.Algebraization

/-! ### Lifting a morphism through an epimorphism -/

/-- `Q` lifts along `ψ` when every morphism `Q ⟶ N` factors through `ψ : M ⟶ N`. -/
private def LiftsAlong {C : Type*} [Category C] {M N : C} (ψ : M ⟶ N) (Q : C) : Prop :=
  ∀ u : Q ⟶ N, ∃ v : Q ⟶ M, v ≫ ψ = u

/-- Lifting along `ψ` is an isomorphism invariant of the source. -/
private theorem liftsAlong_of_iso {C : Type*} [Category C] {M N : C} (ψ : M ⟶ N) {Q Q' : C}
    (e : Q' ≅ Q) (h : LiftsAlong ψ Q) : LiftsAlong ψ Q' := by
  intro u
  obtain ⟨v, hv⟩ := h (e.inv ≫ u)
  refine ⟨e.hom ≫ v, ?_⟩
  rw [Category.assoc, hv, ← Category.assoc, e.hom_inv_id, Category.id_comp]

/-- **A direct sum lifts along `ψ` as soon as each summand does.** A morphism out of a bilimit
is the family of its components, each of which lifts; the lifts assemble through the colimit
property of the bicone. -/
private theorem liftsAlong_of_isBilimit {C : Type*} [Category C] [HasZeroMorphisms C]
    {M N : C} (ψ : M ⟶ N) {ι : Type*} {F : ι → C} (b : Bicone F) (hb : b.IsBilimit)
    (h : ∀ i, LiftsAlong ψ (F i)) : LiftsAlong ψ b.pt := by
  intro u
  choose v hv using fun i => h i (b.ι i ≫ u)
  refine ⟨hb.isColimit.desc ⟨M, Discrete.natTrans fun i => v i.as⟩, ?_⟩
  refine hb.isColimit.hom_ext fun j => ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [hb.isColimit.fac]
  exact hv j.as

/-- **Lifting along `ψ` is transported by an equivalence.** A lift of `T u` along `T ψ` is the
image of a unique morphism, whose composite with `ψ` is `u` because `T` is faithful.

The equivalence is an explicit argument rather than an instance: the functor used below is
declared at the `SheafOfModules` spelling of the category of modules on a scheme, and the
instance is not found again at the `AlgebraicGeometry.Scheme.Modules` spelling, although the two
are definitionally equal. -/
private theorem liftsAlong_of_isEquivalence {C D : Type*} [Category C] [Category D]
    {M N Q : C} (ψ : M ⟶ N) (T : C ⥤ D) (hT : T.IsEquivalence)
    (h : LiftsAlong (T.map ψ) (T.obj Q)) : LiftsAlong ψ Q := by
  have := hT
  intro u
  obtain ⟨v, hv⟩ := h (T.map u)
  refine ⟨T.preimage v, ?_⟩
  apply T.map_injective
  rw [T.map_comp, T.map_preimage, hv]

/-! ### From vanishing `H¹` to a lift of a twist of an invertible module -/

/-- Surjectivity of `Γ(X, -)` on the last term of a short exact sequence, read on the sections of
the underlying sheaf: a section is determined by, and may be built from, its value on `⊤`. -/
private theorem surjective_sectionsMap_of_isZero_hgroup {X : Scheme.{u}}
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ 1 S.X₁)) :
    Function.Surjective (SheafOfModules.sectionsMap S.g) := by
  have hsurj : Function.Surjective
      (ConcreteCategory.hom (Scheme.Modules.Hom.app S.g (⊤ : X.Opens))) :=
    Stacks.SerreAffinenessCriterion.surjective_app_of_isZero_hgroup_one X ⊤ hS h
  intro s
  obtain ⟨y, hy⟩ := hsurj ((Scheme.Modules.sectionsTopEquiv S.X₃).symm s)
  refine ⟨Scheme.Modules.sectionsTopEquiv S.X₂ y, ?_⟩
  refine PresheafOfModules.sections_ext _ _ fun U => ?_
  rw [Scheme.Modules.sectionsMap_val, Scheme.Modules.sectionsTopEquiv_val,
    Scheme.Modules.Hom.app_presheaf_map, hy, ← Scheme.Modules.sectionsTopEquiv_val,
    Equiv.apply_symm_apply]

/-- **The structure sheaf lifts along the last map of a short exact sequence whose first term has
vanishing `H¹`.** A morphism out of `𝒪_X` is a global section, and global sections are surjective
there by the long exact cohomology sequence. -/
@[sga "6 II 2.1.2" "a), b)"]
private theorem liftsAlong_unitModule {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (h : IsZero (Hgroup X.ringCatSheaf ⊤ 1 S.X₁)) :
    LiftsAlong S.g (Scheme.unitModule X) := by
  intro u
  obtain ⟨t, ht⟩ := surjective_sectionsMap_of_isZero_hgroup hS h
    (SheafOfModules.unitHomEquiv S.X₃ u)
  refine ⟨(SheafOfModules.unitHomEquiv S.X₂).symm t,
    (SheafOfModules.unitHomEquiv S.X₃).injective ?_⟩
  refine (SheafOfModules.unitHomEquiv_comp_apply _ _).trans ?_
  exact (congrArg (SheafOfModules.sectionsMap S.g)
    ((SheafOfModules.unitHomEquiv S.X₂).apply_symm_apply t)).trans ht

/-- **A negative twist of an invertible module lifts along the last map of a short exact sequence
whose first term has vanishing `H¹` after the opposite twist.** Tensoring by `L ^⊗ d` is an
autoequivalence carrying `L ^⊗ (-d)` to `𝒪_X`, so the statement is the previous one transported
through it. -/
private theorem liftsAlong_tensorPowModule {X : Scheme.{u}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (d : ℤ) {S : ShortComplex X.Modules}
    (hS : S.ShortExact)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ 1
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
          ((isSheaf_structureRingPresheaf X))⟩).obj (S.X₁)).obj
        ((Stacks.Ample.tensorPowModule X L d)))))) :
    LiftsAlong S.g (Stacks.Ample.tensorPowModule X L (-d)) := by
  refine liftsAlong_of_isEquivalence S.g
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
          (isSheaf_structureRingPresheaf X)⟩).flip.obj
      (Stacks.Ample.tensorPowModule X L d))
    (Stacks.AmpleCohomologicalCriterion.isEquivalence_tensorRight X
      (Stacks.Ample.tensorPowModule X L d)) ?_
  refine liftsAlong_of_iso _
    (Q := Scheme.unitModule X)
    (Stacks.Ample.tensorPowModuleAddIso X L (-d) d ≪≫
      eqToIso (congrArg (Stacks.Ample.tensorPowModule X L) (neg_add_cancel d)) ≪≫
      Stacks.Ample.tensorPowModuleZeroIso X L) ?_
  exact liftsAlong_unitModule
    (Stacks.AmpleCohomologicalCriterion.shortExact_map_tensorRight X
      (Stacks.Ample.tensorPowModule X L d) hS) h

/-! ### Coherence of a finite direct sum -/

/-- A module isomorphic to a finite direct sum of coherent modules is coherent, in the bicone
presentation. -/
private theorem isCoherent_of_iso_biconePt {X : Scheme.{u}} {ι : Type*} [Finite ι]
    {F : ι → X.Modules} (b : Bicone F) (hb : b.IsBilimit) {Q : X.Modules} (e : Q ≅ b.pt)
    (hF : ∀ i, _root_.SheafOfModules.IsCoherent (F i)) :
    _root_.SheafOfModules.IsCoherent Q := by
  have : HasCoproduct F := ⟨⟨⟨b.toCocone, hb.isColimit⟩⟩⟩
  have e' : b.pt ≅ ∐ F := hb.isColimit.coconePointUniqueUpToIso (colimit.isColimit _)
  exact AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent
    ((Stacks.SheafOfModules.coherentModules X.ringCatSheaf).prop_of_iso (e ≪≫ e').symm
      (Stacks.SheafOfModules.isCoherent_sigma F fun i =>
        AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent (hF i)))

/-! ### The compatible system of lifts through the tower -/

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- The compatible system of maps `Q ⟶ F_n` obtained by lifting `q₀ : Q ⟶ F_0` one level at a
time. -/
private noncomputable def towerLift (𝓕 : Stacks.Coherent.CoherentAdicSystems I) (Q : X.Modules)
    (q₀ : Q ⟶ 𝓕.obj.obj (op 0))
    (hl : ∀ n : ℕ, LiftsAlong (𝓕.obj.map (homOfLE (Nat.le_succ n)).op) Q) :
    (n : ℕ) → (Q ⟶ 𝓕.obj.obj (op n))
  | 0 => q₀
  | n + 1 => (hl n (towerLift 𝓕 Q q₀ hl n)).choose

/-- The defining property of `Stacks.Algebraization.towerLift`: each term composed with the
transition map is the previous one. -/
private theorem towerLift_succ (𝓕 : Stacks.Coherent.CoherentAdicSystems I) (Q : X.Modules)
    (q₀ : Q ⟶ 𝓕.obj.obj (op 0))
    (hl : ∀ n : ℕ, LiftsAlong (𝓕.obj.map (homOfLE (Nat.le_succ n)).op) Q) (n : ℕ) :
    towerLift 𝓕 Q q₀ hl (n + 1) ≫ 𝓕.obj.map (homOfLE (Nat.le_succ n)).op =
      towerLift 𝓕 Q q₀ hl n :=
  (hl n (towerLift 𝓕 Q q₀ hl n)).choose_spec

/-- The system `Stacks.Algebraization.towerLift` is compatible with every transition map of the
system, not only the successor ones: the morphisms of `ℕᵒᵖ` are a subsingleton, so each is the
composite of successor steps. -/
private theorem towerLift_comp (𝓕 : Stacks.Coherent.CoherentAdicSystems I) (Q : X.Modules)
    (q₀ : Q ⟶ 𝓕.obj.obj (op 0))
    (hl : ∀ n : ℕ, LiftsAlong (𝓕.obj.map (homOfLE (Nat.le_succ n)).op) Q)
    {m n : ℕ} (h : n ≤ m) :
    ∀ a : op m ⟶ op n,
      towerLift 𝓕 Q q₀ hl m ≫ 𝓕.obj.map a = towerLift 𝓕 Q q₀ hl n := by
  induction m, h using Nat.le_induction with
  | base =>
      intro a
      rw [Subsingleton.elim a (𝟙 (op n)), 𝓕.obj.map_id, Category.comp_id]
  | succ m hm ih =>
      intro a
      rw [Subsingleton.elim a ((homOfLE (Nat.le_succ m)).op ≫ (homOfLE hm).op),
        𝓕.obj.map_comp, ← Category.assoc, towerLift_succ, ih]

/-- The cone on the system with vertex `Q` assembled from the compatible system of lifts. -/
private noncomputable def towerCone (𝓕 : Stacks.Coherent.CoherentAdicSystems I) (Q : X.Modules)
    (q₀ : Q ⟶ 𝓕.obj.obj (op 0))
    (hl : ∀ n : ℕ, LiftsAlong (𝓕.obj.map (homOfLE (Nat.le_succ n)).op) Q) : Cone 𝓕.obj where
  pt := Q
  π :=
    { app := fun j => towerLift 𝓕 Q q₀ hl j.unop
      naturality := fun j k a => by
        dsimp
        rw [Category.id_comp]
        exact (towerLift_comp 𝓕 Q q₀ hl (leOfHom a.unop) a).symm }

/-! ### The generation step -/

/-- Every coherent adic system receives an epimorphism from the completion of a coherent module,
granted the uniform `H¹`-vanishing of Stacks 0884. -/
public theorem exists_epi_completionFunctor_of_vanishing
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (𝓕 : Stacks.Coherent.CoherentAdicSystems
      (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f))
    (hvan : ∃ d₀ : ℤ, ∀ (n : ℕ) (d : ℤ), d₀ ≤ d →
      IsZero (Hgroup X.ringCatSheaf ⊤ 1
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
            ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))⟩).obj
          ((Stacks.Coherent.transitionKernel 𝓕 n))).obj
          ((Stacks.Ample.tensorPowModule X L d)))))) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∃ (P : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
      (p : (Stacks.Algebraization.completionFunctor X
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f)).obj P ⟶ 𝓕), Epi p := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨d₀, hd₀⟩ := hvan
  -- the lowest term of the system is coherent, hence quasi-coherent of finite type
  have hF₀ : _root_.SheafOfModules.IsCoherent (𝓕.obj.obj (op 0)) := 𝓕.property.1 0
  obtain ⟨hqc, hft⟩ :=
    _root_.Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      (𝓕.obj.obj (op 0))
  -- Serre's global generation, untwisted
  obtain ⟨S₀, r, dd, b, hb, e₂, hse, hX₃, -, hdd⟩ :=
    Stacks.AmpleLocalGeneration.isQuotientOfNegativeTwists_of_isAmple L
      ((Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f L).mp hL) d₀
      (𝓕.obj.obj (op 0)) hqc hft
  -- the short exact sequences of the tower
  have hSC : ∀ n : ℕ, (ShortComplex.mk (kernel.ι (𝓕.obj.map (homOfLE (Nat.le_succ n)).op))
      (𝓕.obj.map (homOfLE (Nat.le_succ n)).op) (kernel.condition _)).ShortExact := fun n =>
    { exact := ShortComplex.exact_kernel _
      mono_f := inferInstance
      epi_g := 𝓕.property.epi_map_succ n }
  -- the lifting property of the chosen direct sum
  have hl : ∀ n : ℕ, LiftsAlong (𝓕.obj.map (homOfLE (Nat.le_succ n)).op) S₀.X₂ := fun n =>
    liftsAlong_of_iso _ e₂ <| liftsAlong_of_isBilimit _ b hb fun j =>
      liftsAlong_tensorPowModule L (dd j) (hSC n) (hd₀ (n + 1) (dd j) (hdd j))
  -- coherence of the chosen direct sum
  have hQcoh : _root_.SheafOfModules.IsCoherent S₀.X₂ :=
    isCoherent_of_iso_biconePt b hb e₂ fun j =>
      @Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X _
        (Stacks.Ample.tensorPowModule X L (-dd j))
        (inferInstanceAs (Stacks.Ample.IsInvertibleModule X
          (Stacks.Ample.tensorPowModule X L (-dd j))))
  -- assemble
  have : Epi S₀.g := hse.epi_g
  let P : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf := ⟨S₀.X₂, hQcoh⟩
  let q₀ : S₀.X₂ ⟶ 𝓕.obj.obj (op 0) := S₀.g ≫ eqToHom hX₃
  have : Epi q₀ := epi_comp _ _
  let g : Stacks.Algebraization.coherentObj P ⟶ limit 𝓕.obj :=
    limit.lift 𝓕.obj (towerCone 𝓕 S₀.X₂ q₀ hl)
  refine ⟨P, Stacks.Algebraization.homToAdicSystem P 𝓕 g, ?_⟩
  refine (Stacks.Coherent.epi_iff_epi_app_zero _ _).mpr ?_
  have key := Stacks.Algebraization.completionProjection_homToAdicSystem P 𝓕 g (op 0)
  rw [show g ≫ limit.π 𝓕.obj (op 0) = q₀ from limit.lift_π _ _] at key
  exact epi_of_epi_fac key

end Stacks.Algebraization

end
