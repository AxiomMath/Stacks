module

public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.MeasureComparison
public import StacksFrontier.AlgebraicGeometry.Duality.AffinePushforwardQcohExact

/-!
# The measure of the upper half of a splitting of [Stacks, Tag 0C1L]

`Stacks.GlueSquishFactor.exists_split_isAlmostIso_of_algebraHom` factors an almost isomorphism
`f : X' ⟶ X` through a finite quasi-coherent subalgebra `𝒜` of `f_*𝒪_{X'}` as

`X' --p--> Spec_X(𝒜) --q--> X`

with both halves again almost isomorphisms, and
`Stacks.GlueSquishFactor.sumSheafMultiplicity_cokernel_structureUnitHom_relativeSpecToBase_lt`
makes the measure `Stacks.GlueSquishFactor.measureOver` of the *lower* half drop strictly. This
file does the same for the *upper* half and assembles both drops, so that the splitting clause of
the hypothesis `hsplit` of
`Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso` is available at `μ = measureOver`
whenever a subalgebra proper at both ends is given.

The measure of the upper half is a sum over the points of `Spec_X(𝒜)`, while every drop in the
tree is a sum over the points of `X`. The passage between them is the direct image along `q`:
`Stacks.GlueSquishFactor.sumSheafMultiplicity_le_pushforward` bounds a total multiplicity by that
of its direct image, and `q` is affine, so
`Stacks.AlgebraicGeometry.AffineQcohExactness.preservesColimit_parallelPair_zero` carries
`q_*(p_*𝒪_{X'}/𝒪_{Spec_X(𝒜)})` to the cokernel of `q_*(𝒪_{Spec_X(𝒜)} ⟶ p_*𝒪_{X'})`.

## The identification of the pushforward with the pushforward algebra is an equality

What makes that last step usable is that the two comparisons

* `q_*𝒪_{Spec_X(𝒜)} = 𝒜` — `Stacks.GlueSquishFactor.pushforward_obj_unitModule`;
* `q_*(p_*𝒪_{X'}) = (p ≫ q)_*𝒪_{X'}` —
  `Stacks.GlueSquishFactor.pushforward_obj_underlyingModule_pushforwardAlgebra`;

hold **by `rfl`**, not merely up to isomorphism, so the morphism `q_*(𝒪 ⟶ p_*𝒪_{X'})` already
*is* a morphism `𝒜 ⟶ f_*𝒪_{X'}` of `𝒪_X`-modules and the drop
`Stacks.GlueSquishFactor.sumSheafMultiplicity_cokernel_lt_of_mem_supp_left` applies to it with no
transport. Both sides unfold to the same `ModuleCat.restrictScalars` of the same unit presheaf of
modules over the same ring presheaf `U ↦ Γ(Spec_X(𝒜), q⁻¹U)`: `Scheme.Modules.pushforward` is
`PresheafOfModules.pushforward₀` followed by a restriction of scalars along
`Functor.whiskerRight q.c _`, and `Stacks.RelativeSpec.AlgebraSheaf.underlyingModule` of
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebra q` is a restriction of scalars along
`(sheafCompose _ (forget₂ CommRingCat RingCat)).map ⟨q.c⟩`, which is the same natural
transformation. In particular no comparison between `AlgebraicGeometry.Scheme.ringCatSheaf` —
a `TopCat.Sheaf` — and the `CategoryTheory.Sheaf (Opens.grothendieckTopology _)` in which
`underlyingModule` is phrased is needed, nor could one be built: `TopCat.Sheaf` is a `nonrec def`
for that category, so the two are the same type, and only *instance* synthesis, which does not
unfold a plain `def`, distinguishes them.

## Main results

* `Stacks.GlueSquishFactor.pushforwardStructureUnitHom` — the unit `𝒪_W ⟶ u_*𝒪_{X''}` of
  `u : X'' ⟶ W` pushed forward along `q : W ⟶ X`, read as a morphism
  `q_*𝒪_W ⟶ (u ≫ q)_*𝒪_{X''}` of `𝒪_X`-modules.
* `Stacks.GlueSquishFactor.structureUnitHom_comp_pushforwardStructureUnitHom` — **the commuting
  square**: `𝒪_X ⟶ q_*𝒪_W ⟶ (u ≫ q)_*𝒪_{X''}` is the unit of `u ≫ q`. It is
  `Stacks.RelativeSpec.AlgebraSheaf.structSection_of_oneSection` — a unital morphism of
  underlying modules respects structure morphisms — at the observation that the pushed-forward
  unit sends `1` to `1`.
* `Stacks.GlueSquishFactor.cokernelPushforwardStructureUnitHomIso` — right exactness of `q_*` on
  quasi-coherent modules identifies `q_*(u_*𝒪_{X''}/𝒪_W)` with `(u ≫ q)_*𝒪_{X''}/q_*𝒪_W`.
* `Stacks.GlueSquishFactor.sumSheafMultiplicity_cokernel_structureUnitHom_lt_of_factorization` —
  **the measure of the upper half drops strictly.** For a factorization `u ≫ q = g` of a morphism
  of `k`-schemes with `q` affine and universally closed, both halves isomorphisms away from a
  finite set and injective on structure sheaves, the total multiplicity of `u_*𝒪_{X''}/𝒪_W` on
  `W` is strictly below that of `g_*𝒪_{X''}/𝒪_X` on `X` as soon as `q_*𝒪_W/𝒪_X` is nonzero at
  one point. This is the clause `μ p < μ g` of `hsplit`.
* `Stacks.GlueSquishFactor.exists_split_isAlmostIso_measureOver_lt` — **the splitting clause of
  `hsplit`, with both measure drops.** A finite quasi-coherent subalgebra of `f_*𝒪_{X'}` which is
  proper at *both* ends splits an almost isomorphism into two almost isomorphisms of strictly
  smaller measure. With
  `Stacks.GlueSquishFactor.exists_isFinite_subalg_mem_supp_cokernel_both_of_ne` supplying such a
  subalgebra, this discharges the splitting branch of `hsplit` whenever the bad set of `f` has
  more than one point.
* `Stacks.GlueSquishFactor.exists_split_isAlmostIso_measureOver_lt_of_ne` — that combination, as
  one statement: **two distinct bad points give a splitting with both measures dropping.**

## What remains for [Stacks, Tag 0C1L]

The hypothesis `hsplit` of `Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso` is a
dichotomy, and this file supplies its splitting branch; the other branch — `f` is already a chain
of elementary modifications — is owed exactly when the bad set of `f` is a single point, and is
supplied in `StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryStepBranch`, which
assembles `hsplit` out of the two. The hypothesis `hiso` of
`Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_forall_isFinite_subalg` — an open whose
complement is exactly that one point — is proved there, from the converse of
`Stacks.GlueSquishFactor.isZero_stalk_cokernel_structureUnitHom`. What is left of the lemma after
that is one statement, `Stacks.GlueSquishFactor.IsSquishingProducer`: the squishing half of the
one-step classification, which would produce `AlgebraicGeometry.IsSquishingTangentVector` from a
fibre isomorphic to `k[ε]`.

## No stacks attribute

**No `@[stacks]` attribute is attached, and none is earned.** These statements are inputs to the
splitting hypothesis `hsplit` of
`Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso`, which is still unproved; on their own
they assert no part of the lemma.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.GlueSquishFactor

/-! ### The direct image of a pushforward algebra -/

/-- **The direct image of the structure sheaf is the module of the pushforward algebra**, on the
nose. Both sides are the restriction of scalars of the unit sheaf of modules over the sheaf of
rings `U ↦ Γ(W, q⁻¹U)` along the same natural transformation `Functor.whiskerRight q.c _`. -/
theorem pushforward_obj_unitModule {W X : Scheme.{u}} (q : W ⟶ X) :
    (Scheme.Modules.pushforward q).obj (unitModule W) =
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra q) : X.Modules) :=
  rfl

/-- **The direct image of a pushforward algebra is the pushforward algebra of the composite**, on
the nose: `q_*(u_*𝒪_{X''}) = (u ≫ q)_*𝒪_{X''}` as `𝒪_X`-modules. -/
theorem pushforward_obj_underlyingModule_pushforwardAlgebra {X'' W X : Scheme.{u}} (u : X'' ⟶ W)
    (q : W ⟶ X) :
    (Scheme.Modules.pushforward q).obj
        (AlgebraSheaf.underlyingModule (pushforwardAlgebra u) : W.Modules) =
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (u ≫ q)) : X.Modules) :=
  rfl

/-- **The unit of `u` pushed forward along `q`**, as a morphism `q_*𝒪_W ⟶ (u ≫ q)_*𝒪_{X''}` of
`𝒪_X`-modules. The ascription is legal because the source and target are the direct images of
`Stacks.GlueSquishFactor.unitModule` and of `u_*𝒪_{X''}` on the nose; see
`Stacks.GlueSquishFactor.pushforward_obj_unitModule` and
`Stacks.GlueSquishFactor.pushforward_obj_underlyingModule_pushforwardAlgebra`. -/
def pushforwardStructureUnitHom {X'' W X : Scheme.{u}} (u : X'' ⟶ W) (q : W ⟶ X) :
    (AlgebraSheaf.underlyingModule (pushforwardAlgebra q) : X.Modules) ⟶
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (u ≫ q)) : X.Modules) :=
  (Scheme.Modules.pushforward q).map (structureUnitHom u)

/-- The pushed-forward unit is unital: over an open `V` of `X` it is the unit map of `u` over
`q⁻¹V`, which carries the section `1` to the section `1`. -/
theorem oneSection_pushforwardStructureUnitHom {X'' W X : Scheme.{u}} (u : X'' ⟶ W) (q : W ⟶ X)
    (V : (X.Opens)ᵒᵖ) :
    ((pushforwardStructureUnitHom u q).val.app V).hom
        (AlgebraSheaf.oneSection (pushforwardAlgebra q) V) =
      AlgebraSheaf.oneSection (pushforwardAlgebra (u ≫ q)) V := by
  have h : ((structureUnitHom u).val.app (op (q ⁻¹ᵁ V.unop))).hom
      (AlgebraSheaf.oneSection (pushforwardAlgebra q) V) =
        AlgebraSheaf.oneSection (pushforwardAlgebra (u ≫ q)) V := by
    rw [structureUnitHom_eq_unitModuleMap]
    exact AlgebraSheaf.structSection_one (pushforwardAlgebra u) (op (q ⁻¹ᵁ V.unop))
  exact h

/-- **The commuting square of a factorization `u ≫ q`**: the unit `𝒪_X ⟶ (u ≫ q)_*𝒪_{X''}`
factors as the unit of `q` followed by the pushed-forward unit of `u`.

This is the hypothesis `hab` of
`Stacks.GlueSquishFactor.sheafMultiplicity_cokernel_structureUnitHom_add`
and of its strict-drop companions for the factorization through `q_*𝒪_W`. Both units are
structure morphisms of algebra sheaves by
`Stacks.GlueSquishFactor.structureUnitHom_eq_unitModuleMap`, so it is enough that the middle map
is unital, which is `Stacks.GlueSquishFactor.oneSection_pushforwardStructureUnitHom`. -/
theorem structureUnitHom_comp_pushforwardStructureUnitHom {X'' W X : Scheme.{u}} (u : X'' ⟶ W)
    (q : W ⟶ X) :
    structureUnitHom q ≫ pushforwardStructureUnitHom u q = structureUnitHom (u ≫ q) := by
  rw [structureUnitHom_eq_unitModuleMap, structureUnitHom_eq_unitModuleMap]
  apply SheafOfModules.hom_ext
  refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
  exact AlgebraSheaf.structSection_of_oneSection (pushforwardStructureUnitHom u q)
    (fun V => oneSection_pushforwardStructureUnitHom u q V) V r

/-- The structure sheaf is quasi-coherent as a module over itself. -/
instance isQuasicoherent_unitModule (W : Scheme.{u}) : (unitModule W).IsQuasicoherent := by
  unfold unitModule
  infer_instance

/-- **The direct image along an affine morphism of the quotient `u_*𝒪_{X''}/𝒪_W` is the quotient
`(u ≫ q)_*𝒪_{X''}/q_*𝒪_W`.** Both the unit module and the module of a pushforward algebra along
an affine morphism are quasi-coherent, so
`Stacks.AlgebraicGeometry.AffineQcohExactness.preservesColimit_parallelPair_zero` applies. -/
def cokernelPushforwardStructureUnitHomIso {X'' W X : Scheme.{u}} (u : X'' ⟶ W) (q : W ⟶ X)
    [IsAffineHom q] [IsAffineHom u] :
    (Scheme.Modules.pushforward q).obj (cokernel (structureUnitHom u)) ≅
      cokernel (pushforwardStructureUnitHom u q) :=
  haveI : (AlgebraSheaf.underlyingModule (pushforwardAlgebra u) : W.Modules).IsQuasicoherent :=
    isQuasicoherent_pushforwardAlgebra u
  haveI := Stacks.AlgebraicGeometry.AffineQcohExactness.preservesColimit_parallelPair_zero q
    (structureUnitHom u)
  PreservesCokernel.iso _ _

/-- Isomorphic modules have the same support: the stalk functor carries the isomorphism to a
linear equivalence of stalks, and nontriviality transports along it. -/
theorem mem_supp_of_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) {x : X}
    (hx : x ∈ SheafOfModules.supp F) : x ∈ SheafOfModules.supp G :=
  (SheafOfModules.mem_supp_iff_nontrivial_stalk G x).mpr
    ((Stacks.SheafOfModules.FlatShortExact.stalkLinearEquivOfIso e x).toEquiv.nontrivial_congr.mp
      ((SheafOfModules.mem_supp_iff_nontrivial_stalk F x).mp hx))

/-! ### The strict drop of the measure of the upper half -/

/-- **The measure of the upper half of a splitting of [Stacks, Tag 0C1L] drops strictly.** Let
`u ≫ q = g` be a factorization of a morphism of `k`-schemes with `q` affine and universally
closed and `u` affine, let `g` be an isomorphism over an open `U` of `X` with finite complement
and `u` an isomorphism over an open `V` of `W` with finite complement, let both units be
monomorphisms of `𝒪`-modules, and suppose the quotient `q_*𝒪_W/𝒪_X` is nonzero at one point.
Then the total multiplicity of `u_*𝒪_{X''}/𝒪_W` on `W` — the measure of the upper half — is
strictly below the measure of `g`.

This is the clause `μ p < μ g` of the splitting hypothesis `hsplit` of
`Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso`. Three steps: the measure of the upper
half is at most the total multiplicity of its direct image
(`Stacks.GlueSquishFactor.sumSheafMultiplicity_le_pushforward`, whose support hypotheses come
from `Stacks.GlueSquishFactor.finite_supp_cokernel_structureUnitHom` and
`Stacks.GlueSquishFactor.isClosed_singleton_of_mem_compl_isoLocus` at `V`); that direct image is
`(u ≫ q)_*𝒪_{X''}/q_*𝒪_W` by
`Stacks.GlueSquishFactor.cokernelPushforwardStructureUnitHomIso`; and the multiplicity of the
latter is below that of `g_*𝒪_{X''}/𝒪_X` by
`Stacks.GlueSquishFactor.sumSheafMultiplicity_cokernel_lt_of_mem_supp_left` at the commuting
square `Stacks.GlueSquishFactor.structureUnitHom_comp_pushforwardStructureUnitHom`. -/
theorem sumSheafMultiplicity_cokernel_structureUnitHom_lt_of_factorization {k : Type u} [Field k]
    {X'' W X : Scheme.{u}} (g : X'' ⟶ X) (u : X'' ⟶ W) (q : W ⟶ X) (hfac : u ≫ q = g)
    [IsAffineHom q] [UniversallyClosed q] [IsAffineHom u]
    (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π]
    (πW : W ⟶ Spec (.of k)) [LocallyOfFiniteType πW]
    (hcoh : (cokernel (structureUnitHom g)).IsCoherent)
    (U : X.Opens) (hUiso : IsIso (g ∣_ U)) (hUfin : Set.Finite ((U : Set X)ᶜ))
    (V : W.Opens) (hViso : IsIso (u ∣_ V)) (hVfin : Set.Finite ((V : Set W)ᶜ))
    (hmq : Mono (structureUnitHom q)) (hmu : Mono (structureUnitHom u))
    {x₀ : X} (ha : x₀ ∈ SheafOfModules.supp (cokernel (structureUnitHom q))) :
    sumSheafMultiplicity (cokernel (structureUnitHom u)) <
      sumSheafMultiplicity (cokernel (structureUnitHom g)) := by
  subst hfac
  have : Mono (pushforwardStructureUnitHom u q) :=
    inferInstanceAs (Mono ((Scheme.Modules.pushforward q).map (structureUnitHom u)))
  have hiso := cokernelPushforwardStructureUnitHomIso u q
  have hlen : ∀ x : X, IsFiniteLength (X.presheaf.stalk x)
      (((Scheme.Modules.pushforward q).obj
        (cokernel (structureUnitHom u))).presheaf.stalk x) := by
    intro x
    let e : ((Scheme.Modules.pushforward q).obj (cokernel (structureUnitHom u))).presheaf.stalk x
        ≃ₗ[X.presheaf.stalk x] (cokernel (pushforwardStructureUnitHom u q)).presheaf.stalk x :=
      Stacks.SheafOfModules.FlatShortExact.stalkLinearEquivOfIso hiso x
    refine e.symm.isFiniteLength ?_
    have hf := isFiniteLength_stalk_cokernel_structureUnitHom (u ≫ q) π hcoh U hUfin x
    rw [← structureUnitHom_comp_pushforwardStructureUnitHom u q] at hf
    exact isFiniteLength_stalk_cokernel_of_comp_right _ _ hf
  calc sumSheafMultiplicity (cokernel (structureUnitHom u))
      ≤ sumSheafMultiplicity
          ((Scheme.Modules.pushforward q).obj (cokernel (structureUnitHom u))) :=
        sumSheafMultiplicity_le_pushforward q _ (finite_supp_cokernel_structureUnitHom u V hVfin)
          (fun z hz => isClosed_singleton_of_mem_compl_isoLocus πW hVfin
            (supp_subset_compl_cokernel_structureUnitHom u V hz)) hlen
    _ = sumSheafMultiplicity (cokernel (pushforwardStructureUnitHom u q)) :=
        sumSheafMultiplicity_eq_of_iso hiso
    _ < sumSheafMultiplicity (cokernel (structureUnitHom (u ≫ q))) :=
        sumSheafMultiplicity_cokernel_lt_of_mem_supp_left (u ≫ q) π hcoh U hUfin
          (structureUnitHom q) (pushforwardStructureUnitHom u q)
          (structureUnitHom_comp_pushforwardStructureUnitHom u q) ha

/-- A quasi-compact locally quasi-finite morphism pulls an open with finite complement back to an
open with finite complement. -/
theorem finite_compl_preimage {Y X : Scheme.{u}} (q : Y ⟶ X) [LocallyQuasiFinite q]
    [QuasiCompact q] {U : X.Opens} (hU : ((U : Set X)ᶜ).Finite) :
    (((q ⁻¹ᵁ U : Y.Opens) : Set Y)ᶜ).Finite := by
  have hpre : ((q ⁻¹ᵁ U : Y.Opens) : Set Y)ᶜ = ⋃ y ∈ (U : Set X)ᶜ, q.base ⁻¹' {y} := by
    ext z
    simp
  rw [hpre]
  exact hU.biUnion fun y _ => q.finite_preimage_singleton y

/-! ### The splitting clause of `hsplit` -/

/-- **A subalgebra proper at both ends splits an almost isomorphism with both measures dropping.**
Let `f : X' ⟶ X` be an almost isomorphism of algebraic `k`-schemes with `f_*𝒪_{X'}/𝒪_X` coherent,
and let `C` be a finite quasi-coherent `𝒪_X`-subalgebra of `f_*𝒪_{X'}` for which *both* quotients
`C/𝒪_X` and `f_*𝒪_{X'}/C` are nonzero somewhere. Then `f` factors over `Spec k` as `p ≫ q` with
`p` and `q` again almost isomorphisms and `measureOver p`, `measureOver q` both strictly below
`measureOver f`.

This is exactly the splitting branch of the hypothesis `hsplit` of
`Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso` at `μ = measureOver`. The splitting is
the one of `Stacks.GlueSquishFactor.exists_split_of_algebraHom` — the relative spectrum of `C`,
with `Stacks.GlueSquishFactor.toIntermediate` above it — reconstructed here rather than obtained
from that theorem's existential, because the two measures are computed from the two halves and an
existential does not name them. The lower drop is
`Stacks.GlueSquishFactor.sumSheafMultiplicity_cokernel_structureUnitHom_relativeSpecToBase_lt`
and the upper one is
`Stacks.GlueSquishFactor.sumSheafMultiplicity_cokernel_structureUnitHom_lt_of_factorization`.

Combined with
`Stacks.GlueSquishFactor.exists_isFinite_subalg_mem_supp_cokernel_both_of_ne`, which produces
such a `C` from two distinct bad points, this discharges `hsplit` whenever the bad set of `f` has
more than one point. -/
theorem exists_split_isAlmostIso_measureOver_lt {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Over (Spec (.of k))} (f : X' ⟶ X) (hf : IsAlmostIso f)
    (hcoh : (cokernel (structureUnitHom f.left)).IsCoherent)
    (C : AlgebraSheaf.Subalg (pushforwardAlgebra f.left))
    [AlgebraSheaf.IsQuasicoherent (AlgebraSheaf.Subalg.toAlgebraSheaf C)]
    (hCfin : AlgebraSheaf.IsFinite (AlgebraSheaf.Subalg.toAlgebraSheaf C))
    (hlow : (SheafOfModules.supp (cokernel (AlgebraSheaf.unitModuleMap
      (AlgebraSheaf.Subalg.toAlgebraSheaf C)))).Nonempty)
    (hup : (SheafOfModules.supp (cokernel (AlgebraSheaf.underlyingModuleMap
      (AlgebraSheaf.Subalg.incl C)))).Nonempty) :
    ∃ (Z : Over (Spec (.of k))) (p : X' ⟶ Z) (q : Z ⟶ X), p ≫ q = f ∧
      IsAlmostIso p ∧ IsAlmostIso q ∧
        measureOver p < measureOver f ∧ measureOver q < measureOver f := by
  obtain ⟨⟨hX'ft, hX'qc, hXft, hXqc, hffin, U, hUfin, hUiso⟩, hmono⟩ := hf
  set A := AlgebraSheaf.Subalg.toAlgebraSheaf C
  set ψ := AlgebraSheaf.Subalg.incl C
  have hψ : ∀ V : X.left.Opens, Function.Injective (ψ.right.hom.app (op V)).hom :=
    fun _ => Subtype.val_injective
  have hfac : toIntermediate f.left A ψ ≫ relativeSpecToBase A = f.left :=
    toIntermediate_comp_relativeSpecToBase f.left A ψ
  have hq : IsFinite (relativeSpecToBase A) :=
    Stacks.AffineAlgebraEquivalence.isFinite_relativeSpecToBase A hCfin
  have hqU : IsIso (relativeSpecToBase A ∣_ U) :=
    isIso_morphismRestrict_relativeSpecToBase f.left A ψ hψ hUiso
  have hp : IsFinite (toIntermediate f.left A ψ) := by
    have : IsFinite (toIntermediate f.left A ψ ≫ relativeSpecToBase A) := by
      rw [hfac]
      infer_instance
    exact IsFinite.of_comp _ (relativeSpecToBase A)
  have hpU : IsIso (toIntermediate f.left A ψ ∣_ (relativeSpecToBase A ⁻¹ᵁ U)) := by
    have hcomp : IsIso ((toIntermediate f.left A ψ ≫ relativeSpecToBase A) ∣_ U) := by
      rwa [hfac]
    rw [morphismRestrict_comp] at hcomp
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance hcomp
  have hqmono : Mono (pushforwardAlgebra (relativeSpecToBase A)).hom :=
    mono_hom_pushforwardAlgebra_of_factorization f.left (toIntermediate f.left A ψ)
      (relativeSpecToBase A) hfac
  have hpmono : Mono (pushforwardAlgebra (toIntermediate f.left A ψ)).hom :=
    mono_hom_pushforwardAlgebra_toIntermediate f.left A ψ hψ
  have hpreUfin := finite_compl_preimage (relativeSpecToBase A) hUfin
  have hZft : LocallyOfFiniteType (relativeSpecToBase A ≫ (X.left ↘ Spec (.of k))) :=
    inferInstance
  have hZqc : QuasiCompact (relativeSpecToBase A ≫ (X.left ↘ Spec (.of k))) :=
    inferInstance
  obtain ⟨x₁, hx₁⟩ := hlow
  obtain ⟨x₂, hx₂⟩ := hup
  refine ⟨Over.mk (relativeSpecToBase A ≫ X.hom),
    Over.homMk (toIntermediate f.left A ψ) ?_, Over.homMk (relativeSpecToBase A) rfl,
    Over.OverMorphism.ext hfac, ⟨⟨hX'ft, hX'qc, hZft, hZqc, hp, relativeSpecToBase A ⁻¹ᵁ U,
      hpreUfin, hpU⟩, hpmono⟩, ⟨⟨hZft, hZqc, hXft, hXqc, hq, U, hUfin, hqU⟩, hqmono⟩, ?_, ?_⟩
  · change toIntermediate f.left A ψ ≫ relativeSpecToBase A ≫ X.hom = X'.hom
    rw [← Category.assoc, hfac, Over.w]
  · exact sumSheafMultiplicity_cokernel_structureUnitHom_lt_of_factorization f.left
      (toIntermediate f.left A ψ) (relativeSpecToBase A) hfac
      (X.left ↘ Spec (.of k)) (relativeSpecToBase A ≫ (X.left ↘ Spec (.of k))) hcoh
      U hUiso hUfin (relativeSpecToBase A ⁻¹ᵁ U) hpU hpreUfin
      (mono_structureUnitHom (relativeSpecToBase A) hqmono)
      (mono_structureUnitHom (toIntermediate f.left A ψ) hpmono)
      (mem_supp_of_iso (cokernelStructureUnitHomRelativeSpecIso A).symm hx₁)
  · exact sumSheafMultiplicity_cokernel_structureUnitHom_relativeSpecToBase_lt f.left
      (X.left ↘ Spec (.of k)) hcoh U hUfin hmono C hx₂

/-- **Two distinct bad points split an almost isomorphism with both measures dropping.** This is
`Stacks.GlueSquishFactor.exists_split_isAlmostIso_measureOver_lt` fed by
`Stacks.GlueSquishFactor.exists_isFinite_subalg_mem_supp_cokernel_both_of_ne`: the subalgebra
`𝒪_X + ℐ_y · f_*𝒪_{X'}` is proper at both ends as soon as the stalk extension is nontrivial at
two distinct points, one of them closed.

So the splitting branch of the hypothesis `hsplit` of
`Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso` holds whenever the bad set of `f` has
more than one point, and the elementary-step branch is owed only when it has exactly one — where
`Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_forall_isFinite_subalg` applies. -/
theorem exists_split_isAlmostIso_measureOver_lt_of_ne {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Over (Spec (.of k))} (f : X' ⟶ X) (hf : IsAlmostIso f)
    (hcoh : (cokernel (structureUnitHom f.left)).IsCoherent) [IsLocallyNoetherian X.left]
    [AlgebraSheaf.IsQuasicoherent (pushforwardAlgebra f.left)]
    [(AlgebraSheaf.underlyingModule (pushforwardAlgebra f.left) : X.left.Modules).IsCoherent]
    {x y : X.left} (hxy : x ≠ y) (hcly : IsClosed ({y} : Set X.left))
    (hbadx : letI : Algebra (X.left.presheaf.stalk x)
                ((f.left.base _* X'.left.presheaf).stalk x) :=
        (stalkPushforwardMap f.left x).hom.toAlgebra
      (⊥ : Subalgebra (X.left.presheaf.stalk x)
        ((f.left.base _* X'.left.presheaf).stalk x)) ≠ ⊤)
    (hbady : letI : Algebra (X.left.presheaf.stalk y)
                ((f.left.base _* X'.left.presheaf).stalk y) :=
        (stalkPushforwardMap f.left y).hom.toAlgebra
      (⊥ : Subalgebra (X.left.presheaf.stalk y)
        ((f.left.base _* X'.left.presheaf).stalk y)) ≠ ⊤) :
    ∃ (Z : Over (Spec (.of k))) (p : X' ⟶ Z) (q : Z ⟶ X), p ≫ q = f ∧
      IsAlmostIso p ∧ IsAlmostIso q ∧
        measureOver p < measureOver f ∧ measureOver q < measureOver f := by
  have : IsFinite f.left := hf.1.2.2.2.2.1
  obtain ⟨C, hCqc, hCfin, hlow, hup⟩ :=
    exists_isFinite_subalg_mem_supp_cokernel_both_of_ne f.left hf.2 hxy hcly hbadx hbady
  exact exists_split_isAlmostIso_measureOver_lt f hf hcoh C hCfin hlow hup

end Stacks.GlueSquishFactor

end
