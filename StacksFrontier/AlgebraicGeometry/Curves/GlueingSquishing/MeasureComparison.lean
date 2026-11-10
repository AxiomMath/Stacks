module

public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.BadPointsSum
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.BadPointsSupport
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.FibreSum
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SplittingStep
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.StalkSubalgebraSpreadOut

/-!
# The measure of the two halves of a splitting of [Stacks, Tag 0C1L]

`Stacks.GlueSquishFactor.exists_split_isAlmostIso_of_algebraHom` factors an almost isomorphism
`f : X' ⟶ X` through a finite quasi-coherent subalgebra `𝒜` of `f_*𝒪_{X'}` as

`X' --p--> Spec_X(𝒜) --q--> X`

with both halves again almost isomorphisms. The induction
`Stacks.GlueSquishFactor.isElementaryChain_of_split` additionally needs the measure
`Stacks.GlueSquishFactor.measureOver` to drop strictly at both halves, and the two strict drops
that are proved — `Stacks.GlueSquishFactor.sumSheafMultiplicity_cokernel_lt_of_mem_supp_right`
and `...._left` — are stated about the two quotients `𝒜/𝒪_X` and `f_*𝒪_{X'}/𝒜` **on `X`**,
whereas the measures of `q` and `p` are the total multiplicities of `q_*𝒪/𝒪_X` on `X` and of
`p_*𝒪_{X'}/𝒪_{Spec_X(𝒜)}` on `Spec_X(𝒜)`. This file identifies the first of the two with its
drop, and supplies the summation step the second one needs.

## Main results

* `Stacks.GlueSquishFactor.cokernelStructureUnitHomRelativeSpecIso` — the identification
  `coker(𝒪_X ⟶ q_*𝒪_{Spec_X(𝒜)}) ≅ coker(𝒪_X ⟶ 𝒜)`, which is
  `Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso` of [Stacks, Tag 01SA] read on
  underlying modules. The square commutes by functoriality of the structure morphism of an
  algebra sheaf, `Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap_comp`, once
  `Stacks.GlueSquishFactor.structureUnitHom` is recognised as that structure morphism by
  `Stacks.GlueSquishFactor.structureUnitHom_eq_unitModuleMap`.
* `Stacks.GlueSquishFactor.measureOver_relativeSpecToBase_eq` — hence the two have the same
  total multiplicity.
* `Stacks.GlueSquishFactor.sumSheafMultiplicity_cokernel_structureUnitHom_relativeSpecToBase_lt`
  — **the measure of the lower half of a splitting drops strictly**, as soon as `f_*𝒪_{X'}/𝒜`
  is nonzero at one point. With
  `Stacks.GlueSquishFactor.exists_isFinite_subalg_mem_supp_cokernel_both` supplying that point,
  this is the clause `μ q < μ f` of the splitting hypothesis `hsplit` of
  `Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso`.
* `Stacks.GlueSquishFactor.measureOver_homMk_relativeSpecToBase` — the same statement about the
  morphism `Stacks.GlueSquishFactor.exists_split_of_algebraHom` actually produces.
* `Stacks.GlueSquishFactor.sumSheafMultiplicity_le_pushforward` — **the summation step for the
  upper half**: for a universally closed `g : W ⟶ X` and an `𝒪_W`-module `N` whose support is a
  finite set of closed points with finite stalk lengths along `g`, the total multiplicity of `N`
  on `W` is at most the total multiplicity of `g_*N` on `X`. This is the fibrewise inequality
  `Stacks.GlueSquishFactor.sum_sheafMultiplicity_le_sheafMultiplicity_pushforward` summed over
  the base, the sum over `W` being regrouped along the fibres of `g` by
  `Finset.sum_fiberwise_of_maps_to`.
* `Stacks.GlueSquishFactor.ideal_closedIdeal_eq_top` — the ideal sheaf of a closed set is the
  unit ideal on an affine open which misses it.
* `Stacks.GlueSquishFactor.exists_isFinite_subalg_mem_supp_cokernel_both_of_ne` — **two distinct
  bad points give a subalgebra proper at both ends**, with no hypothesis on either stalk beyond
  non-triviality. This is the reduction recorded in the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.StalkSubalgebraSpreadOut`: a splitting
  of [Stacks, Tag 0C1L] exists whenever the bad set has more than one point, so the
  elementary-step branch of the dichotomy — and with it the hypothesis `hiso` of
  `Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_forall_isFinite_subalg`, an isomorphism
  off a *single* point — is needed only when the bad set has exactly one point.

## Implementation notes

**Why the lower half is an equality and the upper half only an inequality.** The lower half is a
sum over the points of `X` on both sides, so the identification of [Stacks, Tag 01SA] transports
it verbatim. The upper half is a sum over the points of `Spec_X(𝒜)`, and the fibre of `q` over a
bad point of `X` may have several points; the lengths there add up to at most the length of the
stalk of `q_*` of the quotient, by
`Stacks.GlueSquishFactor.sum_length_stalk_le_length_stalk_pushforward`, the defect being the
residue degrees, which are discarded. An inequality is all the induction needs.

**What the upper half still owes, and it is the only thing [Stacks, Tag 0C1L] is now waiting
on.** `Stacks.GlueSquishFactor.sumSheafMultiplicity_le_pushforward` compares the measure of `p`
with the total multiplicity of `q_*coker(𝒪_{Spec_X(𝒜)} ⟶ p_*𝒪_{X'})` on `X`. Identifying *that*
with the total multiplicity of `f_*𝒪_{X'}/𝒜`, which is what
`Stacks.GlueSquishFactor.sumSheafMultiplicity_cokernel_lt_of_mem_supp_left` drops, needs right
exactness of `q_*` on quasi-coherent modules
(`Stacks.AlgebraicGeometry.AffineQcohExactness.preservesColimit_parallelPair_zero`, which *is*
available) applied to a square built from two identifications of *underlying modules*:

* `(Scheme.Modules.pushforward q).obj (unitModule (relativeSpec 𝒜)) ≅`
  `AlgebraSheaf.underlyingModule (pushforwardAlgebra q)`, i.e. `q_*𝒪_{Spec_X(𝒜)}` formed as a
  direct image of modules agrees with the underlying module of the pushforward *algebra*; and
* `(Scheme.Modules.pushforward q).obj (AlgebraSheaf.underlyingModule (pushforwardAlgebra p)) ≅`
  `AlgebraSheaf.underlyingModule (pushforwardAlgebra f)` for `p ≫ q = f`.

Both hold on sections, `Γ((pushforward q).obj M, V) = Γ(M, q ⁻¹ᵁ V)` being definitional and
`f ⁻¹ᵁ V = p ⁻¹ᵁ (q ⁻¹ᵁ V)` following from `p ≫ q = f`; neither is in the tree in module form,
and the obstruction to writing them down is the coercion between
`AlgebraicGeometry.Scheme.ringCatSheaf`, a `TopCat.Sheaf`, and the
`CategoryTheory.Sheaf (Opens.grothendieckTopology _)` in which
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModule` is phrased — the same mismatch that makes
`Mono` instances for `Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap` have to be passed
positionally below. With that square, the upper drop and hence the splitting hypothesis
`hsplit` close.

## No stacks attribute

**No `@[stacks]` attribute is attached, and none is earned.** These are inputs to the splitting
hypothesis `hsplit` of `Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso`, which is
still unproved; on their own they assert no part of the lemma.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.SubalgebraGeneratedByModule
open Stacks.AlgebraicGeometry.IdealPowerSmul

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.GlueSquishFactor

/-! ### The lower half: the measure of `Spec_X(𝒜) ⟶ X` -/

/-- **The quotient of the unit by the lower half of a splitting is the quotient by the
subalgebra.** For a quasi-coherent sheaf of `𝒪_X`-algebras `A`, the identification
`q_*𝒪_{Spec_X(A)} ≅ A` of [Stacks, Tag 01SA] carries the unit `𝒪_X ⟶ q_*𝒪_{Spec_X(A)}` to the
structure morphism `𝒪_X ⟶ A`, hence identifies their cokernels as `𝒪_X`-modules.

The commuting square is `Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap_comp` applied to the
isomorphism, once `Stacks.GlueSquishFactor.structureUnitHom` of the structure morphism of the
relative spectrum is recognised as the structure morphism of its pushforward algebra. -/
def cokernelStructureUnitHomRelativeSpecIso {X : Scheme.{u}} (A : AlgebraSheaf X)
    [AlgebraSheaf.IsQuasicoherent A] :
    cokernel (structureUnitHom (relativeSpecToBase A)) ≅
      cokernel (AlgebraSheaf.unitModuleMap A) :=
  haveI : IsIso (AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraIso A).hom) :=
    inferInstanceAs (IsIso ((AlgebraSheaf.underlyingModuleFunctor X).map
      (pushforwardAlgebraIso A).hom))
  cokernel.mapIso (f := structureUnitHom (relativeSpecToBase A)) (AlgebraSheaf.unitModuleMap A)
    (Iso.refl _) (asIso (AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraIso A).hom))
    (by
      rw [asIso_hom, structureUnitHom_eq_unitModuleMap]
      exact (AlgebraSheaf.unitModuleMap_comp (pushforwardAlgebraIso A).hom).trans
        (Category.id_comp _).symm)

/-- **The measure of the lower half of a splitting is the total multiplicity of `A/𝒪_X`.** The
total multiplicity is an isomorphism invariant
(`Stacks.GlueSquishFactor.sumSheafMultiplicity_eq_of_iso`), so the identification of
[Stacks, Tag 01SA] carries it across. -/
theorem measureOver_relativeSpecToBase_eq {X : Scheme.{u}} (A : AlgebraSheaf X)
    [AlgebraSheaf.IsQuasicoherent A] :
    sumSheafMultiplicity (cokernel (structureUnitHom (relativeSpecToBase A))) =
      sumSheafMultiplicity (cokernel (AlgebraSheaf.unitModuleMap A)) :=
  sumSheafMultiplicity_eq_of_iso (cokernelStructureUnitHomRelativeSpecIso A)

/-- **The measure of the lower half of a splitting of [Stacks, Tag 0C1L] drops strictly.** Let
`f : X' ⟶ X` be a morphism of schemes of finite type over a field with `𝒪_X ⊂ f_*𝒪_{X'}` which
is an isomorphism away from a finite set, let `C` be a quasi-coherent subalgebra of `f_*𝒪_{X'}`,
and suppose the quotient `f_*𝒪_{X'}/C` is nonzero at one point. Then the total multiplicity of
`q_*𝒪_{Spec_X(C)}/𝒪_X` — the measure of the lower half `q : Spec_X(C) ⟶ X` of the splitting of
`Stacks.GlueSquishFactor.exists_split_isAlmostIso_of_algebraHom` — is strictly below the measure
of `f`.

This is the clause `μ q < μ f` of the splitting hypothesis `hsplit` of
`Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso`. The point of the support is supplied
by `Stacks.GlueSquishFactor.exists_isFinite_subalg_mem_supp_cokernel_both`. -/
theorem sumSheafMultiplicity_cokernel_structureUnitHom_relativeSpecToBase_lt {k : Type u}
    [Field k] {X' X : Scheme.{u}} (f : X' ⟶ X) (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π]
    (hcoh : (cokernel (structureUnitHom f)).IsCoherent) (U : X.Opens) [IsIso (f ∣_ U)]
    (hUfin : Set.Finite ((U : Set X)ᶜ)) (hmono : Mono (pushforwardAlgebra f).hom)
    (C : AlgebraSheaf.Subalg (pushforwardAlgebra f))
    [AlgebraSheaf.IsQuasicoherent (AlgebraSheaf.Subalg.toAlgebraSheaf C)] {x₀ : X}
    (hb : x₀ ∈ SheafOfModules.supp
      (cokernel (AlgebraSheaf.underlyingModuleMap (AlgebraSheaf.Subalg.incl C)))) :
    sumSheafMultiplicity (cokernel (structureUnitHom
        (relativeSpecToBase (AlgebraSheaf.Subalg.toAlgebraSheaf C)))) <
      sumSheafMultiplicity (cokernel (structureUnitHom f)) := by
  rw [measureOver_relativeSpecToBase_eq]
  have hmonoa : Mono (AlgebraSheaf.unitModuleMap (AlgebraSheaf.Subalg.toAlgebraSheaf C)) :=
    mono_unitModuleMap_subalg f hmono C
  have hmonob : Mono (AlgebraSheaf.underlyingModuleMap (AlgebraSheaf.Subalg.incl C)) :=
    Stacks.AlgebraImageSurjective.mono_underlyingModuleMap_of_mono
      (AlgebraSheaf.Subalg.incl C) inferInstance
  exact @sumSheafMultiplicity_cokernel_lt_of_mem_supp_right k _ X' X f π _ hcoh U _ hUfin
    _ _ _ hmonoa hmonob (unitModuleMap_comp_underlyingModuleMap_incl f C) x₀ hb

/-- **The measure of the lower half of the splitting of
`Stacks.GlueSquishFactor.exists_split_of_algebraHom`, on the nose.** That splitting's second
half is `Over.homMk (relativeSpecToBase A) rfl`, whose measure is therefore the total
multiplicity of `A/𝒪_X`. This is the machine check that
`Stacks.GlueSquishFactor.measureOver_relativeSpecToBase_eq` is about the morphism the splitting
actually produces, rather than about an isomorphic one. -/
theorem measureOver_homMk_relativeSpecToBase {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (A : AlgebraSheaf X.left) [AlgebraSheaf.IsQuasicoherent A] :
    measureOver (Over.homMk (relativeSpecToBase A) rfl :
        Over.mk (relativeSpecToBase A ≫ X.hom) ⟶ X) =
      sumSheafMultiplicity (cokernel (AlgebraSheaf.unitModuleMap A)) :=
  measureOver_relativeSpecToBase_eq A

/-! ### The upper half: summing the fibrewise inequality over the base -/

/-- **The total multiplicity of a module is at most that of its direct image.** Let `g : W ⟶ X`
be universally closed — in particular finite — and let `N` be an `𝒪_W`-module whose support is
a finite set of closed points and whose direct image has finite stalk lengths. Then the total
multiplicity of `N` on `W` is at most the total multiplicity of `g_*N` on `X`.

This is the summation step the measure of the *upper* half of a splitting of
[Stacks, Tag 0C1L] needs: that measure is a sum over the points of `Spec_X(𝒜)`, and the drop
`Stacks.GlueSquishFactor.sumSheafMultiplicity_cokernel_lt_of_mem_supp_left` is a sum over the
points of `X`. The fibrewise inequality is
`Stacks.GlueSquishFactor.sum_sheafMultiplicity_le_sheafMultiplicity_pushforward`, and the sum
over `W` is regrouped along the fibres of `g` by `Finset.sum_fiberwise_of_maps_to`; the points of
`X` outside the image of the support contribute nothing because there the fibre of the support is
empty, so `Stacks.GlueSquishFactor.length_stalk_pushforward_eq_sum` is an empty sum. -/
theorem sumSheafMultiplicity_le_pushforward {W X : Scheme.{u}} (g : W ⟶ X)
    [UniversallyClosed g] (N : W.Modules)
    (hfin : (SheafOfModules.supp N : Set W).Finite)
    (hcl : ∀ z ∈ SheafOfModules.supp N, IsClosed ({z} : Set W))
    (hlen : ∀ x : X, IsFiniteLength (X.presheaf.stalk x)
      (((Scheme.Modules.pushforward g).obj N).presheaf.stalk x)) :
    sumSheafMultiplicity N ≤
      sumSheafMultiplicity ((Scheme.Modules.pushforward g).obj N) := by
  classical
  let : ∀ x : X, Fintype ↥{z : W | g.base z = x ∧ z ∈ SheafOfModules.supp N} := fun _ =>
    (hfin.subset fun _ hz => hz.2).fintype
  have hmemN : ∀ z : W, (Stacks.Chow.sheafMultiplicity N z).toNat ≠ 0 →
      z ∈ hfin.toFinset := fun z hz =>
    hfin.mem_toFinset.mpr (mem_supp_of_toNat_sheafMultiplicity_ne_zero N hz)
  have hmemP : ∀ x : X,
      (Stacks.Chow.sheafMultiplicity ((Scheme.Modules.pushforward g).obj N) x).toNat ≠ 0 →
        x ∈ hfin.toFinset.image g.base := by
    intro x hx
    by_contra hcon
    let : ∀ z : ↥{z : W | g.base z = x ∧ z ∈ SheafOfModules.supp N},
        Module (X.presheaf.stalk x) (N.presheaf.stalk z.1) :=
      Stacks.Chow.supportFibreStalkModule g N x
    have : IsEmpty ↥{z : W | g.base z = x ∧ z ∈ SheafOfModules.supp N} :=
      ⟨fun z => hcon (z.2.1 ▸ Finset.mem_image_of_mem g.base
        (hfin.mem_toFinset.mpr z.2.2))⟩
    have h0 : Module.length (X.presheaf.stalk x)
        (((Scheme.Modules.pushforward g).obj N).presheaf.stalk x) = 0 := by
      rw [length_stalk_pushforward_eq_sum g N hfin hcl x]
      simp
    refine hx ?_
    rw [Stacks.Chow.sheafMultiplicity, h0]
    simp
  have hfib := Finset.sum_fiberwise_of_maps_to
    (fun z (hz : z ∈ hfin.toFinset) => Finset.mem_image_of_mem g.base hz)
    (fun z => (Stacks.Chow.sheafMultiplicity N z).toNat)
  rw [sumSheafMultiplicity_eq_finset_sum N hfin.toFinset hmemN,
    sumSheafMultiplicity_eq_finset_sum ((Scheme.Modules.pushforward g).obj N)
      (hfin.toFinset.image g.base) hmemP, ← hfib]
  refine Finset.sum_le_sum fun x _ => ?_
  have hle := sum_sheafMultiplicity_le_sheafMultiplicity_pushforward g N hfin hcl x (hlen x)
  have hconv : ∑ z ∈ hfin.toFinset.filter (fun z => g.base z = x),
      Stacks.Chow.sheafMultiplicity N z =
      ∑ z : ↥{z : W | g.base z = x ∧ z ∈ SheafOfModules.supp N},
        Stacks.Chow.sheafMultiplicity N z.1 :=
    Finset.sum_subtype _ (fun z => by
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      tauto) _
  have hcast : ((∑ z ∈ hfin.toFinset.filter (fun z => g.base z = x),
        (Stacks.Chow.sheafMultiplicity N z).toNat : ℕ) : ℤ) ≤
      Stacks.Chow.sheafMultiplicity ((Scheme.Modules.pushforward g).obj N) x := by
    rw [Nat.cast_sum]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun z _ => ?_)) (hconv ▸ hle)
    exact Int.toNat_of_nonneg (sheafMultiplicity_nonneg N z)
  omega

/-! ### Two bad points: a splitting with no hypothesis on the stalk -/

/-- **The ideal sheaf of a closed set is the unit ideal on an affine open which misses it.**
Were it proper it would lie in a maximal ideal, and every prime of the ring of functions on an
affine open is the prime of a point of that open
(`Stacks.AlgebraicGeometry.IdealPowerSmul.primeIdealOf_fromSpec`), which would then lie in the
closed set by
`Stacks.AlgebraicGeometry.IdealPowerSmul.mem_closed_iff_vanishingIdeal_le`. -/
theorem ideal_closedIdeal_eq_top {X : Scheme.{u}} (Z : Closeds X) (W : X.affineOpens)
    (hW : ∀ z ∈ (W.1 : Set X), z ∉ (Z : Set X)) : (closedIdeal Z).ideal W = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem := fromSpec_mem W (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(X, W.1))
  refine hW _ hmem ((mem_closed_iff_vanishingIdeal_le Z W _ hmem).mpr ?_)
  rw [primeIdealOf_fromSpec]
  exact hle

/-- **Two bad points give a subalgebra proper at both ends, with no hypothesis on either
stalk beyond non-triviality.** Let `f : X' ⟶ X` be finite with `𝒪_X ⊂ f_*𝒪_{X'}`, and suppose
`f` fails to be an isomorphism at two *distinct* points `x ≠ y`, in the form
`𝒪_{X,x} ≠ (f_*𝒪_{X'})_x` and `𝒪_{X,y} ≠ (f_*𝒪_{X'})_y`, with `{y}` closed. Then there is a
finite quasi-coherent `𝒪_X`-subalgebra `𝒜` of `f_*𝒪_{X'}` for which **both** quotients
`𝒜/𝒪_X` and `f_*𝒪_{X'}/𝒜` have a point in their support.

The subalgebra is `𝒪_X + ℐ_y · f_*𝒪_{X'}` of
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SpreadOutSubalgebra`. At `y` it is proper
at the upper end by `Stacks.GlueSquishFactor.ne_top_obj_idealSmulSubalg`; on an affine open
around `x` *missing* `y` the ideal `ℐ_y` is the unit ideal, so by
`Stacks.GlueSquishFactor.obj_idealSmulSubalg_eq_top` the subalgebra is all of `f_*𝒪_{X'}` there,
and a section which is not a section of `𝒪_X` — which exists because the stalk extension at `x`
is nontrivial, by `Stacks.GlueSquishFactor.exists_mem_obj_germPreimage_notMem_range` at `E = ⊤`
— makes it proper at the lower end.

This is what the one-point case is *not*: compared with
`Stacks.GlueSquishFactor.exists_isFinite_subalg_mem_supp_cokernel_both`, whose hypothesis `hb`
is the branch `m_x·(f_*𝒪_{X'})_x ⊄ 𝒪_{X,x}` of
`Stacks.GlueSquishFactor.forall_exists_algebraMap_eq_or_exists_subalgebra`, here no such branch
is needed: the second bad point does the work the branch did. So a splitting of
[Stacks, Tag 0C1L] exists whenever the bad set has more than one point, and the elementary-step
branch of the dichotomy is needed only when it has exactly one. -/
theorem exists_isFinite_subalg_mem_supp_cokernel_both_of_ne {X' X : Scheme.{u}} (f : X' ⟶ X)
    [IsFinite f] [IsLocallyNoetherian X] [AlgebraSheaf.IsQuasicoherent (pushforwardAlgebra f)]
    [(AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).IsCoherent]
    (hmono : Mono (pushforwardAlgebra f).hom) {x y : X} (hxy : x ≠ y)
    (hcly : IsClosed ({y} : Set X))
    (hbadx : letI : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
        (stalkPushforwardMap f x).hom.toAlgebra
      (⊥ : Subalgebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x)) ≠ ⊤)
    (hbady : letI : Algebra (X.presheaf.stalk y) ((f.base _* X'.presheaf).stalk y) :=
        (stalkPushforwardMap f y).hom.toAlgebra
      (⊥ : Subalgebra (X.presheaf.stalk y) ((f.base _* X'.presheaf).stalk y)) ≠ ⊤) :
    ∃ C : AlgebraSheaf.Subalg (pushforwardAlgebra f),
      (AlgebraSheaf.Subalg.toAlgebraSheaf C).IsQuasicoherent ∧
        (AlgebraSheaf.Subalg.toAlgebraSheaf C).IsFinite ∧
          (SheafOfModules.supp (cokernel (AlgebraSheaf.unitModuleMap
            (AlgebraSheaf.Subalg.toAlgebraSheaf C)))).Nonempty ∧
          (SheafOfModules.supp (cokernel (AlgebraSheaf.underlyingModuleMap
            (AlgebraSheaf.Subalg.incl C)))).Nonempty := by
  classical
  let : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
    (stalkPushforwardMap f x).hom.toAlgebra
  let Z : Closeds X := ⟨{y}, hcly⟩
  obtain ⟨Uy, hUy, hyUy, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show y ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨Ux, hUx, hxUx, hUxy⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ (⟨{y}ᶜ, hcly.isOpen_compl⟩ : X.Opens) from hxy)
  have htop : (idealSmulSubalg (pushforwardAlgebra f)
      (closedIdeal Z)).obj Ux = ⊤ := by
    refine obj_idealSmulSubalg_eq_top (pushforwardAlgebra f) _ fun W hWU => ?_
    exact ideal_closedIdeal_eq_top _ W fun z hz hzZ => hUxy (hWU hz) hzZ
  refine ⟨idealSmulSubalg (pushforwardAlgebra f) (closedIdeal Z),
    isQuasicoherent_idealSmulSubalg _ _,
    isFinite_idealSmulSubalg _ _ (AlgebraicGeometry.isFinite_pushforwardAlgebra f).isIntegral,
    ?_, ?_⟩
  · obtain ⟨s, -, hsnot⟩ :=
      exists_mem_obj_germPreimage_notMem_range f hUx hxUx ⊤ (Ne.symm hbadx)
    exact nonempty_supp_cokernel_unitModuleMap_of_notMem_range f hmono _
      (htop ▸ Subring.mem_top s) hsnot
  · exact nonempty_supp_cokernel_underlyingModuleMap_incl _
      (ne_top_obj_idealSmulSubalg f _ hUy hyUy
        ((mem_closed_iff_vanishingIdeal_le Z ⟨Uy, hUy⟩ y hyUy).mp rfl) hbady)

end Stacks.GlueSquishFactor

end
