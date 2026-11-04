module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowRank0BFG
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.SectionRatioNoAmple.Pullback
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.PicardUFD.Affine
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackInvertible
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowPullback
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.HProjective.AmpleBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveOverAmpleBase
public import StacksFrontier.AlgebraicGeometry.TensorPowerProduct.Basic
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.AmplePositivePower.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.Variety.MiracleFlatEtale
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.StalkDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenaryExamples
public import StacksFrontier.Topology.Dimension.NowhereDense
public import StacksFrontier.Topology.Dimension.OpenGeneralizingMap
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ConstantRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IrreducibleCriterion
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Positivity
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Multiplication by an integer on an abelian variety is finite locally free

Let `A` be an abelian variety over a field `k` and `d` a nonzero integer.
[Stacks, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG) says that multiplication by `d`,
`[d] : A ⟶ A`, is finite locally free of degree `d^{2 dim A}`. This file proves it for `d ≠ 0`,
following the source from [Stacks, Tag 0BFF] on, granted the theorem of the cube for `A × A × A`,
`Stacks.Groupoids.HasTheoremOfTheCube A`, from which [Stacks, Tag 0BFF] follows.

## Main results

* `AlgebraicGeometry.isFinite_of_isProper_of_isAmple_modulePullback`: a proper morphism along
  which some invertible module pulls back to an ample one is finite.
* `Module.Flat.of_isMaximalCohenMacaulay_of_quasiFinite` and
  `AlgebraicGeometry.flat_stalkMap_of_quasiFiniteAt`: miracle flatness ([Stacks, Tag 00R4]) for a
  quasi-finite local homomorphism, whose fibre ring has dimension zero.
* `AlgebraicGeometry.surjective_of_isFinite_of_topologicalKrullDim_le`: a finite morphism into a
  Noetherian irreducible scheme of finite dimension, from a scheme of at least that dimension, is
  surjective.
* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_degreeOver`: the rank of a finite locally free
  morphism of integral schemes is the degree of the extension of function fields.
* `AlgebraicGeometry.selfIntersectionNumber_eq_of_iso` and
  `AlgebraicGeometry.selfIntersectionNumber_tensorPower`: `(𝓛^d · Z)` depends only on the
  isomorphism class of `𝓛`, and `((𝓛^{⊗ n})^d · Z) = n^d (𝓛^d · Z)`.
* `Stacks.Groupoids.exists_isAmple_symmetric`: an abelian variety carries an ample invertible
  module `N` with `[-1]^* N ≅ N`.
* `Stacks.Groupoids.nonempty_zpowId_pullback_iso_of_symmetric`: `[d]^* N ≅ N^{⊗ d²}` for such `N`.
* `Stacks.Groupoids.isFinite_zpow_id_left`, `Stacks.Groupoids.flat_zpow_id_left`,
  `Stacks.Groupoids.degreeOver_zpow_id_left` and
  `Stacks.Groupoids.isFiniteLocallyFreeOfRank_zpow_id_left_of_hasTheoremOfTheCube`: the statement
  of [Stacks, Tag 0BFG] for `d ≠ 0`, granted `HasTheoremOfTheCube A`.

## The proof

The source's argument, with one change in the finiteness step.

* *Finiteness.* For `N` ample and symmetric, `[d]^* N ≅ N^{⊗ d²}` is ample. The source shows that
  no fibre of `[d]` contains a proper curve, by the degree of an ample module on a curve. Here the
  fibre `A_y` is handled directly: it maps to `A` by an affine morphism, so `([d]^* N)|_{A_y}` is
  ample, and it is pulled back from `Spec κ(y)`, so it is trivial. A scheme whose structure sheaf
  is ample is quasi-affine, and a quasi-affine scheme proper over a field is finite over it. So
  every fibre is finite, and `[d]`, being proper, is finite.
* *Flatness* is the source's: `A` is smooth, so its local rings are regular, hence
  Cohen–Macaulay; `[d]` is finite and, comparing dimensions, surjective, so it preserves the
  dimension of every local ring; miracle flatness applies.
* *The degree* is the source's: by [Stacks, Tag 0BEX] and `[d]^* N ≅ N^{⊗ d²}`,
  `deg([d]) (N^g · A) = d^{2g} (N^g · A)`, and `(N^g · A) > 0` by [Stacks, Tag 0BEV].

## The case `d = 0`

The source states Tag 0BFG with no restriction on `d`, and for `d = 0` and `dim A ≥ 1` it is
false: `[0]` factors through the unit point `Spec k ⟶ A`, so its fibre over the unit is all of
`A`, which is not finite over `k`; hence `[0]` is not finite, let alone finite locally free of
degree `0^{2 dim A} = 0`. Every result here assumes `d ≠ 0`.

## References

* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
* [Stacks Project, Tag 0BFF](https://stacks.math.columbia.edu/tag/0BFF)
* [Stacks Project, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4)
* [Stacks Project, Tag 0BEX](https://stacks.math.columbia.edu/tag/0BEX)
* [Stacks Project, Tag 0BEV](https://stacks.math.columbia.edu/tag/0BEV)
* [Stacks Project, Tag 00R4](https://stacks.math.columbia.edu/tag/00R4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- **A quasi-affine scheme proper over an affine scheme is affine.** Its canonical morphism to the
spectrum of its global sections is an open immersion, and it is proper because the composite with
the separated morphism to the spectrum of the base ring is; so it is a closed immersion into an
affine scheme. -/
theorem isAffine_of_isQuasiAffine_of_isProper {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [IsProper f] [X.IsQuasiAffine] : IsAffine X := by
  have h : X.toSpecΓ ≫ Spec.map f.appTop = f ≫ (Spec R).toSpecΓ :=
    (Scheme.toSpecΓ_naturality f).symm
  have : IsProper (X.toSpecΓ ≫ Spec.map f.appTop) := by rw [h]; infer_instance
  have : IsProper X.toSpecΓ := IsProper.of_comp _ (Spec.map f.appTop)
  have : IsClosedImmersion X.toSpecΓ :=
    .of_isPreimmersion _ X.toSpecΓ.isClosedMap.isClosed_range
  exact isAffine_of_isAffineHom X.toSpecΓ

/-- **A quasi-affine scheme proper over an affine scheme is finite over it.** It is affine, so its
structure morphism is affine and proper, which is finiteness. -/
theorem isFinite_of_isQuasiAffine_of_isProper {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [IsProper f] [X.IsQuasiAffine] : IsFinite f := by
  have := isAffine_of_isQuasiAffine_of_isProper f
  rw [IsFinite.iff_isProper_and_isAffineHom]
  exact ⟨inferInstance, inferInstance⟩

/-- **A pullback of an invertible module along a morphism into the spectrum of a field is
trivial.** An invertible module on the spectrum of a field is trivial, the Picard group of a local
ring being trivial, and pulling back carries the structure sheaf to the structure sheaf. -/
@[ega "I 2.4.8" "special case"]
noncomputable def modulePullbackIsoUnitOfSpecField {K : Type u} [Field K]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ Y) (N : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N] :
    (modulePullback (p ≫ s).toLRSHom.toShHom).obj N ≅ SheafOfModules.unit X.ringCatSheaf :=
  have : Stacks.SheafOfModules.IsInvertible (Spec (.of K)).presheaf
      (structureSheafRing (Spec (.of K)).toRingedSpace).property
      ((modulePullback s.toLRSHom.toShHom).obj N) :=
    modulePullback_isInvertible_scheme s N
  (modulePullbackComp p.toLRSHom.toShHom s.toLRSHom.toShHom).app N ≪≫
    (modulePullback p.toLRSHom.toShHom).mapIso
      (Stacks.PicardUFD.isTrivial_of_isInvertible_spec K _).some ≪≫
    modulePullbackObjUnitIso p.toLRSHom.toShHom

/-- **A proper morphism along which the pullback of an invertible module is ample is finite.**
Let `f : X ⟶ Y` be proper, with `Y` such that the inclusion of each point is affine (for
instance `Y` separated), and let `N` be an invertible `𝒪_Y`-module whose pullback to `X` is
ample. Then `f` is finite.

The fibre `X_y` maps to `X` by an affine morphism, so the pullback of `f^* N` to it is ample; it is
also the pullback of `N` to `Spec κ(y)` pulled back once more, hence trivial. So the structure
sheaf of `X_y` is ample, `X_y` is quasi-affine, and being proper over `κ(y)` it is finite over
it. Every fibre being finite, `f` is locally quasi-finite, and a proper locally quasi-finite
morphism is finite. -/
theorem isFinite_of_isProper_of_isAmple_modulePullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (hY : ∀ y : Y, IsAffineHom (Y.fromSpecResidueField y)) (N : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 N]
    (hN : Stacks.Ample.IsAmple X ((modulePullback f.toLRSHom.toShHom).obj N)) :
    IsFinite f := by
  have hfib : ∀ y : Y, LocallyQuasiFinite (f.fiberToSpecResidueField y) := by
    intro y
    have := hY y
    have : IsAffineHom (f.fiberι y) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)).flip (hY y)
    have : IsProper (f.fiberToSpecResidueField y) :=
      IsProper.isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) ‹IsProper f›
    have : Stacks.Ample.IsInvertibleModule (f.fiber y)
        ((modulePullback (f.fiberι y).toLRSHom.toShHom).obj
          ((modulePullback f.toLRSHom.toShHom).obj N)) :=
      have : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
          ((modulePullback f.toLRSHom.toShHom).obj N) := modulePullback_isInvertible_scheme f N
      modulePullback_isInvertible_scheme (f.fiberι y) _
    have : IsQuasiAffineHom (f.fiberι y) := isQuasiAffineHom_of_isAffineHom _
    have hM := Stacks.SectionRatioNoAmple.isAmple_modulePullback_of_isQuasiAffineHom
      (f.fiberι y) ((modulePullback f.toLRSHom.toShHom).obj N) hN
    let e : (modulePullback (f.fiberι y).toLRSHom.toShHom).obj
        ((modulePullback f.toLRSHom.toShHom).obj N) ≅ Stacks.Ample.unitModule (f.fiber y) :=
      ((modulePullbackComp (f.fiberι y).toLRSHom.toShHom f.toLRSHom.toShHom).app N).symm ≪≫
        eqToIso (congrArg (fun φ => (modulePullback φ).obj N)
          (congrArg (fun m : f.fiber y ⟶ Y => m.toLRSHom.toShHom) (Scheme.Hom.fiber_fac f y))) ≪≫
        modulePullbackIsoUnitOfSpecField (K := Y.residueField y) (f.fiberToSpecResidueField y)
          (Y.fromSpecResidueField y) N
    have : (f.fiber y).IsQuasiAffine :=
      (Stacks.RelativeAmple.isQuasiAffine_iff_isAmple_of_iso_unitModule _ _ e).mpr hM
    have : IsFinite (f.fiberToSpecResidueField y) :=
      isFinite_of_isQuasiAffine_of_isProper _
    infer_instance
  have := LocallyQuasiFinite.of_fiberToSpecResidueField f hfib
  exact (IsFinite.iff_isProper_and_locallyQuasiFinite f).mpr ⟨inferInstance, inferInstance⟩

/-! ### Miracle flatness for a quasi-finite local homomorphism -/

/-- **The fibre ring of a quasi-finite local homomorphism of local rings has dimension zero.**
Every prime of `S` containing `𝔪_R S` lies over `𝔪_R`, as does `𝔪_S`; quasi-finiteness makes
primes over one prime incomparable, so each of them is `𝔪_S`. -/
theorem ringKrullDim_quotient_map_maximalIdeal_eq_zero_of_quasiFinite {R S : Type*}
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra.QuasiFinite R S] :
    ringKrullDim (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) = 0 := by
  set I := (IsLocalRing.maximalIdeal R).map (algebraMap R S) with hIdef
  have hcomap := IsLocalRing.maximalIdeal_comap (algebraMap R S)
  have hI : I ≤ IsLocalRing.maximalIdeal S := Ideal.map_le_iff_le_comap.mpr hcomap.ge
  have hne : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top hI
  have : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  have hunder : ∀ Q : Ideal S, Q.IsPrime → I ≤ Q →
      Q.under R = IsLocalRing.maximalIdeal R := fun Q hQ hIQ =>
    ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.under R Q).ne_top
      (Ideal.map_le_iff_le_comap.mp hIQ)).symm
  have : Ring.KrullDimLE 0 (S ⧸ I) := by
    refine Ring.krullDimLE_zero_iff.mpr fun P hP => ?_
    have hP' : (P.comap (Ideal.Quotient.mk I)).IsPrime := Ideal.comap_isPrime _ _
    have hIP : I ≤ P.comap (Ideal.Quotient.mk I) := fun x hx => by
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    have heq : P.comap (Ideal.Quotient.mk I) = IsLocalRing.maximalIdeal S :=
      Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R) _ _
        (IsLocalRing.le_maximalIdeal hP'.ne_top)
        ((hunder _ hP' hIP).trans hcomap.symm)
    have hmax : (P.comap (algebraMap S (S ⧸ I))).IsMaximal := by
      show (P.comap (Ideal.Quotient.mk I)).IsMaximal
      rw [heq]; exact IsLocalRing.maximalIdeal.isMaximal S
    exact Ideal.IsIntegral.isMaximal_of_isMaximal_comap (R := S) P hmax
  exact le_antisymm (by exact_mod_cast (Ring.krullDimLE_iff (n := 0)).mp ‹_›)
    ringKrullDim_nonneg_of_nontrivial

/-- **Miracle flatness for a quasi-finite local homomorphism.** A quasi-finite local
homomorphism from a regular local ring to a Noetherian Cohen–Macaulay local ring of the same
Krull dimension is flat: its fibre ring has dimension zero, so the dimension formula of
[Stacks, Tag 00R4] reduces to the equality of the two dimensions. -/
@[ega "IV 15.4.2" "e′)⇒b), partial", ega "IV 6.1.5" "special case"]
theorem Module.Flat.of_isMaximalCohenMacaulay_of_quasiFinite
    {R S : Type*} [CommRing R] [IsRegularLocalRing R] [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [Algebra.QuasiFinite R S]
    (hS : Module.IsMaximalCohenMacaulay S S) (hdim : ringKrullDim S = ringKrullDim R) :
    Module.Flat R S := by
  refine Module.Flat.of_isMaximalCohenMacaulay_of_ringKrullDim_eq_add hS ?_
  rw [ringKrullDim_quotient_map_maximalIdeal_eq_zero_of_quasiFinite, add_zero, hdim]

/-- **Miracle flatness at a point of a scheme.** If `g : X ⟶ Y` is quasi-finite at `x`, the local
rings `𝒪_{Y, g x}` and `𝒪_{X, x}` are regular and of the same Krull dimension, then the stalk
map of `g` at `x` is flat. -/
theorem flat_stalkMap_of_quasiFiniteAt {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X)
    [IsRegularLocalRing (Y.presheaf.stalk (g x))] [IsRegularLocalRing (X.presheaf.stalk x)]
    (hqf : g.QuasiFiniteAt x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (g x))) :
    (g.stalkMap x).hom.Flat := by
  let : Algebra (Y.presheaf.stalk (g x)) (X.presheaf.stalk x) := (g.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (g x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (g.stalkMap x).hom)
  have : Algebra.QuasiFinite (Y.presheaf.stalk (g x)) (X.presheaf.stalk x) := hqf
  exact RingHom.flat_algebraMap_iff.mpr
    (Module.Flat.of_isMaximalCohenMacaulay_of_quasiFinite
      (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
        (X.presheaf.stalk x)).2 hdim)

/-- **A closed set which is not everything is nowhere dense in an irreducible space**: a nonempty
open subset of it would be dense, and so would the closed set. -/
@[ega "0 2.1.1" "partial"]
theorem _root_.IsClosed.isNowhereDense_of_ne_univ {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] {Z : Set T} (hZ : IsClosed Z) (hne : Z ≠ Set.univ) :
    IsNowhereDense Z := by
  rw [IsNowhereDense, hZ.closure_eq, Set.eq_empty_iff_forall_notMem]
  intro x hx
  apply hne
  have hd : Dense (interior Z) := isOpen_interior.dense ⟨x, hx⟩
  exact Set.eq_univ_of_univ_subset
    (hd.closure_eq ▸ closure_minimal interior_subset hZ)

/-- **A finite locally quasi-finite morphism into a Noetherian irreducible scheme of finite
dimension, from a scheme of the same dimension, is surjective.** Its image is closed and, the
fibres being discrete, has dimension at least that of the source; a proper closed subset of an
irreducible Noetherian space of finite dimension has strictly smaller dimension. -/
theorem surjective_of_isFinite_of_topologicalKrullDim_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IrreducibleSpace Y] [TopologicalSpace.NoetherianSpace Y]
    (hfin : topologicalKrullDim Y ≠ ⊤) (hdim : topologicalKrullDim Y ≤ topologicalKrullDim X) :
    Surjective f := by
  refine ⟨fun y => ?_⟩
  by_contra hy
  have hne : Set.range f ≠ Set.univ := fun h => hy (h.symm ▸ Set.mem_univ y : y ∈ Set.range f)
  have hclosed : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  have hlt := (hclosed.isNowhereDense_of_ne_univ hne).topologicalKrullDim_lt hclosed ⟨y⟩ hfin
  have hle : topologicalKrullDim X ≤ topologicalKrullDim (Set.range f) :=
    Topology.topologicalKrullDim_le_of_injOn_specializes (Set.rangeFactorization f)
      (f.continuous.subtype_mk _) fun a b hab he =>
        (f.isDiscrete_preimage_singleton (f b)).eq_of_specializes hab
          (by simpa using congrArg Subtype.val he) (by simp)
  exact absurd (hdim.trans hle) (not_le.mpr hlt)

/-- **A finite locally free morphism of integral schemes has rank the degree of its function
field extension**, provided its fibre over the generic point of the target is the generic point
of the source. The rank of `f_*𝒪_X` at the generic point is `[R(X) : R(Y)]`, and the rank of a
finite locally free module on an integral scheme is constant. -/
theorem isFiniteLocallyFreeOfRank_degreeOver {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [LocallyOfFiniteType f] [IsDominant f]
    [h : Stacks.Morphisms.IsFiniteLocallyFree f]
    (hgen : f (genericPoint X) = genericPoint Y)
    (hpre : f ⁻¹' ({genericPoint Y} : Set Y) = {genericPoint X}) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank f (degreeOver f) :=
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Morphisms.pushforwardStructureSheaf.{u} f) := h.toIsFiniteLocallyFree
  (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff f _).mpr ⟨h.toIsAffineHom,
    Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq _ _ (genericPoint Y)
      (fiberRank_pushforward_unit_genericPoint_eq_degreeOver_of_isFinite f hgen hpre)⟩

/-- **The fibre of a locally quasi-finite morphism over the image of the generic point of an
irreducible source is that generic point.** Every point of the source is a specialization of the
generic point, and two points of a fibre of a locally quasi-finite morphism one of which
specializes to the other are equal. -/
theorem preimage_genericPoint_of_locallyQuasiFinite {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) [LocallyQuasiFinite f]
    (hgen : f (genericPoint X) = genericPoint Y) :
    f ⁻¹' ({genericPoint Y} : Set Y) = {genericPoint X} := by
  refine Set.Subset.antisymm (fun x hx => ?_) (by simpa using hgen)
  exact ((f.isDiscrete_preimage_singleton (genericPoint Y)).eq_of_specializes
    ((genericPoint_spec X).specializes trivial) (by simpa using hgen) hx).symm

/-! ### Self-intersection numbers of isomorphic modules and of tensor powers -/

section SelfIntersection

open Stacks.SheafOfModules.Invertible (tensorPower)

attribute [local instance] isInvertible_update

variable (k : Type u) [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞))

/-- The family which is `M'` on the slots in `s` and `M` elsewhere. -/
private noncomputable abbrev slotFamily (M M' : X.Modules) (s : Finset (Fin d)) :
    Fin d → X.Modules := fun j => if j ∈ s then M' else M

private theorem isInvertible_slotFamily (M M' : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M'] (s : Finset (Fin d))
    (j : Fin d) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (slotFamily d M M' s j) := by
  by_cases h : j ∈ s
  · simp only [slotFamily, if_pos h]; infer_instance
  · simp only [slotFamily, if_neg h]; infer_instance

/-- **The self-intersection number depends only on the isomorphism class of the module.** Each
of the `d` slots is replaced in turn, by `AlgebraicGeometry.intersectionNumber_eq_of_iso_at`. -/
theorem selfIntersectionNumber_eq_of_iso (M M' : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M'] (e : M ≅ M') :
    selfIntersectionNumber k f i d hd M = selfIntersectionNumber k f i d hd M' := by
  have := isInvertible_slotFamily d M M'
  have key : ∀ s : Finset (Fin d), intersectionNumber k f i d hd (slotFamily d M M' ∅) =
      intersectionNumber k f i d hd (slotFamily d M M' s) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s has ih =>
      refine ih.trans (intersectionNumber_eq_of_iso_at k f i d hd _ _ a (fun q hq => ?_) ?_)
      · simp [slotFamily, Finset.mem_insert, hq]
      · exact eqToIso (by simp [slotFamily, has]) ≪≫ e ≪≫ eqToIso (by simp [slotFamily])
  have h0 : slotFamily d M M' ∅ = fun _ => M := funext fun j => by simp [slotFamily]
  have h1 : slotFamily d M M' Finset.univ = fun _ => M' := funext fun j => by simp [slotFamily]
  rw [selfIntersectionNumber_eq_intersectionNumber, selfIntersectionNumber_eq_intersectionNumber,
    ← intersectionNumber_congr_family k f i d hd h0,
    ← intersectionNumber_congr_family k f i d hd h1]
  exact key Finset.univ

/-- The tensor power of a module equal to `M` is the tensor power of `M`, whatever the
invertibility instances. -/
private theorem tensorPower_eq_of_eq {M N : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] (h : N = M) (n : ℤ) :
    tensorPower X.presheaf X.ringCatSheaf.2 N n = tensorPower X.presheaf X.ringCatSheaf.2 M n := by
  subst h; rfl

/-- **The self-intersection number of a tensor power.** `((𝓛^{⊗ n})^d · Z) = n^d (𝓛^d · Z)`:
each of the `d` slots is replaced in turn, by
`AlgebraicGeometry.intersectionNumber_update_tensorPower`. -/
theorem selfIntersectionNumber_tensorPower (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (n : ℕ) :
    selfIntersectionNumber k f i d hd (tensorPower X.presheaf X.ringCatSheaf.2 M (n : ℤ)) =
      (n : ℤ) ^ d * selfIntersectionNumber k f i d hd M := by
  set T := tensorPower X.presheaf X.ringCatSheaf.2 M (n : ℤ) with hT
  have := isInvertible_slotFamily d M T
  have key : ∀ s : Finset (Fin d),
      intersectionNumber k f i d hd (slotFamily d M T s) =
        (n : ℤ) ^ s.card * intersectionNumber k f i d hd (slotFamily d M T ∅) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s has ih =>
      have h := intersectionNumber_update_tensorPower k f i d hd (slotFamily d M T s) a n
      have : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
          (Function.update (slotFamily d M T s) a
            (tensorPower X.presheaf X.ringCatSheaf.2 (slotFamily d M T s a) (n : ℤ)) q) :=
        isInvertible_update (slotFamily d M T s) a _
      have hiso := intersectionNumber_eq_of_iso_at k f i d hd
        (Function.update (slotFamily d M T s) a
          (tensorPower X.presheaf X.ringCatSheaf.2 (slotFamily d M T s a) (n : ℤ)))
        (slotFamily d M T (insert a s)) a
        (fun q hq => (Function.update_of_ne hq _ _).symm ▸ (by simp [slotFamily, hq]))
        (eqToIso (Function.update_self _ _ _) ≪≫
          eqToIso (tensorPower_eq_of_eq (N := slotFamily d M T s a) (M := M)
            (by simp [slotFamily, has]) _) ≪≫
          eqToIso (if_pos (Finset.mem_insert_self a s)).symm)
      rw [← hiso, h, ih, Finset.card_insert_of_notMem has, pow_succ]
      ring
  have h0 : slotFamily d M T ∅ = fun _ => M := funext fun j => by simp [slotFamily]
  have h1 : slotFamily d M T Finset.univ = fun _ => T :=
    funext fun j => if_pos (Finset.mem_univ j)
  have h := key Finset.univ
  rwa [intersectionNumber_congr_family k f i d hd h0,
    intersectionNumber_congr_family k f i d hd h1, Finset.card_univ, Fintype.card_fin] at h

end SelfIntersection

end AlgebraicGeometry

namespace Stacks.Groupoids

open scoped CategoryTheory.MonObj
open Stacks.SheafOfModules (schemeTensor schemeTensorPower picardClass pullbackPicardClass
  isInvertible_schemeTensor pullbackPicardClass_comp pullbackPicardClass_id
  pullbackPicardClass_schemeTensor picardClass_schemeTensor)

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- **An abelian variety carries an ample invertible module.** It is quasi-projective over `k`, a
group scheme of finite type over a field being so (Tag 0BF7), and the spectrum of a field carries
the ample structure sheaf, so its source carries an ample invertible module. -/
theorem exists_isAmple_of_isAbelianVariety [AlgebraicGeometry.IsAbelianVariety k A] :
    ∃ (L : A.left.Modules) (_ : Stacks.Ample.IsInvertibleModule A.left L),
      Stacks.Ample.IsAmple A.left L := by
  have : LocallyOfFiniteType (Grp.mk A).X.hom := inferInstanceAs (LocallyOfFiniteType A.hom)
  have : QuasiCompact (Grp.mk A).X.hom := inferInstanceAs (QuasiCompact A.hom)
  have hqp : IsQuasiProjective A.hom := isQuasiProjective_of_groupScheme_over_field (Grp.mk A)
  obtain ⟨M, hM, hMa⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of k))
  exact exists_isAmple_of_isQuasiProjective A.hom M hMa hqp

/-- **The pullback of an ample module along an isomorphism is ample**, an isomorphism being an
affine morphism. -/
theorem isAmple_modulePullback_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (L : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y L] (hL : Stacks.Ample.IsAmple Y L) :
    Stacks.Ample.IsAmple X ((modulePullback f.toLRSHom.toShHom).obj L) :=
  have : IsQuasiAffineHom f := isQuasiAffineHom_of_isAffineHom f
  Stacks.SectionRatioNoAmple.isAmple_modulePullback_of_isQuasiAffineHom f L hL

/-- **An abelian variety carries a symmetric ample invertible module.** For `L` ample, the
module `N = L ⊗ [-1]^* L` is ample, being a tensor product of two ample modules (Tag 0890), and
`[-1]^* N ≅ N` because `[-1] ∘ [-1]` is the identity. -/
theorem exists_isAmple_symmetric [AlgebraicGeometry.IsAbelianVariety k A] :
    ∃ (N : A.left.Modules) (_ : Stacks.SheafOfModules.IsInvertible A.left.presheaf
        A.left.ringCatIsSheaf N),
      Stacks.Ample.IsAmple A.left N ∧ Nonempty (pullbackOver (ι : A ⟶ A) N ≅ N) := by
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isAbelianVariety A
  have hι : IsIso (ι : A ⟶ A).left :=
    ((Over.forget (Spec (.of k))).mapIso (asIso (ι : A ⟶ A))).isIso_hom
  have hM : Stacks.Ample.IsInvertibleModule A.left (pullbackOver (ι : A ⟶ A) L) :=
    modulePullback_isInvertible_scheme _ L
  have hMa : Stacks.Ample.IsAmple A.left (pullbackOver (ι : A ⟶ A) L) :=
    isAmple_modulePullback_of_isIso _ L hLa
  have hL' := Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple A.left L hLa
  have hM' := Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple A.left _ hMa
  have hNa := Scheme.Modules.isAmple_tensor_of_power_sections_cover A.left L
    (pullbackOver (ι : A ⟶ A) L) hL' (fun x => by
      obtain ⟨n, hn, s, hx, -⟩ := hM'.2 x
      exact ⟨n, hn, s, hx⟩)
  let hNinv := isInvertible_schemeTensor A.left L (pullbackOver (ι : A ⟶ A) L) hL hM
  refine ⟨schemeTensor A.left L (pullbackOver (ι : A ⟶ A) L), hNinv,
    Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple A.left _ hNa, ?_⟩
  refine (Stacks.SheafOfModules.picardClass_eq_iff A.left.presheaf A.left.ringCatIsSheaf _ _
    (isInvertible_pullbackOver (ι : A ⟶ A) _ hNinv) hNinv).mp ?_
  have hιι : pullbackPicardClass (ι : A ⟶ A).left (pullbackOver (ι : A ⟶ A) L) hM =
      picardClass A.left.presheaf A.left.ringCatIsSheaf L hL := by
    have h2 : (ι : A ⟶ A).left ≫ (ι : A ⟶ A).left = 𝟙 A.left := by
      rw [← Over.comp_left, GrpObj.inv_comp_inv, Over.id_left]
    exact (Stacks.SheafOfModules.picardClass_eq_iff A.left.presheaf A.left.ringCatIsSheaf _ _
      (Stacks.RingedSpace.modulePullback_isInvertible _ _) hL).mpr
      ⟨((modulePullbackComp (ι : A ⟶ A).left.toLRSHom.toShHom
          (ι : A ⟶ A).left.toLRSHom.toShHom).app L).symm ≪≫
        eqToIso (congrArg (fun φ => (modulePullback φ).obj L)
          (congrArg (fun m : A.left ⟶ A.left => m.toLRSHom.toShHom) h2)) ≪≫
        (modulePullbackId A.left.toRingedSpace).app L⟩
  have h3 := pullbackPicardClass_schemeTensor (ι : A ⟶ A).left L (pullbackOver (ι : A ⟶ A) L)
    hL hM
  have h4 := picardClass_schemeTensor A.left L (pullbackOver (ι : A ⟶ A) L) hL hM
  refine h3.trans ?_
  refine Eq.trans ?_ h4.symm
  rw [hιι, add_comm]
  rfl

/-- The two triangular numbers of Tag 0BFF add up to a square: `n(n+1)/2 + n(n-1)/2 = n²`. -/
theorem triangularNumber_add_triangularNumber_neg (n : ℤ) :
    triangularNumber n + triangularNumber (-n) = n * n := by
  linarith [two_mul_triangularNumber n, two_mul_triangularNumber (-n)]

/-- **Tag 0BFF for a symmetric module.** If `[-1]^* N ≅ N`, then `[n]^* N ≅ N^{⊗ n²}` for every
integer `n`, granted the theorem of the cube for `A` (`HasTheoremOfTheCube A`, the hypothesis of
`Stacks.Groupoids.nonempty_zpowId_pullback_iso`). -/
theorem nonempty_zpowId_pullback_iso_of_symmetric [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A)
    (N : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
    (hN : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf N)
    (e : pullbackOver (ι : A ⟶ A) N ≅ N) (n : ℤ) :
    Nonempty (pullbackOver ((𝟙 A : A ⟶ A) ^ n) N ≅ schemeTensorPower A.left N hN (n * n)) := by
  refine (Stacks.SheafOfModules.picardClass_eq_iff A.left.presheaf A.left.ringCatIsSheaf _ _
    (isInvertible_pullbackOver ((𝟙 A : A ⟶ A) ^ n) N hN)
    (Stacks.SheafOfModules.isInvertible_schemeTensorPower A.left N hN (n * n))).mp ?_
  have hι : pullbackPicardClass (ι : A ⟶ A).left N hN =
      picardClass A.left.presheaf A.left.ringCatIsSheaf N hN :=
    (Stacks.SheafOfModules.picardClass_eq_iff A.left.presheaf A.left.ringCatIsSheaf _ _ _ hN).mpr
      ⟨e⟩
  have key := zpowIdPicardClass_eq A N hN hcube n
  rw [hι, ← add_smul, triangularNumber_add_triangularNumber_neg] at key
  exact key.trans (Stacks.SheafOfModules.picardClass_schemeTensorPower A.left N hN (n * n)).symm

/-- The inclusion of a point into an abelian variety is an affine morphism: its source is affine
and the abelian variety is separated over the ground field. -/
theorem isAffineHom_fromSpecResidueField [AlgebraicGeometry.IsAbelianVariety k A] (y : A.left) :
    IsAffineHom (A.left.fromSpecResidueField y) :=
  MorphismProperty.of_postcomp (W := @IsAffineHom) (W' := @IsSeparated) _ A.hom inferInstance
    inferInstance

/-- **Multiplication by a nonzero integer on an abelian variety is finite**, granted the theorem
of the cube for `A`. For the symmetric ample module `N`, `[d]^* N ≅ N^{⊗ d²}` is ample, and a
proper morphism along which an invertible module pulls back to an ample one is finite. -/
theorem isFinite_zpow_id_left [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) (d : ℤ) (hd : d ≠ 0) :
    IsFinite ((𝟙 A : A ⟶ A) ^ d).left := by
  obtain ⟨N, hN, hNa, ⟨e⟩⟩ := exists_isAmple_symmetric A
  obtain ⟨f⟩ := nonempty_zpowId_pullback_iso_of_symmetric A hcube N hN e d
  have := isProper_zpow_id_left A d
  have hm : 1 ≤ d.natAbs * d.natAbs :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr hd)
      (Int.natAbs_ne_zero.mpr hd))
  have hpow := Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple N _ hm hNa
  have hcast : ((d.natAbs * d.natAbs : ℕ) : ℤ) = d * d := Int.natAbs_mul_self
  rw [hcast] at hpow
  have hinv : Stacks.Ample.IsInvertibleModule A.left (pullbackOver ((𝟙 A : A ⟶ A) ^ d) N) :=
    modulePullback_isInvertible_scheme _ N
  have hample : Stacks.Ample.IsAmple A.left (pullbackOver ((𝟙 A : A ⟶ A) ^ d) N) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _
      (f ≪≫ Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso A.left N (d * d))).mpr hpow
  exact isFinite_of_isProper_of_isAmple_modulePullback _ (isAffineHom_fromSpecResidueField A) N
    hample

/-- A finite multiplication by a nonzero integer on an abelian variety is surjective: the source
and target are the same irreducible variety, of finite dimension. -/
private theorem surjective_zpow_id_left [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ)
    [IsFinite ((𝟙 A : A ⟶ A) ^ d).left] : Surjective ((𝟙 A : A ⟶ A) ^ d).left :=
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have := isLocallyNoetherian_left A
  have : IsNoetherian A.left := {}
  surjective_of_isFinite_of_topologicalKrullDim_le _
    (topologicalKrullDim_ne_top_of_isProper k A.hom) le_rfl

/-- **Multiplication by a nonzero integer on an abelian variety is flat**, granted the theorem of
the cube for `A`. It is finite (`isFinite_zpow_id_left`), hence surjective, the source and target
being the same irreducible variety; so it preserves the dimension of every local ring, the
target being universally catenary, and the local rings of the smooth variety `A` are regular. By
miracle flatness ([Stacks, Tag 00R4]) every stalk map is flat. -/
theorem flat_zpow_id_left [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) (d : ℤ) (hd : d ≠ 0) :
    Flat ((𝟙 A : A ⟶ A) ^ d).left := by
  have := isFinite_zpow_id_left A hcube d hd
  have := smooth_hom A
  have := isLocallyNoetherian_left A
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsNoetherian A.left := {}
  have := surjective_zpow_id_left A d
  have hdom : IsDominant ((𝟙 A : A ⟶ A) ^ d).left := inferInstance
  have hS := Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_field k A.hom
  rw [Flat.iff_flat_stalkMap]
  intro x
  have := isRegularLocalRing_stalk_of_smooth_over_field A.hom x
  have := isRegularLocalRing_stalk_of_smooth_over_field A.hom (((𝟙 A : A ⟶ A) ^ d).left x)
  exact flat_stalkMap_of_quasiFiniteAt _ x (Scheme.Hom.quasiFiniteAt _ x)
    (ringKrullDim_stalk_eq_of_locallyQuasiFinite _ hS x)

/-- **Multiplication by a nonzero integer on an abelian variety is finite locally free**, granted
the theorem of the cube for `A`: it is finite and flat, over a locally Noetherian base. -/
theorem isFiniteLocallyFree_zpow_id_left [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) (d : ℤ) (hd : d ≠ 0) :
    Stacks.Morphisms.IsFiniteLocallyFree ((𝟙 A : A ⟶ A) ^ d).left :=
  have := isFinite_zpow_id_left A hcube d hd
  have := flat_zpow_id_left A hcube d hd
  isFiniteLocallyFree_of_isFinite_of_flat A _

/-- The dimension of an abelian variety is the natural number `abelianVarietyDimension A`: the
underlying scheme is nonempty and of finite dimension, being proper over a field. -/
theorem topologicalKrullDim_eq_abelianVarietyDimension [AlgebraicGeometry.IsAbelianVariety k A] :
    topologicalKrullDim A.left = (abelianVarietyDimension A : WithBot ℕ∞) := by
  have htop := topologicalKrullDim_ne_top_of_isProper k A.hom
  have hbot : topologicalKrullDim A.left ≠ ⊥ := fun h =>
    (not_isEmpty_of_nonempty A.left) ((topologicalKrullDim_eq_bot_iff_isEmpty _).mp h)
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hmtop : m ≠ ⊤ := by rintro rfl; exact htop hm.symm
  obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp hmtop
  unfold abelianVarietyDimension
  rw [← hm]
  rfl

/-- The self-intersection number does not depend on how the structure morphism is written. -/
private theorem selfIntersectionNumber_congr_structure {X : Scheme.{u}} {p p' : X ⟶ Spec (.of k)}
    (h : p = p') [IsProper p] [IsProper p'] (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    selfIntersectionNumber k p (𝟙 X) d hd M = selfIntersectionNumber k p' (𝟙 X) d hd M := by
  subst h; rfl

/-- **The degree of multiplication by a nonzero integer `d` on an abelian variety is
`|d| ^ (2 dim A)`**, granted the theorem of the cube for `A`. For the symmetric ample module `N`,
`[d]^* N ≅ N^{⊗ d²}`, so by [Stacks, Tag 0BEX]
`deg([d]) (N^g · A) = ([d]^* N^g · A) = ((N^{⊗ d²})^g · A) = d^{2g} (N^g · A)`, and
`(N^g · A) > 0` ([Stacks, Tag 0BEV]). -/
theorem degreeOver_zpow_id_left [AlgebraicGeometry.IsAbelianVariety k A]
    (hcube : HasTheoremOfTheCube A) (d : ℤ) (hd : d ≠ 0) :
    haveI := isFinite_zpow_id_left A hcube d hd
    haveI : Surjective ((𝟙 A : A ⟶ A) ^ d).left :=
      have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
      have := isLocallyNoetherian_left A
      have : IsNoetherian A.left := {}
      surjective_of_isFinite_of_topologicalKrullDim_le _
        (topologicalKrullDim_ne_top_of_isProper k A.hom) le_rfl
    degreeOver ((𝟙 A : A ⟶ A) ^ d).left = d.natAbs ^ (2 * abelianVarietyDimension A) := by
  have := isFinite_zpow_id_left A hcube d hd
  have := surjective_zpow_id_left A d
  set f := ((𝟙 A : A ⟶ A) ^ d).left with hfdef
  set g := abelianVarietyDimension A
  have hdim := topologicalKrullDim_eq_abelianVarietyDimension A
  obtain ⟨N, hN, hNa, ⟨e⟩⟩ := exists_isAmple_symmetric A
  obtain ⟨e₁⟩ := nonempty_zpowId_pullback_iso_of_symmetric A hcube N hN e d
  have : SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatSheaf.2 N := hN
  have hfp : f ≫ A.hom = A.hom := zpow_id_left_comp_hom A d
  have : IsVariety k (f ≫ A.hom) := by rw [hfp]; infer_instance
  have : IsProper (f ≫ A.hom) := by rw [hfp]; infer_instance
  have h0BEX := selfIntersectionNumber_pullback_of_isFinite k A.hom f g hdim N
  rw [selfIntersectionNumber_congr_structure hfp] at h0BEX
  have : SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatSheaf.2
      ((Scheme.Modules.pullback f).obj N) := modulePullback_isInvertible_scheme f N
  set m := d.natAbs * d.natAbs with hm
  have hcast : ((m : ℕ) : ℤ) = d * d := Int.natAbs_mul_self
  have e₂ : (Scheme.Modules.pullback f).obj N ≅
      Stacks.SheafOfModules.Invertible.tensorPower A.left.presheaf A.left.ringCatSheaf.2 N
        ((m : ℕ) : ℤ) :=
    e₁ ≪≫ eqToIso (by rw [hcast]; rfl)
  rw [selfIntersectionNumber_eq_of_iso k A.hom (𝟙 A.left) g _ _ _ e₂,
    selfIntersectionNumber_tensorPower] at h0BEX
  have hpos := selfIntersectionNumber_pos k A.hom (𝟙 A.left) g hdim N
    (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple A.left N hNa)
  have key : (degreeOver f : ℤ) = (m : ℤ) ^ g :=
    (mul_right_cancel₀ hpos.ne' h0BEX).symm
  have : degreeOver f = m ^ g := by exact_mod_cast key
  rw [this, hm, ← pow_two, ← pow_mul]

/-- **Multiplication by a nonzero integer `d` on an abelian variety is finite locally free of
degree `|d| ^ (2 dim A)`**, granted the theorem of the cube for `A` (`HasTheoremOfTheCube A`, the
conclusion of [Stacks, Tag 0BF4] for `A × A × A`). This is the statement of [Stacks, Tag 0BFG]
for `d ≠ 0`, with that one input. For `d = 0` and `dim A ≥ 1` the statement of the source is
false: `[0]` factors through the unit point, so its fibre over the unit is all of `A` and `[0]`
is not finite.

The morphism is finite and flat (`isFiniteLocallyFree_zpow_id_left`), its rank is the degree of
the extension of function fields (`isFiniteLocallyFreeOfRank_degreeOver`), and that degree is
`|d| ^ (2 dim A)` (`degreeOver_zpow_id_left`). -/
theorem isFiniteLocallyFreeOfRank_zpow_id_left_of_hasTheoremOfTheCube
    [AlgebraicGeometry.IsAbelianVariety k A] (hcube : HasTheoremOfTheCube A) (d : ℤ)
    (hd : d ≠ 0) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((𝟙 A : A ⟶ A) ^ d).left
      (d.natAbs ^ (2 * abelianVarietyDimension A)) := by
  have := isFinite_zpow_id_left A hcube d hd
  have := isFiniteLocallyFree_zpow_id_left A hcube d hd
  have := surjective_zpow_id_left A d
  have hgen := genericPoint_eq_of_surjective ((𝟙 A : A ⟶ A) ^ d).left
  have h := isFiniteLocallyFreeOfRank_degreeOver ((𝟙 A : A ⟶ A) ^ d).left hgen
    (preimage_genericPoint_of_locallyQuasiFinite _ hgen)
  rwa [degreeOver_zpow_id_left A hcube d hd] at h

end Stacks.Groupoids

end
