module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleLocalDimension
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.ElementaryDevissage
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.FibrePoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.ClosedImmersionPushforward
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension

/-!
# A one-step dévissage after elementary étale neighbourhoods

Let `f : X ⟶ S` be locally of finite type and let `F` be a finite-type quasi-coherent
`𝒪_X`-module whose restriction to the fibre of `f` through a point `x` has `x` in its support.
Then there are elementary étale neighbourhoods `U` of `(X, x)` and `V` of `(S, f x)` and a
morphism `U ⟶ V` making the square commute, such that the pullback of `F` to `U` has a one-step
dévissage at the distinguished point of `U`. That is Stacks 05H6.

That support hypothesis is not an extra assumption but the exact condition under which the
source's conclusion can hold, and this is proved here: see the discussion of the degenerate
case below and
`AlgebraicGeometry.exists_etaleNeighborhood_oneStepDevissageAt_iff_mem_fiber_supp`.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_fiber_eq_of_smoothOfRelativeDimension`: a morphism
  smooth of relative dimension `n` with geometrically integral fibres has every fibre of
  dimension `n`.
* `AlgebraicGeometry.exists_etaleNeighborhood_oneStepDevissageAt` is Stacks 05H6.
* `AlgebraicGeometry.exists_etaleNeighborhood_oneStepDevissageAt_iff_mem_fiber_supp` is Stacks
  05H6 together with the converse: those neighbourhoods exist precisely at the points of the
  support of the module on the fibre.
* `AlgebraicGeometry.OneStepDevissageAt.mem_supp` and
  `AlgebraicGeometry.isEmpty_oneStepDevissage_of_supp_eq_empty` are the two halves of that
  converse.

## The degenerate case

The source states Tag 05H6 for an arbitrary point `x ∈ X`, but its conclusion presupposes
`x ∈ Supp(F_s)`, where `s = f x`: condition (1) of Tag 05H5 is
`dim_x(Supp(F_s)) = dim(Supp(F_s))`, and `dim_x(T)` is defined only for a point `x` *of* the
space `T` (Tag 0055 (4), `topologicalKrullDimAt`, the minimum of `dim(U)` over the open
neighbourhoods of `x` in `T`). Accordingly
`AlgebraicGeometry.OneStepDevissageAt.mem_fiber_support` is a field of a one-step dévissage at
`x`, and there is no degenerate dévissage to fall back on when `x ∉ Supp(F_s)`:

* if `Supp(F_s) ≠ ∅`, reading condition (1) with the convention `dim_x(T) = -∞` for `x ∉ T`
  makes it fail, since its right-hand side is then `≥ 0`;
* if `Supp(F_s) = ∅`, condition (1) reads `-∞ = -∞`, but there is no one-step dévissage over
  `s` at all, by `AlgebraicGeometry.isEmpty_oneStepDevissage_of_supp_eq_empty`: condition (5)
  of Tag 05H4 asks the fibres of `Y → S` to be geometrically irreducible of dimension
  `dim(Supp(F_s)) = -∞`, and an irreducible space is nonempty, hence of dimension `≥ 0`.

The consumer of Tag 05H6 in the Stacks project, Tag 05HR, treats the two cases separately for
exactly this reason: `x ∉ Supp(F)` is settled there by the empty complete dévissage on the
complement of the support, see
`AlgebraicGeometry.exists_etaleNeighborhood_completeDevissageAt_of_notMem_supp`.

## Implementation notes

The data are exactly those of an elementary dévissage (Stacks 057S,
`AlgebraicGeometry.ElementaryDevissage`): the two neighbourhoods, the square, the closed
immersion `i : Z ⟶ U` with `i_* G ≅ g^* F`, and the finite morphism `π : Z ⟶ Y` over the smooth
`h : Y ⟶ V`. What has to be supplied is the one numerical field of
`AlgebraicGeometry.OneStepDevissage` that an elementary dévissage does not record in that form:
every fibre of `h` must have topological Krull dimension equal to the dimension of the support
of the pulled-back module on the distinguished fibre.

Both sides are computed to be the integer `n` of the elementary dévissage. For the fibres of `h`
this is `AlgebraicGeometry.topologicalKrullDim_fiber_eq_of_smoothOfRelativeDimension`: the local
dimension at each point of a fibre is `n` by Tag 0B9D
(`AlgebraicGeometry.fiberDimensionAt_eq_of_smoothOfRelativeDimension`), and geometric integrality
makes the fibre irreducible, so its dimension is that common local dimension.

For the support `B` of the pulled-back module on the fibre of `U ⟶ V` over the distinguished
point, the two inequalities come from different places.

* `≥` is the local dimension of `B` at the distinguished point, which agrees with the local
  dimension of the original support `A` because the comparison morphism `φ` of fibres across
  the square is étale (Stacks 04NI) and `B = φ⁻¹(A)`; the dimension of a closed subset is
  unchanged along an étale morphism by
  `Topology.topologicalKrullDimAt_eq_of_isOpenMap_of_specializes_injective`.
* `≤` uses that `B` is contained in the image of the fibre of `Z`: the support of a direct
  image along a closed immersion is contained in the image, so `B` lies in the range of the
  comparison map from the fibre of `i ≫ (U ⟶ V)`, whose dimension is at most that of the fibre
  of `h` because `π` is finite, hence integral (Stacks 0ECG).

## References

* [Stacks Project, Tag 05H6](https://stacks.math.columbia.edu/tag/05H6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The local dimension of a fibre along an étale comparison -/

/-- An étale morphism of schemes does not change the local Krull dimension of the preimage of a
closed subset of its target. -/
private theorem topologicalKrullDimAt_preimage_eq_of_etale {P Q : Scheme.{u}} (φ : P ⟶ Q)
    [Etale φ] (A : Set Q) (hA : IsClosed A) (p : P) (hp : φ p ∈ A) :
    topologicalKrullDimAt (φ ⁻¹' A) ⟨p, hp⟩ = topologicalKrullDimAt A ⟨φ p, hp⟩ := by
  have hqf := locallyQuasiFinite_of_etale φ
  have : LocallyOfFiniteType φ := hqf.1
  have : LocallyQuasiFinite φ := hqf.2
  let r := A.restrictPreimage (φ : P → Q)
  have hrInj : ∀ ⦃u v : (φ : P → Q) ⁻¹' A⦄, u ⤳ v → r u = r v → u = v := by
    intro u v huv hEq
    have huv' : (u : P) ⤳ (v : P) := (subtype_specializes_iff u v).mp huv
    have hval : φ (u : P) = φ (v : P) := congrArg Subtype.val hEq
    exact Subtype.ext ((φ.isDiscrete_preimage_singleton (φ (u : P))).eq_of_specializes huv'
      (by simp) (by simp [hval]))
  have : QuasiSober (↥A) := hA.isClosedEmbedding_subtypeVal.quasiSober
  have : QuasiSober (↥((φ : P → Q) ⁻¹' A)) :=
    (hA.preimage φ.continuous).isClosedEmbedding_subtypeVal.quasiSober
  exact Topology.topologicalKrullDimAt_eq_of_isOpenMap_of_specializes_injective r
    (continuous_induced_rng.mpr (φ.continuous.comp continuous_subtype_val))
    (φ.isOpenMap.restrictPreimage A) hrInj
    ((Flat.generalizingMap φ).restrictPreimage A) ⟨p, hp⟩

/-! ### Fibres of a smooth morphism of given relative dimension -/

/-- The fibre of a morphism over a point may be transported along an equality of points. -/
public def fiberCongr {X S : Scheme.{u}} (f : X ⟶ S) {a b : S} (h : a = b) :
    f.fiber a ≅ f.fiber b := by
  cases h
  exact Iso.refl _

/-- Transporting a fibre along an equality of points is compatible with the inclusions of the
two fibres into the source. -/
public theorem fiberCongr_hom_fiberι {X S : Scheme.{u}} (f : X ⟶ S) {a b : S} (h : a = b) :
    (fiberCongr f h).hom ≫ f.fiberι b = f.fiberι a := by
  cases h
  rfl

/-- The fibre of a morphism may be transported along an equality of morphisms. -/
private def fiberCongrHom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (s : Y) :
    f.fiber s ≅ g.fiber s := by
  cases h
  exact Iso.refl _

private theorem fiberCongrHom_inv_fiberι {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (s : Y) :
    (fiberCongrHom h s).inv ≫ f.fiberι s = g.fiberι s := by
  cases h
  rfl

/-- The local Krull dimension of a subset at a point does not depend on which of two equal
descriptions of the subset is used. -/
private theorem topologicalKrullDimAt_of_eq_set {Y : Type*} [TopologicalSpace Y] {s t : Set Y}
    (h : s = t) (y : Y) (hs : y ∈ s) (ht : y ∈ t) :
    topologicalKrullDimAt s ⟨y, hs⟩ = topologicalKrullDimAt t ⟨y, ht⟩ := by
  subst h
  rfl

/-- A morphism smooth of relative dimension `n` whose fibres are geometrically integral has all
its fibres of dimension `n`. -/
theorem topologicalKrullDim_fiber_eq_of_smoothOfRelativeDimension {X S : Scheme.{u}} (n : ℕ)
    (f : X ⟶ S) [SmoothOfRelativeDimension n f]
    (hGI : ∀ t : S, GeometricallyIntegral (f.fiberToSpecResidueField t)) (t : S) :
    topologicalKrullDim (f.fiber t) = (n : WithBot ℕ∞) := by
  have hloc (z : f.fiber t) : localKrullDim (f.fiber t) z = (n : WithBot ℕ∞) := by
    rw [← topologicalKrullDimAt_eq_localKrullDim]
    let y := f.fiberι t z
    have hdim := fiberDimensionAt_eq_of_smoothOfRelativeDimension f n y
    have hpoint1 : f.fiberHomeo (f y) (f.asFiber y) = ⟨y, rfl⟩ := by
      apply Subtype.ext
      simp [Scheme.Hom.asFiber]
    have hdimSet : topologicalKrullDimAt ((f : X → S) ⁻¹' {f y}) ⟨y, rfl⟩ =
        (n : WithBot ℕ∞) := by
      have hh := topologicalKrullDimAt_eq_of_homeomorph (f.fiberHomeo (f y)) (f.asFiber y)
      rw [hpoint1] at hh
      exact hh.symm.trans hdim
    have hsets : (f : X → S) ⁻¹' {f y} = (f : X → S) ⁻¹' {t} :=
      congrArg (fun s => (f : X → S) ⁻¹' {s}) (f.fiberHomeo t z).property
    calc
      topologicalKrullDimAt (f.fiber t) z =
          topologicalKrullDimAt ((f : X → S) ⁻¹' {t}) (f.fiberHomeo t z) :=
        topologicalKrullDimAt_eq_of_homeomorph (f.fiberHomeo t) z
      _ = topologicalKrullDimAt ((f : X → S) ⁻¹' {f y}) ⟨y, rfl⟩ :=
        (topologicalKrullDimAt_of_eq_set hsets.symm y (f.fiberHomeo t z).property rfl)
      _ = (n : WithBot ℕ∞) := hdimSet
  have := hGI t
  have : IsIntegral (f.fiber t) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (f.fiberToSpecResidueField t)
  rw [topologicalKrullDim_eq_iSup_localKrullDim, iSup_congr hloc, iSup_const]

/-! ### Points of the support, on the scheme and on a fibre -/

/-- A point lies in the support of `F` exactly when the corresponding point of the fibre lies in
the support of the module on the fibre. -/
theorem mem_supp_fiber_iff_mem_supp {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    [F.IsFiniteType] (x : X) :
    f.asFiber x ∈ SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) ↔
      x ∈ SheafOfModules.supp F := by
  rw [Stacks.Modules.supp_pullback]
  simp only [Set.mem_preimage, Scheme.Hom.fiberι_asFiber]

/-! ### The support of a direct image along a closed immersion -/

/-- The support of the direct image of a module along a closed immersion is contained in the
image of the closed immersion: outside that image the stalk of the direct image is zero. -/
private lemma supp_pushforward_subset_range {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (F : Y.Modules) :
    SheafOfModules.supp ((Scheme.Modules.pushforward i).obj F) ⊆ Set.range (i : Y → X) := by
  intro x hx
  change ∃ a : ((Scheme.Modules.pushforward i).obj F).presheaf.stalk x, a ≠ 0 at hx
  by_contra hnot
  let Gsh : TopCat.Sheaf AddCommGrpCat.{u} Y.toTopCat := ⟨F.presheaf, F.isSheaf⟩
  have hz : IsTerminal (((Scheme.Modules.pushforward i).obj F).presheaf.stalk x) := by
    show IsTerminal (TopCat.Presheaf.stalk
      ((TopCat.Sheaf.pushforward AddCommGrpCat i.base).obj Gsh).1 x)
    exact ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange
      i.base Gsh.property i.isClosedEmbedding x hnot
  obtain ⟨a, ha⟩ := hx
  have hab : 𝟙 (((Scheme.Modules.pushforward i).obj F).presheaf.stalk x) = 0 := hz.hom_ext _ _
  exact ha (by simpa using congrArg (fun k => k a) hab)

/-! ### Comparison of fibres across a composite -/

/- `fiberCompMap`, `fiberCompMap_fiberι` and `fiberCompMap_isClosedImmersion` stood here, each a
private re-proof of a public declaration of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/NowhereDenseFibres/FibrePoints.lean`, which this
module now imports. Those live in `AlgebraicGeometry.Scheme.Hom`:

* `fiberMapComp` (StacksFrontier/AlgebraicGeometry/MoreMorphisms/NowhereDenseFibres/FibrePoints.lean:78) was byte-identical to `fiberCompMap`;
* `fiberMapComp_fiberι` (StacksFrontier/AlgebraicGeometry/MoreMorphisms/NowhereDenseFibres/FibrePoints.lean:83) has the statement `fiberCompMap_fiberι` had, and
  the same proof;
* the instance `fiberMapComp_isClosedImmersion` (StacksFrontier/AlgebraicGeometry/MoreMorphisms/NowhereDenseFibres/FibrePoints.lean:113) subsumes
  `fiberCompMap_isClosedImmersion`, and is global there, so it needs no local attribute here.

Only the integrality lemma below has no public twin: `StacksFrontier/AlgebraicGeometry/MoreMorphisms/NowhereDenseFibres/FibrePoints.lean` carries the closed- and
open-immersion cases and no `IsIntegralHom` one. It is kept, restated for the canonical map. -/
private lemma fiberMapComp_isIntegralHom {T X S : Scheme.{u}} (i : T ⟶ X) [IsFinite i]
    (f : X ⟶ S) (s : S) : IsIntegralHom (Scheme.Hom.fiberMapComp i f s) := by
  have hsnd : IsFinite (pullback.snd i (f.fiberι s)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback i (f.fiberι s)) ‹IsFinite i›
  have hfin : IsFinite ((pullbackRightPullbackFstIso f (S.fromSpecResidueField s) i).inv ≫
      pullback.snd i (f.fiberι s)) :=
    MorphismProperty.IsStableUnderComposition.comp_mem _ _ inferInstance hsnd
  exact ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mp hfin).1

attribute [local instance] fiberMapComp_isIntegralHom

/-! ### Stacks 05H6 -/

/-- **Stacks Project, Tag 05H6.** A finite-type quasi-coherent module supported at a point of a
fibre admits a one-step dévissage there after elementary étale neighbourhoods of the point and
of its image. -/
@[stacks 05H6]
theorem exists_etaleNeighborhood_oneStepDevissageAt {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (x : X)
    (hx : f.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)) :
    ∃ (U : EtaleNeighborhood X x) (V : EtaleNeighborhood S (f x)) (h : U.scheme ⟶ V.scheme),
      U.IsElementary ∧ V.IsElementary ∧ (U.toBase ≫ f = h ≫ V.toBase) ∧
        (h U.point = V.point) ∧
        ∃ (hft : LocallyOfFiniteType h)
          (hq : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent)
          (hf : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType),
          letI : LocallyOfFiniteType h := hft
          letI : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent := hq
          letI : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType := hf
          Nonempty (OneStepDevissageAt h
            ((Scheme.Modules.pullback U.toBase).obj F) U.point) := by
  classical
  obtain ⟨D⟩ := exists_elementaryDevissage f F x hx
  have hpoint : D.toBase D.U.point = D.V.point := by
    calc
      D.toBase D.U.point = D.toBase (D.i D.z) := by rw [D.point_closed]
      _ = D.h (D.π D.z) := by
        simpa using congrArg (fun k : D.Z ⟶ D.V.scheme => k D.z) D.commutes_closed
      _ = D.V.point := D.point_base
  refine ⟨D.U, D.V, D.toBase, D.elementary_U, D.elementary_V, D.commutes_base, hpoint, ?_⟩
  have : LocallyOfFiniteType (D.toBase ≫ D.V.toBase) := by
    rw [← D.commutes_base]
    infer_instance
  have hft : LocallyOfFiniteType D.toBase := locallyOfFiniteType_of_comp D.toBase D.V.toBase
  have hq : ((Scheme.Modules.pullback D.U.toBase).obj F).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ D.U.toBase.toLRSHom.toShHom F ‹_›
  have hf : ((Scheme.Modules.pullback D.U.toBase).obj F).IsFiniteType :=
    @SheafOfModules.pullback_isFiniteType _ _ D.U.toBase.toLRSHom.toShHom F ‹_›
  refine ⟨hft, hq, hf, ?_⟩
  have hGI : GeometricallyIntegral D.h :=
    (GeometricallyIntegral.iff_geometricallyIntegral_fiber D.h).2 D.integral_fibers
  have : GeometricallyIrreducible D.h := inferInstance
  let q := D.toBase D.U.point
  have hbase : D.V.toBase q = f x := by
    have hsq : f (D.U.toBase D.U.point) = D.V.toBase (D.toBase D.U.point) := by
      simpa only [← Scheme.Hom.comp_apply] using
        congrArg (fun k : D.U.scheme ⟶ S => k D.U.point) D.commutes_base
    exact hsq.symm.trans (congrArg f D.U.map_point)
  -- the comparison morphism of fibres across the étale square
  let φ₀ := fiberMap D.toBase D.U.toBase D.V.toBase f D.commutes_base q
  let φ := φ₀ ≫ (fiberCongr f hbase).hom
  have : Etale φ₀ := etale_fiberMap D.toBase D.U.toBase D.V.toBase f D.commutes_base q
  have : Etale φ := by
    dsimp [φ]
    infer_instance
  have hφcomp : φ ≫ f.fiberι (f x) = D.toBase.fiberι q ≫ D.U.toBase := by
    dsimp [φ, φ₀]
    rw [Category.assoc, fiberCongr_hom_fiberι]
    simp only [fiberMap, Scheme.Hom.fiberι, Scheme.Hom.fiber, Limits.pullback.map,
      Limits.pullback.lift_fst]
  have oldFT : ((Scheme.Modules.pullback (f.fiberι (f x))).obj F).IsFiniteType :=
    @SheafOfModules.pullback_isFiniteType _ _ (f.fiberι (f x)).toLRSHom.toShHom F ‹_›
  have newFT : ((Scheme.Modules.pullback (D.toBase.fiberι q)).obj
      ((Scheme.Modules.pullback D.U.toBase).obj F)).IsFiniteType :=
    @SheafOfModules.pullback_isFiniteType _ _ (D.toBase.fiberι q).toLRSHom.toShHom
      ((Scheme.Modules.pullback D.U.toBase).obj F) hf
  let A : Set (f.fiber (f x)) :=
    SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)
  let B : Set (D.toBase.fiber q) :=
    SheafOfModules.supp ((Scheme.Modules.pullback (D.toBase.fiberι q)).obj
      ((Scheme.Modules.pullback D.U.toBase).obj F))
  have hAclosed : IsClosed A := SheafOfModules.isClosed_supp _
  have hAset : A = (f.fiberι (f x) : f.fiber (f x) → X) ⁻¹' SheafOfModules.supp F :=
    Stacks.Modules.supp_pullback (f.fiberι (f x)) F
  have hBset : B = (D.toBase.fiberι q : D.toBase.fiber q → D.U.scheme) ⁻¹'
      ((D.U.toBase : D.U.scheme → X) ⁻¹' SheafOfModules.supp F) := by
    dsimp only [B]
    rw [Stacks.Modules.supp_pullback, Stacks.Modules.supp_pullback]
  have hAB : B = (φ : D.toBase.fiber q → f.fiber (f x)) ⁻¹' A := by
    rw [hBset, hAset]
    ext z
    simp only [Set.mem_preimage]
    have hmap : f.fiberι (f x) (φ z) = D.U.toBase (D.toBase.fiberι q z) := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun k : D.toBase.fiber q ⟶ X => k z) hφcomp
    rw [hmap]
  let p := D.toBase.asFiber D.U.point
  have hxF : x ∈ SheafOfModules.supp F := (mem_supp_fiber_iff_mem_supp f F x).1 hx
  have hpB : p ∈ B := by
    refine (mem_supp_fiber_iff_mem_supp D.toBase _ D.U.point).2 ?_
    rw [Stacks.Modules.supp_pullback]
    show D.U.toBase D.U.point ∈ SheafOfModules.supp F
    rw [D.U.map_point]
    exact hxF
  have hφpoint : φ p = f.asFiber x := by
    apply (f.fiberι (f x)).isEmbedding.injective
    calc
      f.fiberι (f x) (φ p) = (φ ≫ f.fiberι (f x)) p := by simp
      _ = (D.toBase.fiberι q ≫ D.U.toBase) p := by rw [hφcomp]
      _ = D.U.toBase (D.toBase.fiberι q p) := by simp
      _ = D.U.toBase D.U.point := by rw [Scheme.Hom.fiberι_asFiber]
      _ = x := D.U.map_point
      _ = f.fiberι (f x) (f.asFiber x) := by simp
  have hpPre : p ∈ (φ : D.toBase.fiber q → f.fiber (f x)) ⁻¹' A := by rwa [← hAB]
  have hpA : φ p ∈ A := hpPre
  have hlocal := topologicalKrullDimAt_preimage_eq_of_etale φ A hAclosed p hpA
  have hlocalDim : topologicalKrullDimAt B ⟨p, hpB⟩ = (D.n : WithBot ℕ∞) := by
    calc
      topologicalKrullDimAt B ⟨p, hpB⟩ =
          topologicalKrullDimAt ((φ : D.toBase.fiber q → f.fiber (f x)) ⁻¹' A) ⟨p, hpPre⟩ :=
        topologicalKrullDimAt_of_eq_set hAB p hpB hpPre
      _ = topologicalKrullDimAt A ⟨φ p, hpA⟩ := hlocal
      _ = topologicalKrullDimAt A ⟨f.asFiber x, hx⟩ :=
        congrArg (topologicalKrullDimAt A) (Subtype.ext hφpoint : (⟨φ p, hpA⟩ : A) = _)
      _ = (D.n : WithBot ℕ∞) := D.dimension
  have hFiberDim : ∀ t : D.V.scheme,
      topologicalKrullDim (D.h.fiber t) = (D.n : WithBot ℕ∞) := by
    let : SmoothOfRelativeDimension D.n D.h := D.smooth
    exact fun t => topologicalKrullDim_fiber_eq_of_smoothOfRelativeDimension D.n D.h
      D.integral_fibers t
  -- the dimension of the support of the pulled-back module on the distinguished fibre
  have hB_le : topologicalKrullDim B ≤ (D.n : WithBot ℕ∞) := by
    let k : D.Z ⟶ D.V.scheme := D.π ≫ D.h
    have hcommi : D.i ≫ D.toBase = k := D.commutes_closed
    let : IsClosedImmersion D.i := D.closedImmersion
    let e : (D.i ≫ D.toBase).fiber q ≅ k.fiber q := fiberCongrHom hcommi q
    let j : k.fiber q ⟶ D.toBase.fiber q := e.inv ≫ Scheme.Hom.fiberMapComp D.i D.toBase q
    have hjcomp : j ≫ D.toBase.fiberι q = k.fiberι q ≫ D.i := by
      calc
        j ≫ D.toBase.fiberι q = e.inv ≫ ((D.i ≫ D.toBase).fiberι q ≫ D.i) := by
          simp [j, Scheme.Hom.fiberMapComp_fiberι, Category.assoc]
        _ = k.fiberι q ≫ D.i := by
          rw [← Category.assoc, fiberCongrHom_inv_fiberι hcommi q]
    have hBsubset : B ⊆ Set.range (j : k.fiber q → D.toBase.fiber q) := by
      intro u hu
      have huBase : D.toBase.fiberι q u ∈
          (D.U.toBase : D.U.scheme → X) ⁻¹' SheafOfModules.supp F := by
        rw [hBset] at hu
        exact hu
      have huF : D.toBase.fiberι q u ∈
          SheafOfModules.supp ((Scheme.Modules.pullback D.U.toBase).obj F) := by
        rw [Stacks.Modules.supp_pullback]
        exact huBase
      have huPush : D.toBase.fiberι q u ∈
          SheafOfModules.supp ((Scheme.Modules.pushforward D.i).obj D.G) := by
        rw [SheafOfModules.supp_eq_of_iso D.sheafIso]
        exact huF
      obtain ⟨z, hz⟩ := supp_pushforward_subset_range D.i D.G huPush
      have hzq : k z = q := by
        calc
          k z = D.toBase (D.i z) := by
            show D.h (D.π z) = D.toBase (D.i z)
            simpa only [Scheme.Hom.comp_apply] using
              (congrArg (fun m : D.Z ⟶ D.V.scheme => m z) D.commutes_closed).symm
          _ = D.toBase (D.toBase.fiberι q u) := by rw [hz]
          _ = q := (D.toBase.fiberHomeo q u).property
      let v : k.fiber q := (k.fiberHomeo q).symm ⟨z, by simp [hzq]⟩
      refine ⟨v, (D.toBase.fiberι q).isEmbedding.injective ?_⟩
      calc
        D.toBase.fiberι q (j v) = D.i (k.fiberι q v) := by
          simpa only [Scheme.Hom.comp_apply] using
            congrArg (fun m : k.fiber q ⟶ D.U.scheme => m v) hjcomp
        _ = D.i z := congrArg D.i (k.fiberι_fiberHomeo_symm q ⟨z, by simp [hzq]⟩)
        _ = D.toBase.fiberι q u := hz
    have hdimRange : topologicalKrullDim (Set.range (j : k.fiber q → D.toBase.fiber q)) ≤
        topologicalKrullDim (k.fiber q) :=
      (IsHomeomorph.topologicalKrullDim_eq _ j.isEmbedding.toHomeomorph.isHomeomorph).symm.le
    have hdimB : topologicalKrullDim B ≤
        topologicalKrullDim (Set.range (j : k.fiber q → D.toBase.fiber q)) := by
      let ι₀ : B → Set.range (j : k.fiber q → D.toBase.fiber q) :=
        fun z => ⟨z.1, hBsubset z.2⟩
      have hind : Topology.IsInducing ι₀ := by
        apply Topology.IsInducing.subtypeVal.of_comp_iff.mp
        convert Topology.IsInducing.subtypeVal (t := B) using 1
        funext z
        rfl
      exact hind.topologicalKrullDim_le
    have hdimFinite : topologicalKrullDim (k.fiber q) ≤
        topologicalKrullDim (D.h.fiber q) := by
      let : IsFinite D.π := D.finite_π
      exact topologicalKrullDim_le_of_isIntegralHom (Scheme.Hom.fiberMapComp D.π D.h q)
    exact hdimB.trans (hdimRange.trans (hdimFinite.trans (le_of_eq (hFiberDim q))))
  have hB_ge : (D.n : WithBot ℕ∞) ≤ topologicalKrullDim B := by
    rw [topologicalKrullDim_eq_iSup_localKrullDim]
    calc
      (D.n : WithBot ℕ∞) = localKrullDim B ⟨p, hpB⟩ := by
        rw [← topologicalKrullDimAt_eq_localKrullDim]
        exact hlocalDim.symm
      _ ≤ ⨆ z : B, localKrullDim B z := le_iSup _ _
  have hBdim : topologicalKrullDim B = (D.n : WithBot ℕ∞) := le_antisymm hB_le hB_ge
  refine ⟨{
    toOneStepDevissage :=
      { Z := D.Z
        Y := D.Y
        i := D.i
        π := D.π
        g := D.h
        G := D.G
        quasi_coherent_G := D.quasicoherent_G
        finite_type_G := D.finiteType_G
        over_base := D.commutes_closed
        affine_X := D.affine_U
        affine_S := D.affine_V
        affine_Z := D.affine_Z
        affine_Y := D.affine_Y
        closed_immersion := D.closedImmersion
        finite_presentation := D.finitePresentation
        module_iso := D.sheafIso.symm
        finite := D.finite_π
        smooth := D.smooth.smooth
        geometrically_irreducible := inferInstance
        fiber_dimension := by
          intro t
          rw [hBdim]
          exact hFiberDim t }
    mem_fiber_support := hpB
    dimension := hlocalDim.trans hBdim.symm
    z := D.z
    y := D.π D.z
    i_z := D.point_closed
    π_z := rfl
    g_y := D.point_base.trans hpoint.symm
    fiber_eq_singleton := by
      ext z'
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using D.singleton_fiber z'
    residueField_purelyTranscendental := by
      let e := (D.V.scheme.residueFieldCongr hpoint).commRingCatIsoToRingEquiv
      let oldMap := ((D.V.scheme.residueFieldCongr D.point_base).inv ≫
        D.h.residueFieldMap (D.π D.z)).hom
      let newMap := ((D.V.scheme.residueFieldCongr
        (D.point_base.trans hpoint.symm)).inv ≫ D.h.residueFieldMap (D.π D.z)).hom
      have hcong : (D.V.scheme.residueFieldCongr hpoint).hom ≫
          (D.V.scheme.residueFieldCongr D.point_base).inv =
          (D.V.scheme.residueFieldCongr (D.point_base.trans hpoint.symm)).inv := by
        rw [Scheme.residueFieldCongr_inv, Scheme.residueFieldCongr_inv,
          Scheme.residueFieldCongr_trans_hom]
      have hcongRing :
          (D.V.scheme.residueFieldCongr D.point_base).inv.hom.comp
            (D.V.scheme.residueFieldCongr hpoint).hom.hom =
          (D.V.scheme.residueFieldCongr (D.point_base.trans hpoint.symm)).inv.hom := by
        show CommRingCat.Hom.hom ((D.V.scheme.residueFieldCongr hpoint).hom ≫
          (D.V.scheme.residueFieldCongr D.point_base).inv) = _
        rw [hcong]
      have hmap : newMap = oldMap.comp e.toRingHom := by
        show (D.h.residueFieldMap (D.π D.z)).hom.comp
            (D.V.scheme.residueFieldCongr (D.point_base.trans hpoint.symm)).inv.hom =
          ((D.h.residueFieldMap (D.π D.z)).hom.comp
            (D.V.scheme.residueFieldCongr D.point_base).inv.hom).comp
              (D.V.scheme.residueFieldCongr hpoint).hom.hom
        rw [← hcongRing]
        rfl
      let : Algebra (D.V.scheme.residueField D.V.point) (D.Y.residueField (D.π D.z)) :=
        oldMap.toAlgebra
      let : Algebra (D.V.scheme.residueField q) (D.Y.residueField (D.π D.z)) :=
        newMap.toAlgebra
      exact Stacks.Flatness.purelyTranscendental_of_ringEquiv_base e
        (fun a => congrArg (fun k : _ →+* _ => k a) hmap) D.pureTranscendental
  }⟩

/-! ### The support hypothesis of Stacks 05H6 is necessary -/

/-- A one-step dévissage of `F/X/S` at `x` exists only at a point of the support of `F`: the
point of the fibre determined by `x` lies in the support of the module on the fibre, which is
condition (1) of Tag 05H5 being well posed. -/
theorem OneStepDevissageAt.mem_supp {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    {F : X.Modules} [F.IsQuasicoherent] [F.IsFiniteType] {x : X}
    (D : OneStepDevissageAt f F x) : x ∈ SheafOfModules.supp F :=
  (mem_supp_fiber_iff_mem_supp f F x).1 D.mem_fiber_support

/-- There is no one-step dévissage of `F/X/S` over `s` when the restriction of `F` to the fibre
over `s` has empty support. Indeed condition (5) of Tag 05H4 asks the fibres of the smooth
morphism `Y → S` to be geometrically irreducible of dimension `dim(Supp(F_s))`, which is `-∞`
for an empty support, whereas an irreducible space is nonempty and so has dimension `≥ 0`.

Together with `AlgebraicGeometry.OneStepDevissageAt.mem_supp` this is why Tag 05H6 has nothing
to say at a point outside the support of the module on the fibre. -/
theorem isEmpty_oneStepDevissage_of_supp_eq_empty {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
    (hF : SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F) = ∅) :
    IsEmpty (OneStepDevissage f F s) := by
  refine ⟨fun D ↦ ?_⟩
  have := D.geometrically_irreducible
  have hbot : topologicalKrullDim (D.g.fiber s) = ⊥ := by
    rw [D.fiber_dimension s, topologicalKrullDim_eq_bot_iff_isEmpty]
    exact Set.isEmpty_coe_sort.mpr hF
  exact not_isEmpty_of_nonempty (D.g.fiber s) ((topologicalKrullDim_eq_bot_iff_isEmpty _).mp hbot)

/-- **Stacks Project, Tag 05H6**, in sharp form. The elementary étale neighbourhoods of `(X, x)`
and of `(S, f x)` over which the pullback of `F` acquires a one-step dévissage at the
distinguished point exist exactly when `x` lies in the support of the restriction of `F` to the
fibre of `f` through `x`.

The forward implication is the converse of the source's lemma; it holds because a one-step
dévissage at a point records that the point lies in the support of the module on its fibre
(`AlgebraicGeometry.OneStepDevissageAt.mem_supp`), and the support of the pullback of `F` to an
étale neighbourhood is the inverse image of the support of `F`. -/
@[stacks 05H6]
theorem exists_etaleNeighborhood_oneStepDevissageAt_iff_mem_fiber_supp {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (x : X) :
    (∃ (U : EtaleNeighborhood X x) (V : EtaleNeighborhood S (f x)) (h : U.scheme ⟶ V.scheme),
      U.IsElementary ∧ V.IsElementary ∧ (U.toBase ≫ f = h ≫ V.toBase) ∧
        (h U.point = V.point) ∧
        ∃ (hft : LocallyOfFiniteType h)
          (hq : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent)
          (hf : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType),
          letI : LocallyOfFiniteType h := hft
          letI : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent := hq
          letI : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType := hf
          Nonempty (OneStepDevissageAt h
            ((Scheme.Modules.pullback U.toBase).obj F) U.point)) ↔
      f.asFiber x ∈
        SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) := by
  refine ⟨?_, exists_etaleNeighborhood_oneStepDevissageAt f F x⟩
  rintro ⟨U, _V, _h, _hU, _hV, _hsq, _hpt, _, _, _, ⟨D⟩⟩
  have hU : x ∈ SheafOfModules.supp F := by
    have := D.mem_supp
    rwa [Stacks.Modules.supp_pullback, Set.mem_preimage, U.map_point] at this
  exact (mem_supp_fiber_iff_mem_supp f F x).2 hU

end AlgebraicGeometry

end
