module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TensorTotalComplex
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chern classes of a derived tensor product of perfect objects

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `E`, `F` be perfect objects of `D(𝒪_X)` whose Chern classes are
defined (Stacks 0F9E). Stacks 0FAG says that, writing `r(E) = P_0(E) ∈ A^0(X)` for the rank,

  `c₁(E ⊗^L F) = r(E) c₁(F) + r(F) c₁(E)`,

  `c₂(E ⊗^L F) = r(E) c₂(F) + r(F) c₂(E) + C(r(E), 2) c₁(F)² + (r(E) r(F) - 1) c₁(F) c₁(E) +
    C(r(F), 2) c₁(E)²`,

  `P_p(E ⊗^L F) = ∑_{p₁ + p₂ = p} C(p, p₁) P_{p₁}(E) P_{p₂}(F)`,

the last one giving `ch(E ⊗^L F) = ch(E) ch(F)` after division by `p!`.

The proof is the first one of the source. Choose envelope presentations `(f : Y ⟶ X, 𝓔^•)` of `E`
and `(f' : Y' ⟶ X, 𝓕^•)` of `F`. On the envelope `Y ×_X Y' ⟶ X` the derived pullback of
`E ⊗^L F` is `Lf^*E ⊗^L Lf^*F` (Stacks 079U), hence is represented by the total tensor complex
`Tot(𝓔^• ⊗ 𝓕^•)` of the pulled back complexes, the second one being K-flat. That complex is
again locally bounded with finite locally free terms, so the Chern classes of `E ⊗^L F` are
defined, and its classes are computed from those of the two factors by the formal computations
of `StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TensorTotalComplex`, which rest on
Stacks 0FA6 and Stacks 0F9D for finite locally free modules. Restriction along an envelope is
injective, so the formulas descend to `X`.

## Main definitions

* `Stacks.Chow.EnvelopePresentation.tensor` — the tensor product of two envelope presentations,
  an envelope presentation of `E ⊗^L F`; `Stacks.Chow.EnvelopePresentation.tensorLeft` and
  `Stacks.Chow.EnvelopePresentation.tensorRight` present the two factors on the same envelope.
* `Stacks.Chow.TotalChowClass.ofLocallyConstant` — the class in `A^0(X)` of a locally constant
  integer-valued function on `X`.
* `Stacks.Chow.perfectRank` — the derived-fibre Euler characteristic of a perfect object, as a
  locally constant function.

## Main results

* `Stacks.Chow.derivedTensorQIso` — the derived tensor product with a locally bounded complex of
  finite locally free modules is the total tensor complex.
* `Stacks.Chow.hasDefinedChernClasses_derivedTensor` — the Chern classes of `E ⊗^L F` are
  defined.
* `Stacks.Chow.perfectPowerSum_zero_eq_ofLocallyConstant` — the rank `r(E) = P_0(E)` is the
  class of the locally constant function `x ↦ χ(E ⊗^L κ(x))`.
* `Stacks.Chow.perfectChernClass_derivedTensor_one` — **Stacks 0FAG**, the formula for `c₁`.
* `Stacks.Chow.perfectChernClass_derivedTensor_two` — **Stacks 0FAG**, the formula for `c₂`;
  `Stacks.Chow.perfectChernClass_derivedTensor_two_of_constantRank` is its form for constant
  ranks.
* `Stacks.Chow.perfectPowerSum_derivedTensor` — **Stacks 0FAG**, the formula for `P_p`.

## Implementation notes

The rank `r(E) = P_0(E)` need not be constant. The binomial coefficient `C(r(E), 2)` of the
source is therefore read as the class in `A^0(X)` of the locally constant function
`x ↦ C(χ(x), 2)`, where `χ(x)` is the Euler characteristic of the derived fibre of `E` at `x`,
the function of which `r(E)` itself is the class
(`Stacks.Chow.perfectPowerSum_zero_eq_ofLocallyConstant`). On the open and closed subscheme
where `E` has constant rank `r` these are the integers `r` and `C(r, 2)`; this is the
decomposition of `X` into the parts where the rank is constant used in the remark after
Stacks 0FA6. No division by `2` is involved: `A^*(X)` may have `2`-torsion.

The classes are those of the ring `∏_p A^p(X)` of total Chow cohomology classes, which is not
known to be commutative; every product is written in the order of the source. The formulas for
`c₁` and `P_p` hold for all objects whose Chern classes are defined; perfectness is used only to
make sense of the locally constant rank in the formula for `c₂`. The proof of definedness of the
Chern classes of the tensor product, `Stacks.Chow.hasDefinedChernClasses_derivedTensor`, is an
argument of the statements only because the classes are indexed by it.

The source's "and so on for higher Chern classes" is not a precise assertion and is not
formalized.

## References

* [Stacks Project, Tag 0FAG](https://stacks.math.columbia.edu/tag/0FAG)
* [Stacks Project, Tag 0FA6](https://stacks.math.columbia.edu/tag/0FA6)
* [Stacks Project, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Finset
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The tensor product of two envelope presentations -/

section Presentation

variable {X : Scheme.{u}}

/-- **The derived tensor product of two complexes, the second one locally bounded with finite
locally free terms**, is their total tensor complex: such a complex is K-flat. -/
def derivedTensorQIso (P Q : CochainComplex X.Modules ℤ)
    (hQ : IsLocallyBoundedFiniteLocallyFree Q) :
    ((derivedTensorProductFunctor X.sheaf).obj (DerivedCategory.Q.obj P)).obj
        (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj (tensorTotal P Q) :=
  (canonicalDerivedTensorProduct X.sheaf).comparisonRight P Q
    (Stacks.BlowUpComplexes.kFlatComplex_of_isLocallyBoundedFiniteLocallyFree Q hQ)

/-- **Derived pullback commutes with derived tensor products**, Stacks 079U:
`Lf^*(E ⊗^L F) ≅ Lf^*E ⊗^L Lf^*F`. -/
def derivedPullbackDerivedTensorIso {Y : Scheme.{u}} (f : Y ⟶ X)
    (E F : DerivedCategory X.Modules) :
    (derivedPullback f.toLRSHom.toShHom).obj (((derivedTensorProductFunctor X.sheaf).obj E).obj F) ≅
      ((derivedTensorProductFunctor Y.sheaf).obj ((derivedPullback f.toLRSHom.toShHom).obj E)).obj
        ((derivedPullback f.toLRSHom.toShHom).obj F) :=
  (Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f.toLRSHom.toShHom).app (E, F)

/-- The derived tensor product of isomorphisms. -/
def derivedTensorMapIso {E E' F F' : DerivedCategory X.Modules} (e : E ≅ E') (e' : F ≅ F') :
    ((derivedTensorProductFunctor X.sheaf).obj E).obj F ≅
      ((derivedTensorProductFunctor X.sheaf).obj E').obj F' :=
  ((derivedTensorProductFunctor X.sheaf).mapIso e).app F ≪≫
    ((derivedTensorProductFunctor X.sheaf).obj E').mapIso e'

variable {E F : DerivedCategory X.Modules}

/-- **The tensor product of two envelope presentations.** For presentations `(f, 𝓔^•)` of `E`
and `(f', 𝓕^•)` of `F`, the envelope `Y ×_X Y' ⟶ X` and the total tensor complex of the
pullbacks of `𝓔^•` and `𝓕^•` to `Y ×_X Y'` present `E ⊗^L F`. -/
def EnvelopePresentation.tensor (H : EnvelopePresentation E) (H' : EnvelopePresentation F) :
    EnvelopePresentation (((derivedTensorProductFunctor X.sheaf).obj E).obj F) where
  Y := pullback H.f H'.f
  f := pullback.fst H.f H'.f ≫ H.f
  envelope := isEnvelope_comp H.f _ H.envelope
    (isEnvelope_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback H.f H'.f).flip
      H'.envelope)
  P := tensorTotal (pullbackComplex (pullback.fst H.f H'.f) H.P)
    (pullbackComplex (pullback.snd H.f H'.f) H'.P)
  locallyBounded := isLocallyBoundedFiniteLocallyFree_tensorTotal
    (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ H.P H.locallyBounded)
    (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ H'.P H'.locallyBounded)
  representation := ⟨derivedPullbackDerivedTensorIso _ E F ≪≫
    derivedTensorMapIso (H.pullbackRepresentation (pullback.fst H.f H'.f))
      ((eqToIso (Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq
        (congrArg (fun m : pullback H.f H'.f ⟶ X ↦ m.toLRSHom.toShHom)
          (pullback.condition (f := H.f) (g := H'.f))))).app F ≪≫
        H'.pullbackRepresentation (pullback.snd H.f H'.f)) ≪≫
    derivedTensorQIso _ _
      (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ H'.P
        H'.locallyBounded)⟩

/-- The envelope of the tensor product of two presentations is proper, hence locally of finite
type. The instance `Stacks.Chow.EnvelopePresentation.locallyOfFiniteType_f` for an arbitrary
presentation does not apply to it by unification: the derived category of `X` in which `E ⊗^L F`
lives is presented through the ringed site of `X`. -/
instance EnvelopePresentation.isProper_tensor_f (H : EnvelopePresentation E)
    (H' : EnvelopePresentation F) : IsProper (H.tensor H').f :=
  (H.tensor H').envelope.isProper

/-- **The Chern classes of a derived tensor product are defined** when those of the factors are:
tensor two envelope presentations. -/
theorem hasDefinedChernClasses_derivedTensor (hE : HasDefinedChernClasses E)
    (hF : HasDefinedChernClasses F) :
    HasDefinedChernClasses (((derivedTensorProductFunctor X.sheaf).obj E).obj F) :=
  ⟨hE.some.tensor hF.some⟩

/-- **The first factor on the envelope of a tensor product of presentations**: on
`Y ×_X Y' ⟶ X`, the pullback of `𝓔^•` presents `E`. -/
def EnvelopePresentation.tensorLeft (H : EnvelopePresentation E) (H' : EnvelopePresentation F) :
    EnvelopePresentation E where
  Y := pullback H.f H'.f
  f := pullback.fst H.f H'.f ≫ H.f
  envelope := (H.tensor H').envelope
  P := pullbackComplex (pullback.fst H.f H'.f) H.P
  locallyBounded :=
    Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ H.P H.locallyBounded
  representation := ⟨H.pullbackRepresentation (pullback.fst H.f H'.f)⟩

/-- **The second factor on the envelope of a tensor product of presentations**: on
`Y ×_X Y' ⟶ X`, the pullback of `𝓕^•` presents `F`. -/
def EnvelopePresentation.tensorRight (H : EnvelopePresentation E) (H' : EnvelopePresentation F) :
    EnvelopePresentation F where
  Y := pullback H.f H'.f
  f := pullback.fst H.f H'.f ≫ H.f
  envelope := (H.tensor H').envelope
  P := pullbackComplex (pullback.snd H.f H'.f) H'.P
  locallyBounded :=
    Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ H'.P H'.locallyBounded
  representation := ⟨(eqToIso (Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq
      (congrArg (fun m : pullback H.f H'.f ⟶ X ↦ m.toLRSHom.toShHom)
        (pullback.condition (f := H.f) (g := H'.f))))).app F ≪≫
    H'.pullbackRepresentation (pullback.snd H.f H'.f)⟩

end Presentation

/-! ### The class of a locally constant integer-valued function -/

namespace TotalChowClass

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-- The level sets `{x | n(x) = k}` of a locally constant function, as open subschemes, indexed
in the universe of the scheme. -/
def levelSets (n : LocallyConstant X ℤ) : ULift.{u} ℤ → X.Opens :=
  fun k ↦ ⟨n ⁻¹' {k.down}, n.isLocallyConstant.isOpen_fiber k.down⟩

/-- A point lies in the level set of its value. -/
theorem mem_levelSets {n : LocallyConstant X ℤ} {k : ULift.{u} ℤ} {x : X} :
    x ∈ levelSets n k ↔ n x = k.down :=
  Iff.rfl

/-- The level sets of a locally constant function decompose the scheme into open and closed
subschemes. -/
theorem isClopenDecomposition_levelSets (n : LocallyConstant X ℤ) :
    IsClopenDecomposition (levelSets n) where
  disjoint i j hij := by
    rw [disjoint_iff]
    refine TopologicalSpace.Opens.ext (Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ hij ?_)
    exact ULift.ext _ _ (hx.1.symm.trans hx.2)
  iSup_eq_top := top_unique fun x _ ↦
    TopologicalSpace.Opens.mem_iSup.2 ⟨ULift.up (n x), rfl⟩

variable (C sX) in
/-- **The class of a locally constant integer-valued function** `n` on `X`: the class of
`A^0(X)` restricting to the integer `k` on the open and closed subscheme where `n = k`. -/
def ofLocallyConstant (n : LocallyConstant X ℤ) : TotalChowClass C sX :=
  glue (isClopenDecomposition_levelSets n) fun k ↦ ((k.down : ℤ) : TotalChowClass C _)

/-- **Restriction of the class of a locally constant function.** Along `h : Y ⟶ X` on which `n`
takes the constant value `k`, the class of `n` restricts to `k`. -/
theorem res_ofLocallyConstant {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
    (h : Y ⟶ X) [LocallyOfFiniteType h] (hs : h ≫ sX = sY) (n : LocallyConstant X ℤ) (k : ℤ)
    (hk : ∀ y, n (h.base y) = k) :
    res h hs (ofLocallyConstant C sX n) = (k : TotalChowClass C sY) := by
  have hU := isClopenDecomposition_levelSets n
  refine eq_of_res_eq (hU.preimage h) fun j ↦ ?_
  rcases isEmpty_or_nonempty (h ⁻¹ᵁ levelSets n j : Scheme.{u}) with he | ⟨⟨y, hy⟩⟩
  · exact (subsingleton_of_isEmpty _).elim _ _
  have ha : ∀ j, h ⁻¹ᵁ levelSets n j ≤ h ⁻¹ᵁ levelSets n (id j) := fun _ ↦ le_rfl
  have hfac : (h ⁻¹ᵁ levelSets n j).ι ≫ h =
      pieceMap h (fun j ↦ h ⁻¹ᵁ levelSets n j) (levelSets n) id ha j ≫ (levelSets n j).ι :=
    (pieceMap_comp_ι h _ _ id ha j).symm
  have hpm : pieceMap h (fun j ↦ h ⁻¹ᵁ levelSets n j) (levelSets n) id ha j ≫
      ((levelSets n j).ι ≫ sX) = (h ⁻¹ᵁ levelSets n j).ι ≫ sY := by
    rw [← Category.assoc, ← hfac, Category.assoc, hs]
  have hj : j.down = k := (mem_levelSets.1 hy).symm.trans (hk y)
  rw [res_res, res_congr hfac _ (by rw [Category.assoc, hpm]),
    ← res_res (levelSets n j).ι rfl _ hpm, ofLocallyConstant, res_glue hU, map_intCast,
    map_intCast, hj]

/-- The class of a constant function is the integer. -/
theorem ofLocallyConstant_const (k : ℤ) :
    ofLocallyConstant C sX (LocallyConstant.const X k) = (k : TotalChowClass C sX) := by
  rw [← res_id (ofLocallyConstant C sX _), res_ofLocallyConstant (𝟙 X) _ _ k fun _ ↦ rfl]

end TotalChowClass

open TotalChowClass

/-! ### The rank of a perfect object -/

section Rank

variable {X : Scheme.{u}}

/-- **The derived-fibre Euler characteristic along a presentation.** If `Lφ^*E` is represented by
a complex of finite locally free modules of constant ranks `ρ`, the Euler characteristic of the
derived fibre of `E` at the image of every point is the alternating rank `∑ (-1)^a ρ(a)`. -/
theorem chiDerivedFibre_eq_alternatingRank {T : Scheme.{u}} (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) (φ : T ⟶ X)
    (K : CochainComplex T.Modules ℤ) (ρ : ℤ →₀ ℕ)
    (hK : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (K.X n) (ρ n))
    (e : (derivedPullback φ.toLRSHom.toShHom).obj E ≅ DerivedCategory.Q.obj K) (t : T) :
    DerivedFibreBetti.chiDerivedFibre X E hE (φ.base t) = alternatingRank ρ := by
  have hbounded : {i : ℤ | ¬ IsZero (K.X i)}.Finite := by
    refine ρ.support.finite_toSet.subset fun n hn ↦ ?_
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (K.X n) 0 :=
      h0 ▸ hK n
    exact hn (isZero_of_isFiniteLocallyFreeOfRank_zero _)
  refine (congrFun (DerivedFibreBetti.chiDerivedFibre_derivedPullback φ E hE) t).symm.trans ?_
  have hpcK := DerivedFibreBetti.isPseudoCoherent_Q_of_bounded_finiteLocallyFree T K hbounded
    fun i ↦ AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (K.X i)
      (ρ i) (hM := hK i)
  refine (congrFun (DerivedFibreBetti.chiDerivedFibre_congr T _ hpcK e) t).trans ?_
  rw [alternatingRank_eq_finsum]
  exact DerivedFibreBetti.chiDerivedFibre_eq_of_bounded_finiteLocallyFreeOfRank T K hbounded ρ hK
    _ t

/-- The derived-fibre Euler characteristic of a perfect object, as a locally constant
function (Stacks 0BDJ). -/
def perfectRank (E : DerivedCategory X.Modules) (perfect : RingedSpace.IsPerfect.{u, u + 1} E) :
    LocallyConstant X ℤ :=
  ⟨DerivedFibreBetti.chiDerivedFibre X E
      (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E perfect),
    DerivedFibreBetti.isLocallyConstant_chiDerivedFibre X E perfect⟩

/-- The rank function evaluates to the derived-fibre Euler characteristic. -/
theorem perfectRank_apply (E : DerivedCategory X.Modules)
    (perfect : RingedSpace.IsPerfect.{u, u + 1} E) (x : X) :
    perfectRank E perfect x = DerivedFibreBetti.chiDerivedFibre X E
      (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E perfect) x :=
  rfl

end Rank

/-! ### Stacks 0FAG -/

section Main

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {E F : DerivedCategory X.Modules} (hE : HasDefinedChernClasses E) (hF : HasDefinedChernClasses F)
  (hEF : HasDefinedChernClasses (((derivedTensorProductFunctor X.sheaf).obj E).obj F))

/-- **The rank `r(E) = P_0(E)` of a perfect object** is the class of the locally constant
function `x ↦ χ(E ⊗^L κ(x))`, the Euler characteristic of the derived fibre. -/
theorem perfectPowerSum_zero_eq_ofLocallyConstant (perfect : RingedSpace.IsPerfect.{u, u + 1} E) :
    perfectPowerSum C sX hE 0 = ofLocallyConstant C sX (perfectRank E perfect) := by
  set H := hE.some
  refine res_injective_of_isEnvelope H.f H.envelope rfl ?_
  rw [res_perfectPowerSum_eq_powerSumComplex C sX hE H]
  refine TotalChowClass.eq_of_res_eq_of_complexRank₂ C (H.f ≫ sX) H.locallyBounded
    H.locallyBounded fun {T sT _} g _ hs ρ _ hρ _ ↦ ?_
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · exact (TotalChowClass.subsingleton_of_isEmpty sT).elim _ _
  rw [res_powerSumComplex_eq_powerSumComplexBounded C _ H.locallyBounded g hs ρ hρ,
    powerSumComplexBounded_zero, TotalChowClass.res_res,
    res_ofLocallyConstant _ _ _ (alternatingRank ρ) fun t ↦
      chiDerivedFibre_eq_alternatingRank E _ (g ≫ H.f) _ ρ hρ (H.pullbackRepresentation g) t]

/-- **The first Chern class of a derived tensor product.** For objects `E`, `F` of `D(𝒪_X)` whose
Chern classes are defined,

  `c₁(E ⊗^L F) = r(E) c₁(F) + r(F) c₁(E)`

in `A^*(X)`, where `r(E) = P_0(E)` is the rank and `c₁` the degree-one part of the total Chern
class. -/
@[stacks 0FAG "the formula for c_1(E tensor^L F), for objects E, F of D(O_X) whose Chern classes \
are defined; perfectness is not needed.  The rank r(E) is the class P_0(E) = perfectPowerSum C sX \
hE 0 in A^0(X), not assumed constant, and r(E) c_1(F) is the product in the ring TotalChowClass \
C sX of total Chow cohomology classes.  E tensor^L F is the derived tensor product \
derivedTensorProductFunctor of Stacks 06YU"]
theorem perfectChernClass_derivedTensor_one :
    TotalChowClass.homComponent 1 (perfectChernClass C sX hEF) =
      perfectPowerSum C sX hE 0 * TotalChowClass.homComponent 1 (perfectChernClass C sX hF) +
        perfectPowerSum C sX hF 0 * TotalChowClass.homComponent 1 (perfectChernClass C sX hE) := by
  set H₁ := hE.some
  set H₂ := hF.some
  have : LocallyOfFiniteType (pullback.fst H₁.f H₂.f ≫ H₁.f) :=
    EnvelopePresentation.locallyOfFiniteType_f (H₁.tensor H₂)
  refine res_injective_of_isEnvelope (pullback.fst H₁.f H₂.f ≫ H₁.f) (H₁.tensor H₂).envelope rfl
    ?_
  have hT : res (pullback.fst H₁.f H₂.f ≫ H₁.f) rfl (perfectChernClass C sX hEF) =
      complexChern C ((pullback.fst H₁.f H₂.f ≫ H₁.f) ≫ sX) (H₁.tensor H₂).locallyBounded :=
    res_perfectChernClass C sX hEF (H₁.tensor H₂)
  have hL : res (pullback.fst H₁.f H₂.f ≫ H₁.f) rfl (perfectChernClass C sX hE) =
      complexChern C ((pullback.fst H₁.f H₂.f ≫ H₁.f) ≫ sX) (H₁.tensorLeft H₂).locallyBounded :=
    res_perfectChernClass C sX hE (H₁.tensorLeft H₂)
  have hR : res (pullback.fst H₁.f H₂.f ≫ H₁.f) rfl (perfectChernClass C sX hF) =
      complexChern C ((pullback.fst H₁.f H₂.f ≫ H₁.f) ≫ sX) (H₁.tensorRight H₂).locallyBounded :=
    res_perfectChernClass C sX hF (H₁.tensorRight H₂)
  have hL₀ : res (pullback.fst H₁.f H₂.f ≫ H₁.f) rfl (perfectPowerSum C sX hE 0) =
      powerSumComplex C ((pullback.fst H₁.f H₂.f ≫ H₁.f) ≫ sX)
        (H₁.tensorLeft H₂).locallyBounded 0 :=
    res_perfectPowerSum_eq_powerSumComplex C sX hE (H₁.tensorLeft H₂) 0
  have hR₀ : res (pullback.fst H₁.f H₂.f ≫ H₁.f) rfl (perfectPowerSum C sX hF 0) =
      powerSumComplex C ((pullback.fst H₁.f H₂.f ≫ H₁.f) ≫ sX)
        (H₁.tensorRight H₂).locallyBounded 0 :=
    res_perfectPowerSum_eq_powerSumComplex C sX hF (H₁.tensorRight H₂) 0
  rw [TotalChowClass.res_homComponent, hT, map_add, map_mul, map_mul,
    TotalChowClass.res_homComponent, TotalChowClass.res_homComponent, hL, hR, hL₀, hR₀]
  exact homPart_one_complexChern_tensorTotal C ((pullback.fst H₁.f H₂.f ≫ H₁.f) ≫ sX)
    (H₁.tensorLeft H₂).locallyBounded
    (H₁.tensorRight H₂).locallyBounded

/-- **The power sums of a derived tensor product.** For objects `E`, `F` of `D(𝒪_X)` whose Chern
classes are defined and every `p ≥ 0`,

  `P_p(E ⊗^L F) = ∑_{p₁ + p₂ = p} C(p, p₁) P_{p₁}(E) P_{p₂}(F)`

in `A^p(X)`, the power sums `P_0` being the ranks; dividing by `p!` this is
`ch(E ⊗^L F) = ch(E) ch(F)`. -/
@[stacks 0FAG "the precise form P_p(E tensor^L F) = sum over p_1 + p_2 = p of C(p, p_1) \
P_{p_1}(E) P_{p_2}(F) in A^p(X), for every p >= 0, for objects E, F of D(O_X) whose Chern classes \
are defined (perfectness is not needed); P_p is perfectPowerSum of Stacks 0GUD, P_0 being the \
rank, and the products are those of TotalChowClass C sX.  The statement ch(E tensor F) = ch(E) \
ch(F) in A^*(X) tensor Q is the consequence of this identity obtained by dividing by p!, which is \
not stated separately"]
theorem perfectPowerSum_derivedTensor (p : ℕ) :
    perfectPowerSum C sX hEF p =
      ∑ q ∈ antidiagonal p, (p.choose q.1 : ℤ) •
        (perfectPowerSum C sX hE q.1 * perfectPowerSum C sX hF q.2) := by
  set H₁ := hE.some
  set H₂ := hF.some
  have : LocallyOfFiniteType (pullback.fst H₁.f H₂.f ≫ H₁.f) :=
    EnvelopePresentation.locallyOfFiniteType_f (H₁.tensor H₂)
  refine res_injective_of_isEnvelope (pullback.fst H₁.f H₂.f ≫ H₁.f) (H₁.tensor H₂).envelope rfl
    ?_
  have hT : res (pullback.fst H₁.f H₂.f ≫ H₁.f) rfl (perfectPowerSum C sX hEF p) =
      powerSumComplex C ((pullback.fst H₁.f H₂.f ≫ H₁.f) ≫ sX) (H₁.tensor H₂).locallyBounded p :=
    res_perfectPowerSum_eq_powerSumComplex C sX hEF (H₁.tensor H₂) p
  have hL : ∀ q, res (pullback.fst H₁.f H₂.f ≫ H₁.f) rfl (perfectPowerSum C sX hE q) =
      powerSumComplex C ((pullback.fst H₁.f H₂.f ≫ H₁.f) ≫ sX)
        (H₁.tensorLeft H₂).locallyBounded q :=
    res_perfectPowerSum_eq_powerSumComplex C sX hE (H₁.tensorLeft H₂)
  have hR : ∀ q, res (pullback.fst H₁.f H₂.f ≫ H₁.f) rfl (perfectPowerSum C sX hF q) =
      powerSumComplex C ((pullback.fst H₁.f H₂.f ≫ H₁.f) ≫ sX)
        (H₁.tensorRight H₂).locallyBounded q :=
    res_perfectPowerSum_eq_powerSumComplex C sX hF (H₁.tensorRight H₂)
  rw [hT, map_sum]
  simp only [map_zsmul, map_mul, hL, hR]
  exact powerSumComplex_tensorTotal C ((pullback.fst H₁.f H₂.f ≫ H₁.f) ≫ sX)
    (H₁.tensorLeft H₂).locallyBounded
    (H₁.tensorRight H₂).locallyBounded p

/-- **The second Chern class of a derived tensor product.** For perfect objects `E`, `F` of
`D(𝒪_X)` whose Chern classes are defined,

  `c₂(E ⊗^L F) = r(E) c₂(F) + r(F) c₂(E) + C(r(E), 2) c₁(F)² + (r(E) r(F) - 1) c₁(F) c₁(E) +
    C(r(F), 2) c₁(E)²`

in `A^*(X)`, where `r(E) = P_0(E)` is the rank and `C(r(E), 2)` is the class of the locally
constant function `x ↦ C(χ_E(x), 2)`, `χ_E` being the Euler characteristic of the derived fibre
of `E`, whose class is `r(E)` (`Stacks.Chow.perfectPowerSum_zero_eq_ofLocallyConstant`). -/
@[stacks 0FAG "the formula for c_2(E tensor^L F), for perfect objects E, F of D(O_X) whose Chern \
classes are defined, the ranks being arbitrary locally constant functions.  r(E) is the class \
P_0(E) = perfectPowerSum C sX hE 0 in A^0(X); the binomial coefficient C(r(E), 2) is read as the \
class ofLocallyConstant of the locally constant function x |-> Ring.choose (chi_E(x)) 2, chi_E \
the derived-fibre Euler characteristic, whose own class is r(E) by \
perfectPowerSum_zero_eq_ofLocallyConstant; on the open and closed subscheme where E has rank r \
these are the integers r and C(r, 2), as in Remark 0FA7.  The products are those of \
TotalChowClass C sX, written in the order of the source.  The source's 'and so on for higher \
Chern classes' is not a precise assertion and is not formalized"]
theorem perfectChernClass_derivedTensor_two (perfectE : RingedSpace.IsPerfect.{u, u + 1} E)
    (perfectF : RingedSpace.IsPerfect.{u, u + 1} F) :
    TotalChowClass.homComponent 2 (perfectChernClass C sX hEF) =
      perfectPowerSum C sX hE 0 * TotalChowClass.homComponent 2 (perfectChernClass C sX hF) +
        perfectPowerSum C sX hF 0 * TotalChowClass.homComponent 2 (perfectChernClass C sX hE) +
        ofLocallyConstant C sX ((perfectRank E perfectE).map fun k ↦ Ring.choose k 2) *
          TotalChowClass.homComponent 1 (perfectChernClass C sX hF) ^ 2 +
        (perfectPowerSum C sX hE 0 * perfectPowerSum C sX hF 0 - 1) *
          (TotalChowClass.homComponent 1 (perfectChernClass C sX hF) *
            TotalChowClass.homComponent 1 (perfectChernClass C sX hE)) +
        ofLocallyConstant C sX ((perfectRank F perfectF).map fun k ↦ Ring.choose k 2) *
          TotalChowClass.homComponent 1 (perfectChernClass C sX hE) ^ 2 := by
  set H₁ := hE.some
  set H₂ := hF.some
  set f := pullback.fst H₁.f H₂.f ≫ H₁.f
  have : LocallyOfFiniteType f := EnvelopePresentation.locallyOfFiniteType_f (H₁.tensor H₂)
  refine res_injective_of_isEnvelope f (H₁.tensor H₂).envelope rfl ?_
  have hT : res f rfl (perfectChernClass C sX hEF) =
      complexChern C (f ≫ sX) (H₁.tensor H₂).locallyBounded :=
    res_perfectChernClass C sX hEF (H₁.tensor H₂)
  have hL : res f rfl (perfectChernClass C sX hE) =
      complexChern C (f ≫ sX) (H₁.tensorLeft H₂).locallyBounded :=
    res_perfectChernClass C sX hE (H₁.tensorLeft H₂)
  have hR : res f rfl (perfectChernClass C sX hF) =
      complexChern C (f ≫ sX) (H₁.tensorRight H₂).locallyBounded :=
    res_perfectChernClass C sX hF (H₁.tensorRight H₂)
  have hL₀ : res f rfl (perfectPowerSum C sX hE 0) =
      powerSumComplex C (f ≫ sX) (H₁.tensorLeft H₂).locallyBounded 0 :=
    res_perfectPowerSum_eq_powerSumComplex C sX hE (H₁.tensorLeft H₂) 0
  have hR₀ : res f rfl (perfectPowerSum C sX hF 0) =
      powerSumComplex C (f ≫ sX) (H₁.tensorRight H₂).locallyBounded 0 :=
    res_perfectPowerSum_eq_powerSumComplex C sX hF (H₁.tensorRight H₂) 0
  simp only [TotalChowClass.res_homComponent, hT, map_add, map_mul, map_sub, map_one, map_pow, hL,
    hR, hL₀, hR₀]
  refine TotalChowClass.eq_of_res_eq_of_complexRank₂ C (f ≫ sX)
    (H₁.tensorLeft H₂).locallyBounded (H₁.tensorRight H₂).locallyBounded
    fun {T sT _} g _ hs ρ σ hρ hσ ↦ ?_
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · exact (TotalChowClass.subsingleton_of_isEmpty sT).elim _ _
  have hτ := isFiniteLocallyFreeOfRank_pullbackComplex_tensorTotal g _ _ ρ σ hρ hσ
  have hχE : ∀ t, (perfectRank E perfectE).map (fun k ↦ Ring.choose k 2) ((g ≫ f).base t) =
      Ring.choose (alternatingRank ρ) 2 := fun t ↦
    congrArg (fun k ↦ Ring.choose k 2) (chiDerivedFibre_eq_alternatingRank E
      (DerivedFibreBetti.isPseudoCoherent_of_isPerfect E perfectE) (g ≫ f) _ ρ hρ
        ((H₁.tensorLeft H₂).pullbackRepresentation g) t)
  have hχF : ∀ t, (perfectRank F perfectF).map (fun k ↦ Ring.choose k 2) ((g ≫ f).base t) =
      Ring.choose (alternatingRank σ) 2 := fun t ↦
    congrArg (fun k ↦ Ring.choose k 2) (chiDerivedFibre_eq_alternatingRank F
      (DerivedFibreBetti.isPseudoCoherent_of_isPerfect F perfectF) (g ≫ f) _ σ hσ
        ((H₁.tensorRight H₂).pullbackRepresentation g) t)
  refine (TotalChowClass.res_homComponent g hs 2 _).trans ((congrArg (TotalChowClass.homComponent 2)
    (res_complexChern_eq_complexChernBounded C _ _ g hs (tensorRank ρ σ) hτ)).trans
    ((homPart_complexChernBounded_tensorTotal C sT g ρ σ hρ hσ _ hτ).2.trans ?_))
  simp only [map_add, map_mul, map_sub, map_one, map_pow, TotalChowClass.res_homComponent,
    res_complexChern_eq_complexChernBounded C (f ≫ sX) (H₁.tensorLeft H₂).locallyBounded g hs ρ hρ,
    res_complexChern_eq_complexChernBounded C (f ≫ sX) (H₁.tensorRight H₂).locallyBounded g hs σ
      hσ,
    res_powerSumComplex_eq_powerSumComplexBounded C (f ≫ sX) (H₁.tensorLeft H₂).locallyBounded g
      hs ρ hρ,
    res_powerSumComplex_eq_powerSumComplexBounded C (f ≫ sX) (H₁.tensorRight H₂).locallyBounded g
      hs σ hσ, powerSumComplexBounded_zero,
    TotalChowClass.res_res, res_ofLocallyConstant _ _ _ _ hχE, res_ofLocallyConstant _ _ _ _ hχF,
    zsmul_eq_mul, Int.cast_sub, Int.cast_mul, Int.cast_one]

/-- **The second Chern class of a derived tensor product, for constant ranks.** For perfect
objects `E`, `F` of constant ranks `r` and `s` whose Chern classes are defined,

  `c₂(E ⊗^L F) = r c₂(F) + s c₂(E) + C(r, 2) c₁(F)² + (r s - 1) c₁(F) c₁(E) + C(s, 2) c₁(E)²`,

the binomial coefficients being those of the integers. -/
theorem perfectChernClass_derivedTensor_two_of_constantRank
    (perfectE : RingedSpace.IsPerfect.{u, u + 1} E) (perfectF : RingedSpace.IsPerfect.{u, u + 1} F)
    (r s : ℤ) (hr : ∀ x, perfectRank E perfectE x = r) (hs : ∀ x, perfectRank F perfectF x = s) :
    TotalChowClass.homComponent 2 (perfectChernClass C sX hEF) =
      r • TotalChowClass.homComponent 2 (perfectChernClass C sX hF) +
        s • TotalChowClass.homComponent 2 (perfectChernClass C sX hE) +
        Ring.choose r 2 • TotalChowClass.homComponent 1 (perfectChernClass C sX hF) ^ 2 +
        (r * s - 1) • (TotalChowClass.homComponent 1 (perfectChernClass C sX hF) *
          TotalChowClass.homComponent 1 (perfectChernClass C sX hE)) +
        Ring.choose s 2 • TotalChowClass.homComponent 1 (perfectChernClass C sX hE) ^ 2 := by
  have eE : perfectRank E perfectE = LocallyConstant.const X r := LocallyConstant.ext hr
  have eF : perfectRank F perfectF = LocallyConstant.const X s := LocallyConstant.ext hs
  have eE₂ : (perfectRank E perfectE).map (fun k ↦ Ring.choose k 2) =
      LocallyConstant.const X (Ring.choose r 2) := LocallyConstant.ext fun x ↦ by
    simp [LocallyConstant.map_apply, hr x]
  have eF₂ : (perfectRank F perfectF).map (fun k ↦ Ring.choose k 2) =
      LocallyConstant.const X (Ring.choose s 2) := LocallyConstant.ext fun x ↦ by
    simp [LocallyConstant.map_apply, hs x]
  rw [perfectChernClass_derivedTensor_two C sX hE hF hEF perfectE perfectF,
    perfectPowerSum_zero_eq_ofLocallyConstant C sX hE perfectE,
    perfectPowerSum_zero_eq_ofLocallyConstant C sX hF perfectF, eE₂, eF₂, eE, eF,
    ofLocallyConstant_const, ofLocallyConstant_const, ofLocallyConstant_const,
    ofLocallyConstant_const]
  simp only [zsmul_eq_mul, Int.cast_sub, Int.cast_mul, Int.cast_one]

end Main

end Stacks.Chow

end
