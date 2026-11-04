module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ApproximationTriangle
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.CyclesLift
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.InstanceIndependence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentLocal
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardReflect
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Ri_*E` pseudo-coherent implies `E` pseudo-coherent: the converse half of Stacks 09VA

Let `i : Z ⟶ X` be a morphism of ringed spaces whose underlying continuous map is a closed
embedding and such that `i_*𝒪_Z` is a pseudo-coherent `𝒪_X`-module. This file proves that
`E ∈ D(𝒪_Z)` is `m`-pseudo-coherent as soon as `Ri_*E` is, which is the implication of
Stacks 09VA that the forward half
(`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedPushforwardOXMod`) leaves open.

The argument is the source's. Pseudo-coherence is local on `Z`, and an open of `Z` is the preimage
of an open of `X`, so we may replace `X` by an open on which `Ri_*E`, and hence `E`, is bounded
above. Then we induct on `k`, where `m + k` bounds the top nonvanishing cohomological degree of
`E`.

* If `k = 0` the cohomology of `E` vanishes above `m`, so Stacks 08DN(1) read through `i_*`
  (`isFiniteType_homology_of_isPseudoCoherentFrom_derivedPushforward`, in the namespace
  `AlgebraicGeometry.RingedSpace`) makes `H^m(E)` an `𝒪_Z`-module of finite type, and
  `AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_isFiniteType_homology` turns a
  local epimorphism `𝒪_Z^{⊕n} ⟶ H^m(E)` into the approximation `𝒪_Z^{⊕n}[-m] ⟶ ℰ^•` asked for.
* If `k + 1`, the same two steps at `p = m + k + 1` produce, locally on `Z`, a strictly perfect
  complex `𝒫` concentrated in degree `p` and a map `𝒫 ⟶ ℰ^•|_U` which is an isomorphism on
  cohomology above `p` and an epimorphism in degree `p`. Its cone `C` has no cohomology from
  degree `p` upwards; `Ri_*C` is `m`-pseudo-coherent by Stacks 08CD(1) applied to the
  pushed-forward triangle, whose first term is `Ri_*𝒫` — pseudo-coherent by the hypothesis on
  `i_*𝒪_Z` — and whose second is `Ri_*(E|_U)`; the inductive hypothesis, applied to
  `i|_U : Z|_U ⟶ X|_W`, makes `C` itself `m`-pseudo-coherent, and Stacks 08CD(2) concludes for
  `E|_U`.

## Main results

* `isPseudoCoherentFrom_singleFunctor_pushforwardStructureModule_restrict`, in the namespace
  `AlgebraicGeometry.RingedSpace`: the hypothesis of Stacks 09VA, localized to an open subspace of
  `X`, in the form the induction carries it.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_cone_reflect`: one inductive step,
  stated for an abstract morphism of ringed spaces with the inductive hypothesis as an argument.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_derivedPushforwardOXMod_ind` and
  `isPseudoCoherentFrom_Q_of_derivedPushforwardOXMod_of_bounded`: the induction, and the same with
  the induction variable eliminated in favour of a bound on the cohomology.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_singleFunctor_transfer` and
  `isPseudoCoherentFrom_derivedPushforward_Q_transfer`: the two transfers of the hypotheses between
  two choices of derived category.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_derivedPushforwardOXMod`: the converse
  half of Stacks 09VA.

## Implementation notes

The induction changes the ambient ringed space, so an inductive step for `i : Z ⟶ X` re-applies
the inductive hypothesis to `i|_U : Z|_U ⟶ X|_W`, and the step after that would need
`HasDerivedCategory` instances for the open subspaces of `X|_W`. A hypothesis of the form
`∀ V : Opens X.carrier, HasDerivedCategory (OXMod (X.restrict V))` does not supply those, and Lean
forbids universe-polymorphic recursion, so no statement with two derived-category universes can
serve as its own inductive hypothesis. The induction therefore runs under the single hypothesis
`∀ Y : RingedSpace, HasDerivedCategory.{w} (OXMod Y)`, which *is* stable under shrinking; it is
satisfied at `w = u + 1` by `HasDerivedCategory.standard`, and
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_transfer` bridges from there to the
arbitrary instance of the statement of Stacks 09VA. The bridge happens once, outside the
induction.

`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_cone_reflect` is a separate lemma rather
than part of the induction because every object in it stays behind a variable: instantiating the
cone construction at the restriction functors of the inductive step directly exhausts the
heartbeat budget, while routing through this lemma is free.

## References

* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [Stacks Project, Lemma 20.47.4 (Tag 08DN)](https://stacks.math.columbia.edu/tag/08DN)
* [Stacks Project, Lemma 20.46.10 (Tag 08CD)](https://stacks.math.columbia.edu/tag/08CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
  StrictlyPerfect

universe w w' d u

namespace AlgebraicGeometry.RingedSpace

/-! ### The induction, under a `HasDerivedCategory` instance for every ringed space -/

/-- The cohomology of `K` is the cohomology of any object `E` of the derived category that `Q K`
is isomorphic to. -/
private def homologyIsoOfQObjIso {Z : RingedSpace.{u, u}} [HasDerivedCategory.{w} (OXMod.{u, u} Z)]
    {E : DerivedCategory (OXMod.{u, u} Z)} (K : CochainComplex (OXMod.{u, u} Z) ℤ)
    (e : DerivedCategory.Q.obj K ≅ E) (j : ℤ) :
    K.homology j ≅ (DerivedCategory.homologyFunctor (OXMod.{u, u} Z) j).obj E :=
  (derivedHomologyIso K j).symm ≪≫ (DerivedCategory.homologyFunctor _ j).mapIso e

/-- If `Ri_*E` is `m`-pseudo-coherent, then so is `Ri|_{i⁻¹W *}F` for any `F ≅ E|_{i⁻¹W}`. -/
private theorem isPseudoCoherentFrom_derivedPushforward_restrict_of_iso
    {Z X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u, u} Z)]
    [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    [∀ V : Opens X.carrier, HasDerivedCategory.{w} (OXMod.{u, u} (X.restrict V.isOpenEmbedding))]
    [∀ V : Opens Z.carrier, HasDerivedCategory.{w} (OXMod.{u, u} (Z.restrict V.isOpenEmbedding))]
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i.hom.base) (m : ℤ)
    {E : DerivedCategory (OXMod.{u, u} Z)}
    (hE : IsPseudoCoherentFrom ((derivedPushforwardOXMod i hi).obj E) m) (W : Opens X.carrier)
    {F : DerivedCategory
      (OXMod.{u, u} (Z.restrict ((Opens.map i.hom.base).obj W).isOpenEmbedding))}
    (e : F ≅ (derivedRestrictModules Z ((Opens.map i.hom.base).obj W)).obj E) :
    IsPseudoCoherentFrom ((derivedPushforwardOXMod (restrictHom i W)
      (isClosedEmbedding_restrictHom i W hi)).obj F) m :=
  ((isPseudoCoherentFrom_derivedRestrictModules _ m hE W).ofIso
    (derivedRestrictPushforwardObjIso i W hi E)).ofIso
    ((derivedPushforwardOXMod (restrictHom i W)
      (isClosedEmbedding_restrictHom i W hi)).mapIso e).symm

section Universal

variable [hd : ∀ Y : RingedSpace.{u, u}, HasDerivedCategory.{w} (OXMod.{u, u} Y)]

/-- **The hypothesis of Stacks 09VA localizes.** If `i_*𝒪_Z` placed in degree zero is
`j`-pseudo-coherent on `X` for every `j`, then `(i|_{i⁻¹U})_*𝒪_{Z|i⁻¹U}` placed in degree zero is
`j`-pseudo-coherent on `X|_U` for every `j`.

This is
`isPseudoCoherentFrom_singleFunctor_pushforwardStructureModule_restrictHom`
with the hypothesis in the `∀ j` form rather than as pseudo-coherence of a single complex, which
is what the induction of the converse half of Stacks 09VA can carry: the `∀ j` form is what
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_pushforward_isStrictlyPerfect` consumes, and
it is stable under the localization, whereas pseudo-coherence of a single complex would have to be
re-established at every step. -/
public theorem isPseudoCoherentFrom_singleFunctor_pushforwardStructureModule_restrict
    {Z X : RingedSpace.{u, u}} (i : Z ⟶ X)
    (hO : ∀ j : ℤ, IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj
      (pushforwardStructureModule i)) j)
    (U : Opens X.carrier) (j : ℤ) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor
      (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) 0).obj
        (pushforwardStructureModule (restrictHom i U))) j :=
  ((isPseudoCoherentFrom_derivedRestrictModules _ j (hO j) U).ofIso
    (derivedRestrictSingleFunctorIso U 0 (pushforwardStructureModule i))).ofIso
    ((DerivedCategory.singleFunctor (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) 0).mapIso
      (restrictPushforwardStructureModuleIso i U))

/-- **One inductive step of the converse half of Stacks 09VA.** Let `i : Z ⟶ X` be a closed
embedding of ringed spaces with `i_*𝒪_Z` pseudo-coherent, let `𝒫` be a strictly perfect complex of
`𝒪_Z`-modules and let `φ : 𝒫 ⟶ B` be a morphism of `D(𝒪_Z)` which is an isomorphism on cohomology
above `p` and an epimorphism in degree `p`. Suppose `Ri_*B` is `m`-pseudo-coherent, and suppose the
statement of Stacks 09VA is already known for objects whose cohomology vanishes from degree `p`
upwards. Then `B` is `m`-pseudo-coherent.

The cone `C` of `φ` has no cohomology from degree `p` upwards
(`CategoryTheory.isZero_homology_obj₃_of_distinguished`). Its pushforward `Ri_*C` is the third
term of the pushed-forward distinguished triangle, whose first term `Ri_*𝒫` is pseudo-coherent
(`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_pushforward_isStrictlyPerfect`) and whose
second is `Ri_*B`, so Stacks 08CD(1) makes it `m`-pseudo-coherent; the assumed case of Stacks 09VA
makes `C` itself `m`-pseudo-coherent, and Stacks 08CD(2) on the original triangle gives `B`. -/
public theorem isPseudoCoherentFrom_of_cone_reflect {Z X : RingedSpace.{u, u}} (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding i.hom.base)
    (hO : ∀ j : ℤ, IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj
      (pushforwardStructureModule i)) j)
    (m p : ℤ) {P : CochainComplex (OXMod.{u, u} Z) ℤ} (hP : IsStrictlyPerfect P)
    {B : DerivedCategory (OXMod.{u, u} Z)} (φ : DerivedCategory.Q.obj P ⟶ B)
    (hiso : ∀ j : ℤ, p < j → IsIso ((DerivedCategory.homologyFunctor _ j).map φ))
    (hepi : Epi ((DerivedCategory.homologyFunctor _ p).map φ))
    (hRiB : IsPseudoCoherentFrom ((derivedPushforwardOXMod i hi).obj B) m)
    (hstep : ∀ C : DerivedCategory (OXMod.{u, u} Z),
      IsPseudoCoherentFrom ((derivedPushforwardOXMod i hi).obj C) m →
      (∀ j : ℤ, p ≤ j → IsZero ((DerivedCategory.homologyFunctor _ j).obj C)) →
      IsPseudoCoherentFrom C m) :
    IsPseudoCoherentFrom B m := by
  obtain ⟨Cn, g, h₃, hT⟩ := distinguished_cocone_triangle φ
  set T := Triangle.mk φ g h₃ with hTdef
  have hCvanish : ∀ j : ℤ, p ≤ j → IsZero ((DerivedCategory.homologyFunctor _ j).obj Cn) :=
    fun j hj => isZero_homology_obj₃_of_distinguished p T hT hiso hepi j hj
  have hRiP : IsPseudoCoherentFrom ((derivedPushforwardOXMod i hi).obj
      (DerivedCategory.Q.obj P)) (m + 1) :=
    (isPseudoCoherentFrom_Q_pushforward_isStrictlyPerfect i (m + 1) hO hP).ofIso
      ((derivedPushforwardOXModFactors i hi).app P).symm
  exact isPseudoCoherentFrom_obj₂_of_distinguished m T hT
    ((isPseudoCoherent_Q_obj_of_isStrictlyPerfect hP).isPseudoCoherentFrom m)
    (hstep Cn (isPseudoCoherentFrom_obj₃_of_distinguished m
      ((derivedPushforwardOXMod i hi).mapTriangle.obj T)
      (map_distinguished_derivedPushforwardOXMod i hi T hT) hRiP hRiB) hCvanish)

/-- **The induction of the converse half of Stacks 09VA.** If `Ri_*E` is `m`-pseudo-coherent and
the cohomology of `E` vanishes above `m + k`, then `E` is `m`-pseudo-coherent.

The induction is on `k`. Its base case is
`AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_isFiniteType_homology` applied to a
complex representing `E`, and its step is
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_cone_reflect` applied to the local
approximation that the same lemma provides at degree `m + k + 1`. The step replaces `X` by an open
`W` and `Z` by `i⁻¹W`, which is why the hypothesis on the derived categories has to hold for every
ringed space. -/
public theorem isPseudoCoherentFrom_of_derivedPushforwardOXMod_ind (k : ℕ) :
    ∀ (Z X : RingedSpace.{u, u}) (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i.hom.base),
      (∀ j : ℤ, IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj
        (pushforwardStructureModule i)) j) →
      ∀ (m : ℤ) (E : DerivedCategory (OXMod.{u, u} Z)),
        IsPseudoCoherentFrom ((derivedPushforwardOXMod i hi).obj E) m →
        (∀ j : ℤ, m + (k : ℤ) < j →
          IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Z) j).obj E)) →
        IsPseudoCoherentFrom E m := by
  induction k with
  | zero =>
    intro Z X i hi hO m E hE hvanish
    have hvanish' : ∀ j : ℤ, m < j →
        IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Z) j).obj E) :=
      fun j hj => hvanish j (by omega)
    have hft := isFiniteType_homology_of_isPseudoCoherentFrom_derivedPushforward i hi E m m
      le_rfl hE hvanish'
    set K := DerivedCategory.Q.objPreimage E with hKdef
    have e : DerivedCategory.Q.obj K ≅ E := Functor.objObjPreimageIso DerivedCategory.Q E
    exact ⟨K, isPseudoCoherentComplexFrom_of_isFiniteType_homology K m
      (fun j hj => IsZero.of_iso (hvanish' j hj) (homologyIsoOfQObjIso K e j))
      (SheafOfModules.IsFiniteType.of_iso (R := structureSheafOfRings Z) hft
        (homologyIsoOfQObjIso K e m).symm), ⟨e⟩⟩
  | succ k ih =>
    intro Z X i hi hO m E hE hvanish
    refine isPseudoCoherentFrom_of_local_restrict E m fun z => ?_
    have hvanishp : ∀ j : ℤ, m + (k : ℤ) + 1 < j →
        IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Z) j).obj E) :=
      fun j hj => hvanish j (by push_cast; omega)
    have hft := isFiniteType_homology_of_isPseudoCoherentFrom_derivedPushforward i hi E m
      (m + (k : ℤ) + 1) (by omega) hE hvanishp
    set K := DerivedCategory.Q.objPreimage E with hKdef
    have e : DerivedCategory.Q.obj K ≅ E := Functor.objObjPreimageIso DerivedCategory.Q E
    obtain ⟨U, hzU, P, hP, α, hα, hαepi⟩ :=
      isPseudoCoherentComplexFrom_of_isFiniteType_homology K (m + (k : ℤ) + 1)
        (fun j hj => IsZero.of_iso (hvanishp j hj) (homologyIsoOfQObjIso K e j))
        (SheafOfModules.IsFiniteType.of_iso (R := structureSheafOfRings Z) hft
          (homologyIsoOfQObjIso K e (m + (k : ℤ) + 1)).symm) z
    obtain ⟨W, hW⟩ := exists_opens_preimage_eq i hi.toIsInducing U
    subst hW
    refine ⟨_, hzU, ?_⟩
    have hi' := isClosedEmbedding_restrictHom i W hi
    have hO' := isPseudoCoherentFrom_singleFunctor_pushforwardStructureModule_restrict i hO W
    have eE' : DerivedCategory.Q.obj (restrictComplex K ((Opens.map i.hom.base).obj W)) ≅
        (derivedRestrictModules Z ((Opens.map i.hom.base).obj W)).obj E :=
      (derivedRestrictModulesObjQIso Z ((Opens.map i.hom.base).obj W) K).symm ≪≫
        (derivedRestrictModules Z ((Opens.map i.hom.base).obj W)).mapIso e
    exact (isPseudoCoherentFrom_of_cone_reflect (restrictHom i W) hi' hO' m (m + (k : ℤ) + 1) hP
      (DerivedCategory.Q.map α)
      (fun j hj => isIso_homologyFunctor_map_Q_map α j (hα j hj))
      (epi_homologyFunctor_map_Q_map α (m + (k : ℤ) + 1) hαepi)
      (isPseudoCoherentFrom_derivedPushforward_restrict_of_iso i hi m hE W eE')
      (fun C hC hCv => ih _ _ (restrictHom i W) hi' hO' m C hC
        (fun j hj => hCv j (by omega)))).ofIso eE'

/-- **The converse half of Stacks 09VA, under a `HasDerivedCategory` instance for every ringed
space and a bound on the cohomology of `E`.** This is
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_derivedPushforwardOXMod_ind` with the
induction variable eliminated: a bound `b` on the top nonvanishing cohomological degree of the
complex `𝒦` is a bound of the form `m + k` for `k = (b - m).toNat`.

The bound is stated on the cohomology sheaves of `𝒦` rather than on those of the object
`Q 𝒦` of the derived category, so that it mentions no `HasDerivedCategory` instance and needs no
transport when the instance changes. -/
public theorem isPseudoCoherentFrom_Q_of_derivedPushforwardOXMod_of_bounded
    {Z X : RingedSpace.{u, u}} (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i.hom.base)
    (hO : ∀ j : ℤ, IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj
      (pushforwardStructureModule i)) j)
    (m b : ℤ) (K : CochainComplex (OXMod.{u, u} Z) ℤ)
    (hE : IsPseudoCoherentFrom ((derivedPushforwardOXMod i hi).obj
      (DerivedCategory.Q.obj K)) m)
    (hb : ∀ j : ℤ, b < j → IsZero (K.homology j)) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m :=
  isPseudoCoherentFrom_of_derivedPushforwardOXMod_ind (b - m).toNat Z X i hi hO m
    (DerivedCategory.Q.obj K) hE fun j hj =>
      IsZero.of_iso (hb j (by have := Int.self_le_toNat (b - m); omega))
        (derivedHomologyIso K j)

end Universal

/-! ### Transferring the hypothesis and the conclusion between derived categories -/

/-- **The hypothesis of Stacks 09VA does not depend on the choice of derived category.**
`DerivedCategory.singleFunctorIsoCompQ` identifies the object `i_*𝒪_Z` placed in degree zero with
the image under `Q` of the complex `i_*𝒪_Z` placed in degree zero, so
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_transfer` applies to it. -/
public theorem isPseudoCoherentFrom_singleFunctor_transfer {Y : RingedSpace.{u, u}}
    (inst₁ : HasDerivedCategory.{w} (StrictlyPerfect.OXMod.{u, u} Y))
    (inst₂ : HasDerivedCategory.{w'} (StrictlyPerfect.OXMod.{u, u} Y))
    (M : StrictlyPerfect.OXMod.{u, u} Y) (j : ℤ)
    (h : @IsPseudoCoherentFrom Y inst₁
      ((@DerivedCategory.singleFunctor _ _ _ inst₁ 0).obj M) j) :
    @IsPseudoCoherentFrom Y inst₂ ((@DerivedCategory.singleFunctor _ _ _ inst₂ 0).obj M) j := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := h
  obtain ⟨P', hP', ⟨eP'⟩⟩ := isPseudoCoherentFrom_Q_transfer inst₁ inst₂
    ((CochainComplex.singleFunctor (StrictlyPerfect.OXMod.{u, u} Y) 0).obj M) j
    ⟨P, hP, ⟨eP ≪≫ (@DerivedCategory.singleFunctorIsoCompQ _ _ _ inst₁ 0).app M⟩⟩
  exact ⟨P', hP', ⟨eP' ≪≫ ((@DerivedCategory.singleFunctorIsoCompQ _ _ _ inst₂ 0).app M).symm⟩⟩

/-- **`m`-pseudo-coherence of `Ri_*(Q 𝒦)` does not depend on the choice of derived category.**
`AlgebraicGeometry.RingedSpace.derivedPushforwardOXModFactors` identifies `Ri_*(Q 𝒦)` with
`Q(i_*𝒦)` for the degreewise pushforward `i_*𝒦`, so
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_transfer` applies to it. -/
public theorem isPseudoCoherentFrom_derivedPushforward_Q_transfer {Z X : RingedSpace.{u, u}}
    (instZ₁ : HasDerivedCategory.{w} (StrictlyPerfect.OXMod.{u, u} Z))
    (instX₁ : HasDerivedCategory.{w} (StrictlyPerfect.OXMod.{u, u} X))
    (instZ₂ : HasDerivedCategory.{w'} (StrictlyPerfect.OXMod.{u, u} Z))
    (instX₂ : HasDerivedCategory.{w'} (StrictlyPerfect.OXMod.{u, u} X))
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i.hom.base)
    (K : CochainComplex (StrictlyPerfect.OXMod.{u, u} Z) ℤ) (m : ℤ)
    (h : @IsPseudoCoherentFrom X instX₁ ((@derivedPushforwardOXMod _ _ i instZ₁ instX₁ hi).obj
      ((@DerivedCategory.Q _ _ _ instZ₁).obj K)) m) :
    @IsPseudoCoherentFrom X instX₂ ((@derivedPushforwardOXMod _ _ i instZ₂ instX₂ hi).obj
      ((@DerivedCategory.Q _ _ _ instZ₂).obj K)) m := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := h
  obtain ⟨P', hP', ⟨eP'⟩⟩ := isPseudoCoherentFrom_Q_transfer instX₁ instX₂
    (((pushforwardOXMod i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) m
    ⟨P, hP, ⟨eP ≪≫ (@derivedPushforwardOXModFactors _ _ i instZ₁ instX₁ hi).app K⟩⟩
  exact ⟨P', hP',
    ⟨eP' ≪≫ ((@derivedPushforwardOXModFactors _ _ i instZ₂ instX₂ hi).app K).symm⟩⟩

/-! ### The converse half of Stacks 09VA -/

/-- **The converse half of Stacks 09VA for an object with a bound on its cohomology**, at an
arbitrary choice of derived category.

`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_of_derivedPushforwardOXMod_of_bounded`
proves this under the hypothesis that a derived category has been chosen for the modules on
*every* ringed space, which `HasDerivedCategory.standard` supplies at the universe `u + 1`. The
three transfers between that choice and the given one are
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_singleFunctor_transfer` for the hypothesis on
`i_*𝒪_Z`, `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedPushforward_Q_transfer` for
the hypothesis on `Ri_*(Q 𝒦)`, and
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_transfer` for the conclusion. The bound is
stated on the cohomology sheaves of `𝒦`, which mention no derived category and so need no
transfer. -/
public theorem isPseudoCoherentFrom_Q_of_derivedPushforwardOXMod_of_bounded'
    {Z X : RingedSpace.{u, u}} [instZ : HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} Z)]
    [instX : HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i.hom.base)
    (hO : ∀ j : ℤ, IsPseudoCoherentFrom ((DerivedCategory.singleFunctor
      (StrictlyPerfect.OXMod.{u, u} X) 0).obj (pushforwardStructureModule i)) j)
    (m b : ℤ) (K : CochainComplex (StrictlyPerfect.OXMod.{u, u} Z) ℤ)
    (hE : IsPseudoCoherentFrom ((derivedPushforwardOXMod i hi).obj
      (DerivedCategory.Q.obj K)) m)
    (hb : ∀ j : ℤ, b < j → IsZero (K.homology j)) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m :=
  isPseudoCoherentFrom_Q_transfer (X := Z)
    (HasDerivedCategory.standard (StrictlyPerfect.OXMod.{u, u} Z)) instZ K m
    (isPseudoCoherentFrom_Q_of_derivedPushforwardOXMod_of_bounded
      (hd := fun Y => HasDerivedCategory.standard (StrictlyPerfect.OXMod.{u, u} Y)) i hi
      (fun j => isPseudoCoherentFrom_singleFunctor_transfer (Y := X) instX
        (HasDerivedCategory.standard (StrictlyPerfect.OXMod.{u, u} X)) _ j (hO j))
      m b K
      (isPseudoCoherentFrom_derivedPushforward_Q_transfer instZ instX
        (HasDerivedCategory.standard (StrictlyPerfect.OXMod.{u, u} Z))
        (HasDerivedCategory.standard (StrictlyPerfect.OXMod.{u, u} X)) i hi K m hE)
      hb)

/-- **The converse half of Stacks 09VA.** Let `i : Z ⟶ X` be a morphism of ringed spaces whose
underlying continuous map is a closed embedding and such that `i_*𝒪_Z` is pseudo-coherent as an
`𝒪_X`-module. If `Ri_*E` is `m`-pseudo-coherent for `E ∈ D(𝒪_Z)` then so is `E`.

Pseudo-coherence is local on `Z`, and the opens `i⁻¹W` for `W` open in `X` are a fundamental
system of neighbourhoods of a point of `Z`, so it is enough to produce, for each `z`, an open `W`
of `X` containing `i(z)` on which `E` becomes `m`-pseudo-coherent. Take for `W` an open on which
the cohomology of `Ri_*E` is bounded above
(`AlgebraicGeometry.RingedSpace.exists_isZero_homology_gt_derivedRestrict`); then the cohomology
of `E|_{i⁻¹W}` is bounded above as well, because `i_*` reflects zero objects
(`AlgebraicGeometry.RingedSpace.isZero_homology_of_isZero_homology_derivedPushforward`), and
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_of_derivedPushforwardOXMod_of_bounded'`
applies to `i|_{i⁻¹W} : Z|_{i⁻¹W} ⟶ X|_W`. -/
@[stacks 09VA "Ri_*E m-pseudo-coherent implies E m-pseudo-coherent",
  sga "6 III 1.1.1" "sufficiency: Ri_*E ⇒ E"]
public theorem isPseudoCoherentFrom_of_derivedPushforwardOXMod {Z X : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} Z)]
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]
    [∀ V : Opens X.carrier,
      HasDerivedCategory.{w} (StrictlyPerfect.OXMod.{u, u} (X.restrict V.isOpenEmbedding))]
    [∀ V : Opens Z.carrier,
      HasDerivedCategory.{w} (StrictlyPerfect.OXMod.{u, u} (Z.restrict V.isOpenEmbedding))]
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i.hom.base)
    (hO : IsPseudoCoherent ((DerivedCategory.singleFunctor (StrictlyPerfect.OXMod.{u, u} X) 0).obj
      (pushforwardStructureModule i)))
    (m : ℤ) (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} Z))
    (hE : IsPseudoCoherentFrom ((derivedPushforwardOXMod i hi).obj E) m) :
    IsPseudoCoherentFrom E m := by
  refine isPseudoCoherentFrom_of_local_restrict E m fun z => ?_
  obtain ⟨W, hzW, b, hb⟩ := exists_isZero_homology_gt_derivedRestrict
    ((derivedPushforwardOXMod i hi).obj E) m hE (i.hom.base z)
  refine ⟨(Opens.map i.hom.base).obj W, hzW, ?_⟩
  have hi' := isClosedEmbedding_restrictHom i W hi
  have hO' := isPseudoCoherentFrom_singleFunctor_pushforwardStructureModule_restrictHom i hO W
  -- the cohomology of `E|_{i⁻¹W}` vanishes above `b`, because `i_*` reflects zero objects
  have hb' : ∀ j : ℤ, b < j → IsZero ((DerivedCategory.homologyFunctor
      (StrictlyPerfect.OXMod.{u, u} (Z.restrict ((Opens.map i.hom.base).obj W).isOpenEmbedding))
        j).obj ((derivedRestrictModules Z ((Opens.map i.hom.base).obj W)).obj E)) := by
    intro j hj
    refine isZero_homology_of_isZero_homology_derivedPushforward (restrictHom i W) hi' _ j ?_
    exact IsZero.of_iso (hb j hj)
      ((DerivedCategory.homologyFunctor _ j).mapIso
        (derivedRestrictPushforwardObjIso i W hi E)).symm
  -- a complex representing `E|_{i⁻¹W}`, and the bound read on its cohomology sheaves
  set K := DerivedCategory.Q.objPreimage
    ((derivedRestrictModules Z ((Opens.map i.hom.base).obj W)).obj E) with hKdef
  have e : DerivedCategory.Q.obj K ≅
      (derivedRestrictModules Z ((Opens.map i.hom.base).obj W)).obj E :=
    Functor.objObjPreimageIso DerivedCategory.Q _
  refine (isPseudoCoherentFrom_Q_of_derivedPushforwardOXMod_of_bounded' (restrictHom i W) hi' hO'
    m b K (isPseudoCoherentFrom_derivedPushforward_restrict_of_iso i hi m hE W e)
    fun j hj => IsZero.of_iso (hb' j hj) (homologyIsoOfQObjIso K e j)).ofIso e

end AlgebraicGeometry.RingedSpace

end
