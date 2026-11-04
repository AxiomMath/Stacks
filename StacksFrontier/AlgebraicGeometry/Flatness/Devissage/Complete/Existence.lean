module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineQcohEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleFibreSupportDimension
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.BaseChangeAt
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Join
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.EtaleNeighborhoodComplete
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Glueing
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep.FreeMap
public import StacksFrontier.AlgebraicGeometry.ProperFibreDimensionNeighbourhood.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Existence of a complete dévissage after elementary étale neighbourhoods

Stacks 05HR asserts that a finite-type quasi-coherent module `F` on a scheme `X` locally of
finite type over `S` acquires a complete dévissage at a chosen point `x` after passing to
elementary étale neighbourhoods of `x` and of its image `s`. The proof is an induction on the
dimension `d` of the support of `F` on the fibre of `X` through `x`.

Stacks 05HU is the version of this over a whole fibre, for `X` of finite type over `S`: a single
elementary étale neighbourhood `(S', s')` of `s` and finitely many étale morphisms
`hᵢ : Yᵢ ⟶ X ×_S S'` whose images cover the fibre `(X_{S'})_{s'} = X_s`, with a complete
dévissage of the pullback of `F` to each `Yᵢ` over `s'`. Quasi-compactness of the fibre reduces
it to Stacks 05HR at each of its points, and Stacks 05HJ carries the dévissages obtained there
to the common neighbourhood.

This module carries the induction. It is organised around the predicate
`AlgebraicGeometry.HasEtaleNeighborhoodCompleteDevissageAt`, which names the conclusion of
Stacks 05HR, so that the inductive hypothesis is a statement about the same predicate at a
smaller dimension.

The induction runs as follows. If `x` is not in the support of `F` there is nothing to do: the
complement of the support is an open neighbourhood of `x` on which `F` pulls back to zero, and
the empty dévissage serves. Otherwise Stacks 05H6 produces elementary étale neighbourhoods over
which the pullback of `F` has a *one-step* dévissage `D` at the new point, and the conclusion of
Stacks 05HR is local for elementary étale neighbourhoods, so the problem may be replaced by the
one for the pullback. Stacks 05HF then produces a map `α` from a finite free module on the
smooth scheme `Y` of `D` to the direct image of the module on its closed subscheme, which is an
isomorphism over the residue field of the generic point of the distinguished fibre of `Y`, and
whose cokernel has strictly smaller fibre-support dimension. The induction applies to that
cokernel on `Y` over the new base, at the distinguished point `y` of `D`. Stacks 05HE then
transports the one-step dévissage through the two elementary étale neighbourhoods the inductive
hypothesis returns, and Stacks 05HK carries the complete dévissage of the cokernel to the fibre
product of those two neighbourhoods, producing the situation (a)–(d) of the source's final
paragraph. That paragraph — the shrinking of the one-step dévissage and of the complete
dévissage until the two fit together — is
`AlgebraicGeometry.exists_etaleNeighborhood_completeDevissageAt_of_cokernelDevissage`.

Two facts make the induction legitimate. First, the fibre-support dimension does not grow when
passing to an elementary étale neighbourhood: this is
`AlgebraicGeometry.fiberSupportDim_le_of_etaleSquare`, proved here from the étale invariance of
the local Krull dimension (Stacks 04N4, in the form
`AlgebraicGeometry.topologicalKrullDimAt_preimage_eq_of_etale`) together with the
dimension-attainment clause of a one-step dévissage at a point. Second, the dimension lives in
`WithBot ℕ∞`, which is well-founded for `<`, so the induction is a well-founded recursion on
that value rather than on a natural number — the source's `d` is an integer only because it
tacitly assumes the support nonempty.

## Main definitions

* `AlgebraicGeometry.HasEtaleNeighborhoodCompleteDevissageAt`: the conclusion of Stacks 05HR
  for `F/X/S` at `x`.
* `AlgebraicGeometry.fiberSupportDim`: the dimension of the support of `F` on the fibre of `f`
  through `x`, the quantity the induction of Stacks 05HR runs on.

## Main results

* `AlgebraicGeometry.fiberSupportDim_eq`: the fibre-support dimension read off the fibre over
  any point the structure morphism carries the given point to.
* `AlgebraicGeometry.isQuasicoherent_isFiniteType_cokernel`: the cokernel of a map out of a free
  module into the direct image of the module of a one-step dévissage is quasi-coherent of finite
  type.
* `IsGenericPoint.map_eq_of_isOpenMap`: a continuous open map into an
  irreducible space carries generic point to generic point.
* `AlgebraicGeometry.topologicalKrullDimAt_fiberSupport_eq_of_etaleSquare` and
  `AlgebraicGeometry.fiberSupportDim_le_of_etaleSquare`: the fibre-support dimension does not
  grow along an elementary étale neighbourhood carrying a one-step dévissage at a point.
* `AlgebraicGeometry.hasEtaleNeighborhoodCompleteDevissageAt`: Stacks 05HR.
* `AlgebraicGeometry.exists_etaleNeighborhood_completeDevissage_cover`: Stacks 05HU.

## Implementation notes

`AlgebraicGeometry.hasEtaleNeighborhoodCompleteDevissageAt` is the whole covering set of
Stacks 05HR, and likewise
`AlgebraicGeometry.exists_etaleNeighborhood_completeDevissage_cover` of Stacks 05HU.

The common elementary étale neighbourhood of Stacks 05HU is the fibre product over `S` of the
finitely many neighbourhoods Stacks 05HR returns, shrunk to an affine open neighbourhood of its
distinguished point. The shrinking is not in the source, which applies Stacks 05HJ to a fibre
product that need not be affine; it costs nothing, since the conclusion only asserts that *some*
elementary étale neighbourhood works. That the fibre product of elementary neighbourhoods is
again elementary is read off a section `Spec κ(s) ⟶ S'` over `S` through the distinguished
point, which an elementary neighbourhood has and which a fibre product of two inherits.

Coverage of the fibre is stated for the fibre of the base-changed morphism, the right-hand side
of the source's `X_s = (X_{S'})_{s'}`; the identification itself is the comparison morphism of
fibres attached to the cartesian square, which is an isomorphism because the neighbourhood is
elementary. The covering open sets are the images in `X_s` of the fibres of the neighbourhoods of
Stacks 05HR; each is open because the induced morphism of fibres is étale (Stacks 04NI), and
finitely many suffice because a finite-type morphism has quasi-compact fibres.

The last paragraph of the source's proof — the one the source itself leaves to the reader, "We
suggest the reader do this on their own using Lemmas 05HA and 05HM instead of reading the proof
that follows" — is
`AlgebraicGeometry.exists_etaleNeighborhood_completeDevissageAt_of_cokernelDevissage` in
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/Join.lean`. Its data are the
situation (a)–(d) that everything here produces: a one-step dévissage of `F/X/S` at `x`, a
generically invertible map `α` out of a free module on its smooth scheme `Y`, an open immersion
of `Y` into a scheme `X₁` over `S` carrying a module whose restriction to `Y` is the cokernel of
`α`, and a complete dévissage of that module.

## References

* [Stacks Project, Tag 05HR](https://stacks.math.columbia.edu/tag/05HR)
* [Stacks Project, Tag 05HU](https://stacks.math.columbia.edu/tag/05HU)
* [Stacks Project, Tag 05H6](https://stacks.math.columbia.edu/tag/05H6)
* [Stacks Project, Tag 05HE](https://stacks.math.columbia.edu/tag/05HE)
* [Stacks Project, Tag 05HF](https://stacks.math.columbia.edu/tag/05HF)
* [Stacks Project, Tag 05HJ](https://stacks.math.columbia.edu/tag/05HJ)
* [Stacks Project, Tag 05HK](https://stacks.math.columbia.edu/tag/05HK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-! ### Generic points under an open map -/

/-- A continuous open map into an irreducible space carries the generic point of its source to
the generic point of its target: the image of the source is a nonempty open, hence dense, so the
closure of the image of the generic point is everything. -/
lemma IsGenericPoint.map_eq_of_isOpenMap {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [T0Space β] [PreirreducibleSpace β] {a : α} {b : β} {j : α → β}
    (hc : Continuous j) (hj : IsOpenMap j) (ha : IsGenericPoint a Set.univ)
    (hb : IsGenericPoint b Set.univ) : j a = b := by
  have hdense : Dense (Set.range j) :=
    (by simpa only [Set.image_univ] using hj Set.univ isOpen_univ :
      IsOpen (Set.range j)).dense ⟨j a, a, rfl⟩
  refine IsGenericPoint.eq ?_ hb
  simpa only [Set.image_univ, hdense.closure_eq] using ha.image hc

namespace AlgebraicGeometry

/-! ### The conclusion of Stacks 05HR -/

/-- The conclusion of **Stacks Project, Tag 05HR** for `F/X/S` at `x`: there are elementary
étale neighbourhoods `U` of `x` and `V` of the image of `x`, and a morphism `U ⟶ V` making the
square of the two structure morphisms commute and matching the distinguished points, such that
the pullback of `F` to `U` has a complete dévissage along `U ⟶ V` at the distinguished point. -/
def HasEtaleNeighborhoodCompleteDevissageAt {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X) :
    Prop :=
  ∃ (U : EtaleNeighborhood X x) (V : EtaleNeighborhood S (f x)) (h : U.scheme ⟶ V.scheme),
    U.IsElementary ∧ V.IsElementary ∧ (U.toBase ≫ f = h ≫ V.toBase) ∧ (h U.point = V.point) ∧
      ∃ (hft : LocallyOfFiniteType h)
        (hq : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent)
        (hf : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType),
        letI : LocallyOfFiniteType h := hft
        letI : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent := hq
        letI : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType := hf
        Nonempty (CompleteDevissageAt h ((Scheme.Modules.pullback U.toBase).obj F) U.point)

/-! ### The dimension the induction runs on -/

/-- The dimension of the support of `F` on the fibre of `f` through `x`. This is the quantity
`d = dim_x(Supp(F_s))` of the source's proof of Stacks 05HR, except that the dimension is taken
globally on the fibre rather than locally at `x`; the two agree as soon as a one-step dévissage
at `x` exists, which is what `AlgebraicGeometry.OneStepDevissageAt.dimension` records. -/
def fiberSupportDim {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X) : WithBot ℕ∞ :=
  topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))

/-- The fibre-support dimension may be read off the fibre over any point the structure
morphism carries `x` to. -/
lemma fiberSupportDim_eq {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X) {t : S}
    (h : f x = t) :
    fiberSupportDim f F x =
      topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι t)).obj F)) := by
  cases h
  rfl

/- `mem_supp_fiber_iff_mem_supp` stood here; it is now public in
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/EtaleNeighborhoodOneStep.lean`, which this
module imports, because the converse half of Tag 05H6 proved there needs it too. -/

/-- The comparison morphism of fibres attached to a commutative square is compatible with the
embeddings of the fibres into the sources. -/
private lemma fiberMap_comp_fiberι {U' U V' V : Scheme.{u}} (f' : U' ⟶ V') (g' : U' ⟶ U)
    (g : V' ⟶ V) (f : U ⟶ V) (hsq : g' ≫ f = f' ≫ g) (v' : V') :
    fiberMap f' g' g f hsq v' ≫ f.fiberι (g v') = f'.fiberι v' ≫ g' :=
  pullback.lift_fst _ _ _

/-- The comparison morphism of fibres, transported along an equality of the target point, is
compatible with the embeddings of the fibres into the sources. -/
private lemma fiberMap_fiberCongr_comp_fiberι {U' U V' V : Scheme.{u}} (f' : U' ⟶ V')
    (g' : U' ⟶ U) (g : V' ⟶ V) (f : U ⟶ V) (hsq : g' ≫ f = f' ≫ g) (v' : V') {s : V}
    (hs : g v' = s) :
    (fiberMap f' g' g f hsq v' ≫ (fiberCongr f hs).hom) ≫ f.fiberι s = f'.fiberι v' ≫ g' := by
  rw [Category.assoc, fiberCongr_hom_fiberι, fiberMap_comp_fiberι]

/-- The comparison morphism of fibres, transported along an equality of the target point, is
étale in a square with étale vertical arrows. -/
private lemma etale_fiberMap_fiberCongr {U' U V' V : Scheme.{u}} (f' : U' ⟶ V') (g' : U' ⟶ U)
    (g : V' ⟶ V) (f : U ⟶ V) (hsq : g' ≫ f = f' ≫ g) (v' : V') {s : V} (hs : g v' = s)
    [Etale g'] [Etale g] : Etale (fiberMap f' g' g f hsq v' ≫ (fiberCongr f hs).hom) := by
  have := etale_fiberMap f' g' g f hsq v'
  infer_instance

/-- The local dimension of the support on the distinguished fibre is unchanged by passage to a
pair of compatible étale neighbourhoods of `x` and of its image: the comparison morphism of the
two fibres is étale, and identifies one support with the inverse image of the other, so Stacks
04N4 applies. -/
lemma topologicalKrullDimAt_fiberSupport_eq_of_etaleSquare {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsFiniteType] (x : X) (U : EtaleNeighborhood X x)
    (V : EtaleNeighborhood S (f x)) (k : U.scheme ⟶ V.scheme)
    (hsq : U.toBase ≫ f = k ≫ V.toBase)
    (hmem : U.point ∈ SheafOfModules.supp ((Scheme.Modules.pullback U.toBase).obj F)) :
    ∃ (hx : f.asFiber x ∈
        SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
      (hu : k.asFiber U.point ∈ SheafOfModules.supp ((Scheme.Modules.pullback
        (k.fiberι (k U.point))).obj ((Scheme.Modules.pullback U.toBase).obj F))),
      topologicalKrullDimAt (SheafOfModules.supp ((Scheme.Modules.pullback
            (k.fiberι (k U.point))).obj ((Scheme.Modules.pullback U.toBase).obj F)))
          ⟨k.asFiber U.point, hu⟩ =
        topologicalKrullDimAt
          (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
          ⟨f.asFiber x, hx⟩ := by
  classical
  have hxF : x ∈ SheafOfModules.supp F := by
    rw [Stacks.Modules.supp_pullback] at hmem
    simpa only [Set.mem_preimage, U.map_point] using hmem
  have hFT : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType U.toBase.toLRSHom.toShHom F
  let := hFT
  set q := k U.point with hqdef
  have hbase : V.toBase q = f x := by
    have hsq' : f (U.toBase U.point) = V.toBase (k U.point) := by
      simpa only [← Scheme.Hom.comp_apply] using
        congrArg (fun m : U.scheme ⟶ S => m U.point) hsq
    exact hsq'.symm.trans (congrArg f U.map_point)
  set φ := fiberMap k U.toBase V.toBase f hsq q ≫ (fiberCongr f hbase).hom with hφ
  have : Etale φ := etale_fiberMap_fiberCongr k U.toBase V.toBase f hsq q hbase
  have hφcomp : φ ≫ f.fiberι (f x) = k.fiberι q ≫ U.toBase :=
    fiberMap_fiberCongr_comp_fiberι k U.toBase V.toBase f hsq q hbase
  set A : Set (f.fiber (f x)) :=
    SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) with hA
  set B : Set (k.fiber q) :=
    SheafOfModules.supp ((Scheme.Modules.pullback (k.fiberι q)).obj
      ((Scheme.Modules.pullback U.toBase).obj F)) with hB
  have : ((Scheme.Modules.pullback (f.fiberι (f x))).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType (f.fiberι (f x)).toLRSHom.toShHom F
  have hAclosed : IsClosed A := SheafOfModules.isClosed_supp _
  have hmap : ∀ z, f.fiberι (f x) (φ z) = U.toBase (k.fiberι q z) := fun z => by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m : k.fiber q ⟶ X => m z) hφcomp
  have hAB : B = (φ : k.fiber q → f.fiber (f x)) ⁻¹' A := by
    rw [hA, hB, Stacks.Modules.supp_pullback, Stacks.Modules.supp_pullback,
      Stacks.Modules.supp_pullback]
    ext z
    simp only [Set.mem_preimage]
    rw [hmap]
  have hφpoint : φ (k.asFiber U.point) = f.asFiber x := by
    apply (f.fiberι (f x)).isEmbedding.injective
    rw [hmap, Scheme.Hom.fiberι_asFiber, U.map_point]
    simp
  have hx : f.asFiber x ∈ A := by
    rw [hA]
    exact (mem_supp_fiber_iff_mem_supp f F x).2 hxF
  have hu : k.asFiber U.point ∈ B := by
    rw [hB]
    exact (mem_supp_fiber_iff_mem_supp k ((Scheme.Modules.pullback U.toBase).obj F)
      U.point).2 hmem
  refine ⟨hx, hu, ?_⟩
  have hpPre : k.asFiber U.point ∈ (φ : k.fiber q → f.fiber (f x)) ⁻¹' A := by
    rwa [← hAB]
  have hpA : φ (k.asFiber U.point) ∈ A := hpPre
  calc
    topologicalKrullDimAt B ⟨k.asFiber U.point, hu⟩ =
        topologicalKrullDimAt ((φ : k.fiber q → f.fiber (f x)) ⁻¹' A)
          (Homeomorph.setCongr hAB ⟨k.asFiber U.point, hu⟩) :=
      topologicalKrullDimAt_eq_of_homeomorph (Homeomorph.setCongr hAB) _
    _ = topologicalKrullDimAt ((φ : k.fiber q → f.fiber (f x)) ⁻¹' A)
          ⟨k.asFiber U.point, hpPre⟩ := rfl
    _ = topologicalKrullDimAt A ⟨φ (k.asFiber U.point), hpA⟩ :=
      topologicalKrullDimAt_preimage_eq_of_etale φ A hAclosed ⟨k.asFiber U.point, hpPre⟩
    _ = topologicalKrullDimAt A ⟨f.asFiber x, hx⟩ :=
      congrArg (topologicalKrullDimAt A)
        (Subtype.ext hφpoint : (⟨φ (k.asFiber U.point), hpA⟩ : A) = _)

/-- **The fibre-support dimension does not grow along an elementary étale neighbourhood.** If
the pullback of `F` to an étale neighbourhood `U` of `x`, over an étale neighbourhood of the
image of `x`, has a one-step dévissage at the distinguished point of `U`, then its
fibre-support dimension there is at most that of `F` at `x`.

The one-step dévissage is what makes this true: it records that the dimension of the support on
the new distinguished fibre is attained at the new point, and the local dimension is an étale
invariant, so the new dimension equals the *local* dimension of the old support at `x`, which is
at most the old dimension. -/
lemma fiberSupportDim_le_of_etaleSquare {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X) (U : EtaleNeighborhood X x)
    (V : EtaleNeighborhood S (f x)) (k : U.scheme ⟶ V.scheme)
    (hsq : U.toBase ≫ f = k ≫ V.toBase) (hk : LocallyOfFiniteType k)
    (hq : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent)
    (hf : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType)
    (D : letI := hk; letI := hq; letI := hf
      OneStepDevissageAt k ((Scheme.Modules.pullback U.toBase).obj F) U.point) :
    fiberSupportDim k ((Scheme.Modules.pullback U.toBase).obj F) U.point ≤
      fiberSupportDim f F x := by
  let : LocallyOfFiniteType k := hk
  let : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent := hq
  let : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType := hf
  have hmem : U.point ∈ SheafOfModules.supp ((Scheme.Modules.pullback U.toBase).obj F) :=
    (mem_supp_fiber_iff_mem_supp k ((Scheme.Modules.pullback U.toBase).obj F) U.point).1
      D.mem_fiber_support
  obtain ⟨hx, hu, heq⟩ :=
    topologicalKrullDimAt_fiberSupport_eq_of_etaleSquare f F x U V k hsq hmem
  exact le_trans (le_of_eq (D.dimension.symm.trans heq))
    (topologicalKrullDimAt_le_topologicalKrullDim _)

/-! ### The cokernel of the free-module map -/

/-- The cokernel of a map from a free module into the direct image of the module of a one-step
dévissage is quasi-coherent and of finite type: all four schemes of a one-step dévissage are
affine and its finite morphism is affine, so the direct image is quasi-coherent of finite type,
the free module is quasi-coherent, and the cokernel of a map of quasi-coherent modules is
quasi-coherent, of finite type because it is a quotient of one. -/
lemma isQuasicoherent_isFiniteType_cokernel {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {F : X.Modules} [F.IsQuasicoherent] [F.IsFiniteType] {s : S}
    (E : OneStepDevissage f F s) {r : ℕ}
    (α : SheafOfModules.free (R := E.Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
      (Scheme.Modules.pushforward E.π).obj E.G) :
    (cokernel α).IsQuasicoherent ∧ (cokernel α).IsFiniteType := by
  have : IsAffine E.Y := E.affine_Y
  have : IsAffine E.Z := E.affine_Z
  have : E.G.IsQuasicoherent := E.quasi_coherent_G
  have : E.G.IsFiniteType := E.finite_type_G
  have : IsFinite E.π := E.finite
  have : IsAffineHom E.π := E.finite.toIsAffineHom
  have hpushq : ((Scheme.Modules.pushforward E.π).obj E.G).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom E.π E.G
  have hpusht : ((Scheme.Modules.pushforward E.π).obj E.G).IsFiniteType :=
    Stacks.AlgebraicGeometry.PushforwardCoherent.isFiniteType_pushforward_of_isAffine E.π
      E.π.finite_appTop E.G
  have hfreeq :
      (SheafOfModules.free (R := E.Y.ringCatSheaf) (ULift.{u} (Fin r))).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free (X := E.Y) _
  have := hpushq
  have := hpusht
  have := hfreeq
  have hepi : Epi (cokernel.π α) := coequalizer.π_epi
  refine ⟨Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel α, ?_⟩
  exact @Stacks.SheafOfModules.isFiniteType_of_epi'.{u} _ _ _ _ _ _ _ _ _ (cokernel.π α)
    inferInstance hepi

/-! ### The transported stage -/

/-- The inverse image of a quasi-coherent module of finite type is quasi-coherent and of finite
type. -/
private lemma isQuasicoherent_isFiniteType_pullback {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    ((Scheme.Modules.pullback g).obj M).IsQuasicoherent ∧
      ((Scheme.Modules.pullback g).obj M).IsFiniteType :=
  ⟨Stacks.Modules.isQuasicoherent_pullback g M ‹_›,
    SheafOfModules.pullback_isFiniteType g.toLRSHom.toShHom M⟩

/-- The source's proof of Stacks 05HR from the point at which Stacks 05HE has been applied: the
base change of the free-module map along the transported one-step dévissage is again invertible
over the generic point of the new distinguished fibre, its cokernel is the inverse image of the
old cokernel, and Stacks 05HK carries the complete dévissage of that cokernel to the fibre
product `X₁` of the two neighbourhoods. That is the situation (a)–(d) that
`AlgebraicGeometry.exists_etaleNeighborhood_completeDevissageAt_of_cokernelDevissage` consumes.

The invertibility over the generic point is the one new ingredient: the comparison morphism of
the two distinguished fibres is étale, hence open, and both fibres are irreducible, so it
carries the generic point of the new fibre to the generic point of the old one
(`IsGenericPoint.map_eq_of_isOpenMap`), which is exactly the hypothesis of
`AlgebraicGeometry.isIso_baseChangedAlpha_of_map_eq`. -/
private theorem glue_of_transportedDevissage
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (x : X) (D : OneStepDevissageAt f F x) (r : ℕ)
    (α : SheafOfModules.free (R := D.toOneStepDevissage.Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
      (Scheme.Modules.pushforward D.toOneStepDevissage.π).obj D.toOneStepDevissage.G)
    (hα : IsIso ((Scheme.Modules.pullback (D.toOneStepDevissage.Y.fromSpecResidueField
      (D.toOneStepDevissage.g.fiberι (f x)
        D.toOneStepDevissage.fiberGenericPoint))).map α))
    (C : D.toOneStepDevissage.Y.Modules) (eC : C ≅ cokernel α)
    (U₁ : EtaleNeighborhood D.toOneStepDevissage.Y D.y) (V₀ : EtaleNeighborhood S (f x))
    (h₁ : U₁.scheme ⟶ V₀.scheme)
    (hsq₁ : U₁.toBase ≫ D.toOneStepDevissage.g = h₁ ≫ V₀.toBase)
    (hpt₁ : h₁ U₁.point = V₀.point)
    (W : EtaleNeighborhood V₀.scheme V₀.point) (hW : W.IsElementary)
    (A : EtaleNeighborhood X x) (b : A.scheme ⟶ W.scheme) (hbpt : b A.point = W.point)
    (hl : LocallyOfFiniteType b)
    (hqA : ((Scheme.Modules.pullback A.toBase).obj F).IsQuasicoherent)
    (htA : ((Scheme.Modules.pullback A.toBase).obj F).IsFiniteType)
    (hl₁ : LocallyOfFiniteType h₁)
    (hq₁ : ((Scheme.Modules.pullback U₁.toBase).obj C).IsQuasicoherent)
    (hf₁ : ((Scheme.Modules.pullback U₁.toBase).obj C).IsFiniteType)
    (D'' : @OneStepDevissageAt A.scheme W.scheme b ((Scheme.Modules.pullback A.toBase).obj F)
      A.point hl hqA htA)
    {p : D''.toOneStepDevissage.Z ⟶ D.toOneStepDevissage.Z}
    (j : D''.toOneStepDevissage.Y ⟶ pullback h₁ W.toBase) (hj : IsOpenImmersion j)
    (hjg : D''.toOneStepDevissage.g = j ≫ pullback.snd h₁ W.toBase)
    (hjy : (j ≫ pullback.fst h₁ W.toBase) D''.y = U₁.point)
    (hz : IsPullback p D''.toOneStepDevissage.π D.toOneStepDevissage.π
      (j ≫ pullback.fst h₁ W.toBase ≫ U₁.toBase))
    (hG : D''.toOneStepDevissage.G = (Scheme.Modules.pullback p).obj D.toOneStepDevissage.G)
    (hC : Nonempty (@CompleteDevissageAt U₁.scheme V₀.scheme h₁
      ((Scheme.Modules.pullback U₁.toBase).obj C) U₁.point hl₁ hq₁ hf₁)) :
    @HasEtaleNeighborhoodCompleteDevissageAt A.scheme W.scheme b hl
      ((Scheme.Modules.pullback A.toBase).obj F) hqA htA A.point := by
  classical
  let : IsOpenImmersion j := hj
  let : LocallyOfFiniteType b := hl
  let : ((Scheme.Modules.pullback A.toBase).obj F).IsQuasicoherent := hqA
  let : ((Scheme.Modules.pullback A.toBase).obj F).IsFiniteType := htA
  let : LocallyOfFiniteType h₁ := hl₁
  let : ((Scheme.Modules.pullback U₁.toBase).obj C).IsQuasicoherent := hq₁
  let : ((Scheme.Modules.pullback U₁.toBase).obj C).IsFiniteType := hf₁
  have hXpb : IsPullback (pullback.fst h₁ W.toBase) (pullback.snd h₁ W.toBase) h₁ W.toBase :=
    IsPullback.of_hasPullback h₁ W.toBase
  have hl₂ : LocallyOfFiniteType (pullback.snd h₁ W.toBase) :=
    MorphismProperty.of_isPullback hXpb (P := @LocallyOfFiniteType) inferInstance
  let : LocallyOfFiniteType (pullback.snd h₁ W.toBase) := hl₂
  obtain ⟨hq₂, ht₂⟩ :=
    isQuasicoherent_isFiniteType_pullback (pullback.fst h₁ W.toBase)
      ((Scheme.Modules.pullback U₁.toBase).obj C)
  let := hq₂
  let := ht₂
  -- the stage the one-step dévissage and `α` define, and the base change of its free-module map.
  let stage : DevissageStage f F (f x) := DevissageStage.ofOneStepDevissageAt D r α hα
  let α'' := baseChangedAlpha stage D''.toOneStepDevissage hz hG
  have hβpt : (W.toBase ≫ V₀.toBase) (b A.point) = f x := by
    show V₀.toBase (W.toBase (b A.point)) = f x
    rw [hbpt, W.map_point, V₀.map_point]
  have hcomm' : (j ≫ pullback.fst h₁ W.toBase ≫ U₁.toBase) ≫ D.toOneStepDevissage.g =
      D''.toOneStepDevissage.g ≫ W.toBase ≫ V₀.toBase := by
    rw [hjg]
    simp only [Category.assoc, hsq₁, reassoc_of% hXpb.w]
  let ψ := fiberMap D''.toOneStepDevissage.g (j ≫ pullback.fst h₁ W.toBase ≫ U₁.toBase)
      (W.toBase ≫ V₀.toBase) D.toOneStepDevissage.g hcomm' (b A.point) ≫
    (fiberCongr D.toOneStepDevissage.g hβpt).hom
  have hψ : Etale ψ := etale_fiberMap_fiberCongr _ _ _ _ hcomm' _ hβpt
  have hgi₂ : GeometricallyIrreducible D''.toOneStepDevissage.g :=
    D''.toOneStepDevissage.geometrically_irreducible
  have hgi₁ : GeometricallyIrreducible D.toOneStepDevissage.g :=
    D.toOneStepDevissage.geometrically_irreducible
  have hηmap : ψ D''.toOneStepDevissage.fiberGenericPoint =
      D.toOneStepDevissage.fiberGenericPoint :=
    IsGenericPoint.map_eq_of_isOpenMap ψ.continuous ψ.isOpenMap
      D''.toOneStepDevissage.isGenericPoint_fiberGenericPoint
      D.toOneStepDevissage.isGenericPoint_fiberGenericPoint
  have hψcomp : ψ ≫ D.toOneStepDevissage.g.fiberι (f x) =
      D''.toOneStepDevissage.g.fiberι (b A.point) ≫
        (j ≫ pullback.fst h₁ W.toBase ≫ U₁.toBase) :=
    fiberMap_fiberCongr_comp_fiberι _ _ _ _ hcomm' _ hβpt
  have hη : (j ≫ pullback.fst h₁ W.toBase ≫ U₁.toBase)
        (D''.toOneStepDevissage.g.fiberι (b A.point)
          D''.toOneStepDevissage.fiberGenericPoint) =
      D.toOneStepDevissage.g.fiberι (f x) D.toOneStepDevissage.fiberGenericPoint := by
    rw [← hηmap]
    exact (congrArg (fun m : D''.toOneStepDevissage.g.fiber (b A.point) ⟶
      D.toOneStepDevissage.Y => m D''.toOneStepDevissage.fiberGenericPoint) hψcomp).symm
  have hα'' : IsIso ((Scheme.Modules.pullback (D''.toOneStepDevissage.Y.fromSpecResidueField
      (D''.toOneStepDevissage.g.fiberι (b A.point)
        D''.toOneStepDevissage.fiberGenericPoint))).map α'') :=
    isIso_baseChangedAlpha_of_map_eq stage D''.toOneStepDevissage hz hG hη
  -- the cokernel of the base-changed map is the inverse image of the old cokernel.
  have ecok : (Scheme.Modules.pullback (j ≫ pullback.fst h₁ W.toBase ≫ U₁.toBase)).obj
      (cokernel α) ≅ cokernel α'' :=
    cokernelIsoOfAlphaComparison (D := stage)
      (D' := DevissageStage.ofOneStepDevissageAt D'' r α'' hα'') hz hG rfl
      (baseChangedAlpha_comp stage D''.toOneStepDevissage hz hG)
  have eF₁ : (Scheme.Modules.pullback j).obj
      ((Scheme.Modules.pullback (pullback.fst h₁ W.toBase)).obj
        ((Scheme.Modules.pullback U₁.toBase).obj C)) ≅ cokernel α'' := by
    refine Iso.trans ?_ ecok
    refine Iso.trans ((Scheme.Modules.pullback j).mapIso
      ((Scheme.Modules.pullbackComp (pullback.fst h₁ W.toBase) U₁.toBase).app C)) ?_
    refine Iso.trans ((Scheme.Modules.pullbackComp j
      (pullback.fst h₁ W.toBase ≫ U₁.toBase)).app C) ?_
    exact (Scheme.Modules.pullback (j ≫ pullback.fst h₁ W.toBase ≫ U₁.toBase)).mapIso eC
  -- Stacks 05HK: base-change the complete dévissage of the cokernel to the fibre product.
  have hjy' : pullback.fst h₁ W.toBase (j D''.y) = U₁.point := by simpa using hjy
  have hf₁pt : pullback.snd h₁ W.toBase (j D''.y) = W.point := by
    have h4 := congrArg (fun m : D''.toOneStepDevissage.Y ⟶ W.scheme => m D''.y) hjg
    simp only [Scheme.Hom.comp_apply] at h4
    rw [← h4]
    exact D''.g_y.trans hbpt
  have hWaff : IsAffine W.scheme := D''.toOneStepDevissage.affine_S
  let : IsAffine W.scheme := hWaff
  have hs : W.toBase (pullback.snd h₁ W.toBase (j D''.y)) = h₁ U₁.point := by
    rw [hf₁pt, W.map_point, hpt₁]
  have hres : IsIso (W.toBase.residueFieldMap (pullback.snd h₁ W.toBase (j D''.y))) := by
    rw [Scheme.Hom.isIso_residueFieldMap_congr W.toBase hf₁pt]
    exact (EtaleNeighborhood.isElementary_iff W).mp hW
  have hCD : Nonempty (CompleteDevissageAt (pullback.snd h₁ W.toBase)
      ((Scheme.Modules.pullback (pullback.fst h₁ W.toBase)).obj
        ((Scheme.Modules.pullback U₁.toBase).obj C)) (j D''.y)) := by
    obtain ⟨CD⟩ := hC
    cases CD with
    | empty hzero =>
      exact ⟨CompleteDevissageAt.empty
        ((Scheme.Modules.pullback (pullback.fst h₁ W.toBase)).map_isZero hzero)⟩
    | nonempty data =>
      obtain ⟨data', hbc⟩ := exists_completeDevissage_baseChange
        (s' := pullback.snd h₁ W.toBase (j D''.y)) hs data.toNonemptyCompleteDevissage
        (pullback.fst h₁ W.toBase) hXpb (Iso.refl _)
      obtain ⟨DAt', -, -⟩ := exists_completeDevissageAt_baseChange (x' := j D''.y) hs hres data
        (pullback.fst h₁ W.toBase) hXpb (Iso.refl _) hjy' data' hbc
      exact ⟨CompleteDevissageAt.nonempty DAt'⟩
  exact exists_etaleNeighborhood_completeDevissageAt_of_cokernelDevissage b
    ((Scheme.Modules.pullback A.toBase).obj F) A.point D'' r α'' hα''
    (pullback.snd h₁ W.toBase) _ hl₂ hq₂ ht₂ j hj hjg.symm ⟨eF₁⟩ hCD

/-! ### The induction step, given a one-step dévissage -/

/-- The induction step of Stacks 05HR once Stacks 05H6 and Stacks 05HF have done their work:
given a one-step dévissage of `F/X/S` at `x`, a generically invertible map `α` out of a free
module, and the conclusion of Stacks 05HR for the cokernel of `α` on the smooth scheme, Stacks
05HE transports the one-step dévissage through the two neighbourhoods the latter provides, and
`AlgebraicGeometry.glue_of_transportedDevissage` finishes. -/
private theorem glue_of_oneStepDevissage
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (x : X) (D : OneStepDevissageAt f F x) (r : ℕ)
    (α : SheafOfModules.free (R := D.toOneStepDevissage.Y.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
      (Scheme.Modules.pushforward D.toOneStepDevissage.π).obj D.toOneStepDevissage.G)
    (hα : IsIso ((Scheme.Modules.pullback (D.toOneStepDevissage.Y.fromSpecResidueField
      (D.toOneStepDevissage.g.fiberι (f x)
        D.toOneStepDevissage.fiberGenericPoint))).map α))
    (C : D.toOneStepDevissage.Y.Modules) (eC : C ≅ cokernel α)
    (hgL : LocallyOfFiniteType D.toOneStepDevissage.g) (hCq : C.IsQuasicoherent)
    (hCt : C.IsFiniteType)
    (hrec : @HasEtaleNeighborhoodCompleteDevissageAt D.toOneStepDevissage.Y S
      D.toOneStepDevissage.g hgL C hCq hCt D.y) :
    HasEtaleNeighborhoodCompleteDevissageAt f F x := by
  classical
  obtain ⟨U₁, V₁, h₁, hU₁, hV₁, hsq₁, hpt₁, hl₁, hq₁, hf₁, hC⟩ := hrec
  -- the neighbourhood of the base point, re-indexed at the image of `x`.
  let V₀ : EtaleNeighborhood S (f x) :=
    { scheme := V₁.scheme
      point := V₁.point
      toBase := V₁.toBase
      map_point := V₁.map_point.trans D.g_y }
  have hV₀ : V₀.IsElementary :=
    (EtaleNeighborhood.isElementary_iff V₀).mpr ((EtaleNeighborhood.isElementary_iff V₁).mp hV₁)
  -- Stacks 05HE: transport the one-step dévissage through the two neighbourhoods.
  obtain ⟨W, hW, A, hA, b, hbpt, hbsq, hl, hqA, htA, D', j, p, hj, hjg, hjy, -, -, -,
      hπpb, ⟨eG⟩⟩ :=
    exists_oneStepDevissageAt_of_etaleNeighborhood f F x D V₀ hV₀ U₁ hU₁ h₁ hsq₁ hpt₁
  refine exists_etaleNeighborhood_completeDevissageAt_of_etaleNeighborhood f F x A
    (V₀.comp W) b hA (hV₀.comp hW) hbsq hbpt hl hqA htA ?_
  -- replace the module on the closed subscheme of the transported dévissage by the inverse
  -- image of the old one, so that the comparison of the two is an equality.
  have := D.toOneStepDevissage.quasi_coherent_G
  have := D.toOneStepDevissage.finite_type_G
  obtain ⟨hpGq, hpGt⟩ := isQuasicoherent_isFiniteType_pullback p D.toOneStepDevissage.G
  exact glue_of_transportedDevissage f F x D r α hα C eC U₁ V₀ h₁ hsq₁ hpt₁ W hW A b hbpt
    hl hqA htA hl₁ hq₁ hf₁ (D'.ofClosedModuleIso _ hpGq hpGt eG.symm) j hj hjg hjy hπpb rfl hC

/-! ### The induction -/

/-- One step of the induction of **Stacks Project, Tag 05HR**: the conclusion holds at `x` as
soon as it holds at every situation of strictly smaller fibre-support dimension.

If `x` is not in the support of `F` the empty dévissage on the complement of the support serves.
Otherwise Stacks 05H6 produces a one-step dévissage after elementary étale neighbourhoods, the
conclusion is local for those, and Stacks 05HF produces the generically invertible map out of a
free module whose cokernel has strictly smaller fibre-support dimension — strictly smaller than
`d`, because the fibre-support dimension does not grow along the neighbourhoods. -/
private theorem step_hasEtaleNeighborhoodCompleteDevissageAt (d : WithBot ℕ∞)
    (ih : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
      (hl : LocallyOfFiniteType f) (hq : F.IsQuasicoherent) (hf : F.IsFiniteType),
      fiberSupportDim f F x < d →
        @HasEtaleNeighborhoodCompleteDevissageAt X S f hl F hq hf x)
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (x : X) (hd : fiberSupportDim f F x = d) :
    HasEtaleNeighborhoodCompleteDevissageAt f F x := by
  classical
  by_cases hx : x ∈ SheafOfModules.supp F
  swap
  · exact exists_etaleNeighborhood_completeDevissageAt_of_notMem_supp f F x hx
  obtain ⟨U, V, k, hU, hV, hsq, hpt, hft, hq, hf, ⟨D⟩⟩ :=
    exists_etaleNeighborhood_oneStepDevissageAt f F x
      ((mem_supp_fiber_iff_mem_supp f F x).2 hx)
  have hdle : fiberSupportDim k ((Scheme.Modules.pullback U.toBase).obj F) U.point ≤ d :=
    (fiberSupportDim_le_of_etaleSquare f F x U V k hsq hft hq hf D).trans (le_of_eq hd)
  refine exists_etaleNeighborhood_completeDevissageAt_of_etaleNeighborhood f F x U V k hU hV
    hsq hpt hft hq hf ?_
  let : LocallyOfFiniteType k := hft
  let : ((Scheme.Modules.pullback U.toBase).obj F).IsQuasicoherent := hq
  let : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType := hf
  obtain ⟨r, -, α, hα⟩ := exists_freeMap_isIso_genericFiber k
    ((Scheme.Modules.pullback U.toBase).obj F) (k U.point) D.toOneStepDevissage
    D.toOneStepDevissage.fiberGenericPoint
  obtain ⟨hcq, hct⟩ := isQuasicoherent_isFiniteType_cokernel D.toOneStepDevissage α
  have hsm : Smooth D.toOneStepDevissage.g := D.toOneStepDevissage.smooth
  let : Smooth D.toOneStepDevissage.g := hsm
  have hgL : LocallyOfFiniteType D.toOneStepDevissage.g := inferInstance
  have hlt := dim_support_cokernel_fiber_lt k ((Scheme.Modules.pullback U.toBase).obj F)
    (k U.point) D.toOneStepDevissage D.toOneStepDevissage.fiberGenericPoint α hα
  refine glue_of_oneStepDevissage k ((Scheme.Modules.pullback U.toBase).obj F) U.point D r
    α hα (cokernel α) (Iso.refl _) hgL hcq hct
    (ih D.toOneStepDevissage.g (cokernel α) D.y hgL hcq hct ?_)
  rw [fiberSupportDim_eq D.toOneStepDevissage.g (cokernel α) D.y D.g_y]
  exact lt_of_lt_of_le hlt hdle

/-- **Stacks Project, Tag 05HR.** A finite-type quasi-coherent module on a scheme locally of
finite type over `S` acquires a complete dévissage at any chosen point after elementary étale
neighbourhoods of that point and of its image.

The induction is a well-founded recursion on `AlgebraicGeometry.fiberSupportDim`, which takes
values in the well-founded order `WithBot ℕ∞`. -/
@[stacks 05HR]
theorem hasEtaleNeighborhoodCompleteDevissageAt {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X) :
    HasEtaleNeighborhoodCompleteDevissageAt f F x := by
  have key : ∀ d : WithBot ℕ∞, ∀ {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
      (hl : LocallyOfFiniteType f) (hq : F.IsQuasicoherent) (hf : F.IsFiniteType),
      fiberSupportDim f F x = d → @HasEtaleNeighborhoodCompleteDevissageAt X S f hl F hq hf x := by
    intro d
    induction d using (wellFounded_lt (α := WithBot ℕ∞)).induction with
    | _ d ih =>
      exact fun g M y hl hq hft hdd =>
        @step_hasEtaleNeighborhoodCompleteDevissageAt d
          (fun c N z hl' hq' hf' hlt => ih _ hlt c N z hl' hq' hf' rfl) _ _ g hl M hq hft y hdd
  exact key _ f F x inferInstance inferInstance inferInstance rfl

/-! ### Combining elementary étale neighbourhoods -/

/-- The residue field map of an étale neighbourhood commutes with the canonical morphisms from
the spectra of the residue fields. -/
private lemma specMap_residueFieldMap_comp {S : Scheme.{u}} {s : S}
    (U : EtaleNeighborhood S s) :
    Spec.map U.residueFieldMap ≫ S.fromSpecResidueField s =
      U.scheme.fromSpecResidueField U.point ≫ U.toBase := by
  simp [EtaleNeighborhood.residueFieldMap, Spec.map_comp]

/-- An étale neighbourhood admitting a section `Spec κ(s) ⟶ U` over `S` through the
distinguished point is elementary: the section exhibits a retraction of the residue field
extension, which is therefore trivial. -/
private lemma isElementary_of_section {S : Scheme.{u}} {s : S}
    (U : EtaleNeighborhood S s) (a : Spec (S.residueField s) ⟶ U.scheme)
    (ha : a ≫ U.toBase = S.fromSpecResidueField s) (pt : Spec (S.residueField s))
    (hp : a pt = U.point) : U.IsElementary := by
  obtain rfl : pt = IsLocalRing.closedPoint (S.residueField s) :=
    Subsingleton.elim (α := PrimeSpectrum _) _ _
  let e := Scheme.SpecToEquivOfField (S.residueField s) U.scheme a
  have he : e.1 = U.point := hp
  let t : U.scheme.residueField U.point ⟶ S.residueField s :=
    (U.scheme.residueFieldCongr he.symm).hom ≫ e.2
  have hat : Spec.map t ≫ U.scheme.fromSpecResidueField U.point = a := by
    dsimp only [t]
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
    exact (Scheme.SpecToEquivOfField (S.residueField s) U.scheme).symm_apply_apply a
  have ht : U.residueFieldMap ≫ t = 𝟙 _ := by
    apply Spec.map_injective
    apply (cancel_mono (S.fromSpecResidueField s)).mp
    simp only [Spec.map_comp, Spec.map_id, Category.id_comp, Category.assoc]
    rw [specMap_residueFieldMap_comp, ← Category.assoc, hat, ha]
  refine ⟨⟨t, ht, ?_⟩⟩
  ext y
  exact t.hom.injective
    (congrArg (fun r : S.residueField s ⟶ S.residueField s => r.hom (t.hom y)) ht)

/-- Two elementary étale neighbourhoods of `(S, s)` are dominated by a third one, namely their
fibre product over `S` at the point cut out by the two canonical sections. -/
private lemma exists_isElementary_hom_hom {S : Scheme.{u}} {s : S}
    (U V : EtaleNeighborhood S s) (hU : U.IsElementary) (hV : V.IsElementary) :
    ∃ W : EtaleNeighborhood S s, W.IsElementary ∧ Nonempty (W ⟶ U) ∧ Nonempty (W ⟶ V) := by
  have : IsIso U.residueFieldMap := hU
  have : IsIso V.residueFieldMap := hV
  obtain ⟨pt⟩ : Nonempty ↥(Spec (S.residueField s)) :=
    ⟨IsLocalRing.closedPoint (S.residueField s)⟩
  have ha : (Spec.map (inv U.residueFieldMap) ≫
      U.scheme.fromSpecResidueField U.point) ≫ U.toBase = S.fromSpecResidueField s := by
    rw [Category.assoc, ← specMap_residueFieldMap_comp, ← Spec.map_comp_assoc,
      IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  have hb : (Spec.map (inv V.residueFieldMap) ≫
      V.scheme.fromSpecResidueField V.point) ≫ V.toBase = S.fromSpecResidueField s := by
    rw [Category.assoc, ← specMap_residueFieldMap_comp, ← Spec.map_comp_assoc,
      IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  have hcU := pullback.lift_fst (f := U.toBase) (g := V.toBase) _ _ (ha.trans hb.symm)
  have hcV := pullback.lift_snd (f := U.toBase) (g := V.toBase) _ _ (ha.trans hb.symm)
  have hpU : pullback.fst U.toBase V.toBase
      (pullback.lift _ _ (ha.trans hb.symm) pt) = U.point := by
    rw [← Scheme.Hom.comp_apply, hcU, Scheme.Hom.comp_apply,
      Scheme.fromSpecResidueField_apply]
  have hpV : pullback.snd U.toBase V.toBase
      (pullback.lift _ _ (ha.trans hb.symm) pt) = V.point := by
    rw [← Scheme.Hom.comp_apply, hcV, Scheme.Hom.comp_apply,
      Scheme.fromSpecResidueField_apply]
  refine ⟨{ scheme := pullback U.toBase V.toBase
            point := pullback.lift _ _ (ha.trans hb.symm) pt
            toBase := pullback.fst U.toBase V.toBase ≫ U.toBase
            map_point := by rw [Scheme.Hom.comp_apply, hpU]; exact U.map_point },
    isElementary_of_section _ (pullback.lift _ _ (ha.trans hb.symm)) ?_ pt rfl,
    ⟨⟨pullback.fst _ _, rfl, hpU⟩⟩, ⟨⟨pullback.snd _ _, pullback.condition.symm, hpV⟩⟩⟩
  rw [← Category.assoc, hcU, ha]

/-- Finitely many elementary étale neighbourhoods of `(S, s)` are dominated by a single one: the
fibre product of them all over `S`. This is the `S' = S'₁ ×_S … ×_S S'ₙ` of the source's proof of
Stacks 05HU. -/
private lemma exists_isElementary_forall_hom {S : Scheme.{u}} {s : S} {n : ℕ}
    (V : Fin n → EtaleNeighborhood S s) (hV : ∀ i, (V i).IsElementary) :
    ∃ W : EtaleNeighborhood S s, W.IsElementary ∧ ∀ i, Nonempty (W ⟶ V i) := by
  induction n with
  | zero => exact ⟨.self S s, EtaleNeighborhood.isElementary_self S s, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨W, hW, a⟩ := ih (fun i => V i.succ) fun i => hV i.succ
    obtain ⟨W', hW', ⟨b⟩, ⟨c⟩⟩ := exists_isElementary_hom_hom W (V 0) hW (hV 0)
    exact ⟨W', hW', Fin.cases ⟨c⟩ fun i => ⟨b ≫ (a i).some⟩⟩

/-- An elementary étale neighbourhood is dominated by an *affine* elementary étale
neighbourhood, obtained by restricting it to an affine open neighbourhood of its distinguished
point. Affineness of the new base is what the base change of a complete dévissage,
Stacks 05HJ, requires. -/
private lemma exists_isElementary_isAffine_hom {S : Scheme.{u}} {s : S}
    (U : EtaleNeighborhood S s) (hU : U.IsElementary) :
    ∃ V : EtaleNeighborhood S s, V.IsElementary ∧ IsAffine V.scheme ∧ Nonempty (V ⟶ U) := by
  obtain ⟨A, hA, hp, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show U.point ∈ (⊤ : U.scheme.Opens) from trivial)
  have hB := EtaleNeighborhood.isElementary_ofEtale_of_isOpenImmersion A.ι
    (⟨U.point, hp⟩ : A.toScheme)
  exact ⟨U.comp (EtaleNeighborhood.ofEtale A.ι (⟨U.point, hp⟩ : A.toScheme)), hU.comp hB, hA,
    ⟨⟨A.ι, rfl, rfl⟩⟩⟩

/-! ### Fibres over an elementary étale neighbourhood of the base point -/

/-- An isomorphism of schemes is injective on points. -/
private lemma injective_of_isIso {A B : Scheme.{u}} (m : A ⟶ B) [IsIso m] :
    Function.Injective m := (Scheme.homeoOfIso (asIso m)).injective

/-- The fibre of a base change `X ×_S T ⟶ T` over a point `t` agrees with the fibre of `X ⟶ S`
over its image, provided `T ⟶ S` induces an isomorphism of residue fields at `t`. This is the
identification `X_s = (X_{S'})_{s'}` of Stacks 05HU. -/
private lemma isIso_fiberMap_pullback {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (t : T)
    (hres : IsIso (g.residueFieldMap t)) :
    IsIso (fiberMap (pullback.snd f g) (pullback.fst f g) g f pullback.condition t) := by
  have := hres
  have hspec : IsIso (Spec.map (g.residueFieldMap t)) := inferInstance
  exact (isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f g) t).isIso_fst_of_isIso hspec

/-- Over a point at which the base morphism induces an isomorphism of residue fields, two points
of a base change lying in the same fibre and with the same image in `X` are equal. -/
private lemma eq_of_fst_eq_of_mem_fiber {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (t : T)
    (hres : IsIso (g.residueFieldMap t)) {z w : ↥(pullback f g)}
    (hz : pullback.snd f g z = t) (hw : pullback.snd f g w = t)
    (he : pullback.fst f g z = pullback.fst f g w) : z = w := by
  have hiso := isIso_fiberMap_pullback f g t hres
  have hmι := fiberMap_comp_fiberι (pullback.snd f g) (pullback.fst f g) g f
    pullback.condition t
  have key : ((pullback.snd f g).fiberHomeo t).symm ⟨z, hz⟩ =
      ((pullback.snd f g).fiberHomeo t).symm ⟨w, hw⟩ := by
    refine injective_of_isIso
      (fiberMap (pullback.snd f g) (pullback.fst f g) g f pullback.condition t)
      (f.fiberι_injective (g t) ?_)
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hmι, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply, Scheme.Hom.fiberι_fiberHomeo_symm,
      Scheme.Hom.fiberι_fiberHomeo_symm]
    exact he
  have h₂ := congrArg ((pullback.snd f g).fiberι t) key
  rwa [Scheme.Hom.fiberι_fiberHomeo_symm, Scheme.Hom.fiberι_fiberHomeo_symm] at h₂

/-- In a commutative square with étale vertical arrows whose base morphism induces an
isomorphism of residue fields at `t`, the image of the fibre over `t` is open in the fibre over
the image of `t`: the induced morphism of fibres is étale, hence open. -/
private lemma isOpen_fiber_image {A X T S : Scheme.{u}} (f : X ⟶ S) (g : A ⟶ X) (h : A ⟶ T)
    (b : T ⟶ S) [Etale g] [Etale b] (hsq : g ≫ f = h ≫ b) (t : T)
    (hres : IsIso (b.residueFieldMap t)) (s : S) (hbt : b t = s) :
    IsOpen {z : f.fiber s | ∃ y : A, h y = t ∧ g y = f.fiberι s z} := by
  subst hbt
  have := hres
  have := etale_fiberMap h g b f hsq t
  have hmι := fiberMap_comp_fiberι h g b f hsq t
  have hr : Set.range (fiberMap h g b f hsq t) =
      {z : f.fiber (b t) | ∃ y : A, h y = t ∧ g y = f.fiberι (b t) z} := by
    ext z
    refine ⟨?_, ?_⟩
    · rintro ⟨w, rfl⟩
      refine ⟨h.fiberι t w, (h.fiberHomeo t w).property, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hmι, Scheme.Hom.comp_apply]
    · rintro ⟨w, hw, hgw⟩
      refine ⟨(h.fiberHomeo t).symm ⟨w, hw⟩, f.fiberι_injective (b t) ?_⟩
      rw [← Scheme.Hom.comp_apply, hmι, Scheme.Hom.comp_apply,
        Scheme.Hom.fiberι_fiberHomeo_symm]
      exact hgw
  rw [← hr]
  exact (Scheme.Hom.isOpenMap (fiberMap h g b f hsq t)).isOpen_range

/-! ### Charts carrying a complete dévissage -/

/-- A complete dévissage of `F/X/S` at a point is in particular one over the image of that
point. -/
private def completeDevissageOfAt {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {x : X}
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : CompleteDevissageAt f F x) : CompleteDevissage f F (f x) :=
  match D with
  | .empty hzero => .empty hzero
  | .nonempty data => .nonempty data.toNonemptyCompleteDevissage

/-- The datum Stacks 05HR provides at one point of the fibre `X_s`: an elementary étale
neighbourhood `(S', s')` of `(S, s)`, a scheme `Y` étale over `X` and over `S'` compatibly, and a
complete dévissage over `s'` of the pullback of `F` to `Y`. -/
private structure DevissageChart {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (s : S) where
  /-- The étale neighbourhood of the base point. -/
  base : EtaleNeighborhood S s
  /-- It is elementary. -/
  elementary : base.IsElementary
  /-- The scheme carrying the dévissage. -/
  Y : Scheme.{u}
  /-- Its étale morphism to `X`. -/
  g : Y ⟶ X
  /-- Its structure morphism to the neighbourhood of the base point. -/
  h : Y ⟶ base.scheme
  [etale_g : Etale g]
  /-- The two morphisms are compatible with the structure morphisms. -/
  square : g ≫ f = h ≫ base.toBase
  [locallyOfFiniteType_h : LocallyOfFiniteType h]
  [quasicoherent : ((Scheme.Modules.pullback g).obj F).IsQuasicoherent]
  [finiteType : ((Scheme.Modules.pullback g).obj F).IsFiniteType]
  /-- The pullback of the module to `Y` has a complete dévissage over the distinguished point of
  the neighbourhood. -/
  devissage : Nonempty (@CompleteDevissage Y base.scheme h
    ((Scheme.Modules.pullback g).obj F) base.point locallyOfFiniteType_h quasicoherent
    finiteType)

attribute [instance] DevissageChart.etale_g DevissageChart.locallyOfFiniteType_h
  DevissageChart.quasicoherent DevissageChart.finiteType

/-- Stacks 05HR, repackaged: every point of the fibre `X_s` lies in the image of a chart. -/
private lemma exists_devissageChart {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (s : S) (x : f.fiber s) :
    ∃ (C : DevissageChart f F s) (y : C.Y),
      C.h y = C.base.point ∧ C.g y = f.fiberι s x := by
  have hx : f (f.fiberι s x) = s := (f.fiberHomeo s x).property
  obtain ⟨U, V, k, -, hV, sq, hpt, hft, hq, ht, ⟨D⟩⟩ :=
    hasEtaleNeighborhoodCompleteDevissageAt f F (f.fiberι s x)
  have := hft
  have := hq
  have := ht
  have hV' : ({ V with map_point := V.map_point.trans hx } :
      EtaleNeighborhood S s).IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff] at hV ⊢
    exact hV
  refine ⟨{ base := { V with map_point := V.map_point.trans hx }, elementary := hV'
            Y := U.scheme, g := U.toBase, h := k, square := sq, devissage := ⟨?_⟩ },
    U.point, hpt, U.map_point⟩
  have hD := completeDevissageOfAt D
  rwa [hpt] at hD

/-- Finitely many charts suffice to cover the fibre `X_s`. The image of a chart is open in the
fibre, and the fibre of a finite-type morphism is quasi-compact. -/
private lemma exists_finite_devissageCharts {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (s : S) :
    ∃ (n : ℕ) (C : Fin n → DevissageChart f F s), ∀ z : f.fiber s,
      ∃ (i : Fin n) (y : (C i).Y),
        (C i).h y = (C i).base.point ∧ (C i).g y = f.fiberι s z := by
  classical
  choose C y hy hg using exists_devissageChart f F s
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : f.fiber s => {z : f.fiber s | ∃ w : (C x).Y,
      (C x).h w = (C x).base.point ∧ (C x).g w = f.fiberι s z})
    (fun x => isOpen_fiber_image f (C x).g (C x).h (C x).base.toBase (C x).square
      (C x).base.point
      (by rw [← EtaleNeighborhood.isElementary_iff]; exact (C x).elementary) s
      (C x).base.map_point)
    (fun z _ => Set.mem_iUnion.mpr ⟨z, y z, hy z, hg z⟩)
  obtain ⟨D, hD⟩ : ∃ D : Fin t.card → DevissageChart f F s,
      ∀ i, D i = C ↑(t.equivFin.symm i) := ⟨_, fun _ => rfl⟩
  refine ⟨t.card, D, fun z => ?_⟩
  obtain ⟨x, hx, hz⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ z))
  refine ⟨t.equivFin ⟨x, hx⟩, ?_⟩
  rw [hD, congrArg Subtype.val (t.equivFin.symm_apply_apply ⟨x, hx⟩)]
  exact hz

/-! ### Base change of a chart to a common elementary neighbourhood -/

/-- The base change `Yᵢ = Y ×_{S'ᵢ} S'` of a chart to a neighbourhood `S'` dominating its own,
regarded as a scheme over `X ×_S S'`. -/
private def chartBaseChangeMap {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {s : S}
    (C : DevissageChart f F s) (U : EtaleNeighborhood S s) (q : U ⟶ C.base) :
    pullback C.h q.hom ⟶ pullback f U.toBase :=
  pullback.lift (pullback.fst C.h q.hom ≫ C.g) (pullback.snd C.h q.hom) (by
    rw [Category.assoc, C.square, ← Category.assoc, pullback.condition, Category.assoc, q.over])

/-- The base change of a chart is compatible with the projections to `X`. -/
private lemma chartBaseChangeMap_fst {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {s : S}
    (C : DevissageChart f F s) (U : EtaleNeighborhood S s) (q : U ⟶ C.base) :
    chartBaseChangeMap C U q ≫ pullback.fst f U.toBase = pullback.fst C.h q.hom ≫ C.g :=
  pullback.lift_fst _ _ _

/-- The structure morphism of the base change of a chart over the new neighbourhood is the
second projection of the fibre product defining it. -/
private lemma chartBaseChangeMap_snd {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {s : S}
    (C : DevissageChart f F s) (U : EtaleNeighborhood S s) (q : U ⟶ C.base) :
    chartBaseChangeMap C U q ≫ pullback.snd f U.toBase = pullback.snd C.h q.hom :=
  pullback.lift_snd _ _ _

/-- The base change of a chart is étale over `X ×_S S'`. -/
private lemma etale_chartBaseChangeMap {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {s : S}
    (C : DevissageChart f F s) (U : EtaleNeighborhood S s) (q : U ⟶ C.base) :
    Etale (chartBaseChangeMap C U q) := by
  have h₁ : Etale (q.hom ≫ C.base.toBase) := by rw [q.over]; infer_instance
  have : Etale q.hom := Etale.of_comp q.hom C.base.toBase
  have : Etale (chartBaseChangeMap C U q ≫ pullback.fst f U.toBase) := by
    rw [chartBaseChangeMap_fst]; infer_instance
  exact Etale.of_comp _ (pullback.fst f U.toBase)

/-- The square exhibiting the base change of a chart as a base change of its structure
morphism. -/
private lemma isPullback_chartBaseChangeMap {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    {s : S} (C : DevissageChart f F s) (U : EtaleNeighborhood S s) (q : U ⟶ C.base) :
    IsPullback (pullback.fst C.h q.hom)
      (chartBaseChangeMap C U q ≫ pullback.snd f U.toBase) C.h q.hom := by
  rw [chartBaseChangeMap_snd]
  exact IsPullback.of_hasPullback _ _

/-- The pullback of `F` to the base change of a chart, computed either through the chart or
through `X ×_S S'`. -/
private def chartBaseChangeModuleIso {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {s : S}
    (C : DevissageChart f F s) (U : EtaleNeighborhood S s) (q : U ⟶ C.base) :
    (Scheme.Modules.pullback (pullback.fst C.h q.hom)).obj
        ((Scheme.Modules.pullback C.g).obj F) ≅
      (Scheme.Modules.pullback
        (chartBaseChangeMap C U q ≫ pullback.fst f U.toBase)).obj F :=
  (Scheme.Modules.pullbackComp (pullback.fst C.h q.hom) C.g).app F ≪≫
    (Scheme.Modules.pullbackCongr (chartBaseChangeMap_fst C U q).symm).app F

/-- Stacks 05HJ applied to a chart: the pullback of `F` to the base change of a chart along an
affine elementary étale neighbourhood dominating the chart's own has a complete dévissage over
the new distinguished point. -/
private lemma exists_chartBaseChange_completeDevissage {X S : Scheme.{u}} {f : X ⟶ S}
    {F : X.Modules} {s : S} (C : DevissageChart f F s) (U : EtaleNeighborhood S s)
    [IsAffine U.scheme] (q : U ⟶ C.base) :
    ∃ (hl : LocallyOfFiniteType (chartBaseChangeMap C U q ≫ pullback.snd f U.toBase))
      (hq : ((Scheme.Modules.pullback
        (chartBaseChangeMap C U q ≫ pullback.fst f U.toBase)).obj F).IsQuasicoherent)
      (ht : ((Scheme.Modules.pullback
        (chartBaseChangeMap C U q ≫ pullback.fst f U.toBase)).obj F).IsFiniteType),
      Nonempty (@CompleteDevissage _ _
        (chartBaseChangeMap C U q ≫ pullback.snd f U.toBase)
        ((Scheme.Modules.pullback
          (chartBaseChangeMap C U q ≫ pullback.fst f U.toBase)).obj F) U.point hl hq ht) := by
  have hX := isPullback_chartBaseChangeMap C U q
  have hl : LocallyOfFiniteType (chartBaseChangeMap C U q ≫ pullback.snd f U.toBase) :=
    MorphismProperty.of_isPullback hX (P := @LocallyOfFiniteType) C.locallyOfFiniteType_h
  obtain ⟨hq', ht'⟩ :=
    isQuasicoherent_isFiniteType_pullback (pullback.fst C.h q.hom)
      ((Scheme.Modules.pullback C.g).obj F)
  have hq : ((Scheme.Modules.pullback
      (chartBaseChangeMap C U q ≫ pullback.fst f U.toBase)).obj F).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_of_iso (chartBaseChangeModuleIso C U q) hq'
  have ht : ((Scheme.Modules.pullback
      (chartBaseChangeMap C U q ≫ pullback.fst f U.toBase)).obj F).IsFiniteType :=
    SheafOfModules.isFiniteType_of_iso (chartBaseChangeModuleIso C U q) ht'
  refine ⟨hl, hq, ht, ?_⟩
  have := hl
  have := hq
  have := ht
  obtain ⟨D⟩ := C.devissage
  cases D with
  | empty hzero =>
      exact ⟨.empty (((Scheme.Modules.pullback (pullback.fst C.h q.hom)).map_isZero
        hzero).of_iso (chartBaseChangeModuleIso C U q).symm)⟩
  | nonempty data =>
      obtain ⟨D', -⟩ := exists_completeDevissage_baseChange q.map_point data
        (pullback.fst C.h q.hom) hX (chartBaseChangeModuleIso C U q)
      exact ⟨.nonempty D'⟩

/-- A point of the fibre of `X ×_S S'` over `s'` whose image in `X` is hit by a chart is hit by
the base change of that chart. -/
private lemma mem_range_chartBaseChangeMap {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    {s : S} (C : DevissageChart f F s) (U : EtaleNeighborhood S s) (hU : U.IsElementary)
    (q : U ⟶ C.base) (z : ↥(pullback f U.toBase))
    (hz : pullback.snd f U.toBase z = U.point) (y : C.Y) (hy : C.h y = C.base.point)
    (hgy : C.g y = pullback.fst f U.toBase z) :
    z ∈ Set.range (chartBaseChangeMap C U q) := by
  have hres : IsIso (U.toBase.residueFieldMap U.point) := by
    rw [← EtaleNeighborhood.isElementary_iff]; exact hU
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := C.h) (g := q.hom)
    y U.point (hy.trans q.map_point.symm)
  refine ⟨w, eq_of_fst_eq_of_mem_fiber f U.toBase U.point hres ?_ hz ?_⟩
  · rw [← Scheme.Hom.comp_apply, chartBaseChangeMap_snd]
    exact hw₂
  · rw [← Scheme.Hom.comp_apply, chartBaseChangeMap_fst, Scheme.Hom.comp_apply, hw₁, hgy]

/-! ### Stacks 05HU -/

/-- The form of Stacks 05HU in which the elementary étale neighbourhood is moreover affine; the
construction produces an affine neighbourhood, and the statement records it. -/
theorem exists_isAffine_etaleNeighborhood_completeDevissage_cover {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (s : S) :
    ∃ (S' : EtaleNeighborhood S s) (_ : S'.IsElementary) (_ : IsAffine S'.scheme) (n : ℕ)
      (Y : Fin n → Scheme.{u})
      (h : ∀ i, Y i ⟶ pullback f S'.toBase) (_ : ∀ i, Etale (h i))
      (hl : ∀ i, LocallyOfFiniteType (h i ≫ pullback.snd f S'.toBase))
      (hq : ∀ i, ((Scheme.Modules.pullback
        (h i ≫ pullback.fst f S'.toBase)).obj F).IsQuasicoherent)
      (ht : ∀ i, ((Scheme.Modules.pullback
        (h i ≫ pullback.fst f S'.toBase)).obj F).IsFiniteType),
      (∀ i, Nonempty (@CompleteDevissage _ _ (h i ≫ pullback.snd f S'.toBase)
        ((Scheme.Modules.pullback (h i ≫ pullback.fst f S'.toBase)).obj F) S'.point
        (hl i) (hq i) (ht i))) ∧
        pullback.snd f S'.toBase ⁻¹' {S'.point} ⊆ ⋃ i, Set.range (h i) := by
  classical
  obtain ⟨n, C, hcover⟩ := exists_finite_devissageCharts f F s
  obtain ⟨W, hW, hom⟩ := exists_isElementary_forall_hom (fun i => (C i).base)
    fun i => (C i).elementary
  obtain ⟨U, hU, hUaff, ⟨a⟩⟩ := exists_isElementary_isAffine_hom W hW
  have := hUaff
  choose hl hq ht hD using fun i : Fin n =>
    exists_chartBaseChange_completeDevissage (C i) U (a ≫ (hom i).some)
  refine ⟨U, hU, hUaff, n, fun i => pullback (C i).h (a ≫ (hom i).some).hom,
    fun i => chartBaseChangeMap (C i) U (a ≫ (hom i).some),
    fun i => etale_chartBaseChangeMap (C i) U (a ≫ (hom i).some), hl, hq, ht, hD,
    fun z hz => ?_⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
  have hx : f (pullback.fst f U.toBase z) = s := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hz]
    exact U.map_point
  obtain ⟨i, y, hy, hgy⟩ := hcover ((f.fiberHomeo s).symm ⟨pullback.fst f U.toBase z, hx⟩)
  refine Set.mem_iUnion.mpr ⟨i, mem_range_chartBaseChangeMap (C i) U hU
    (a ≫ (hom i).some) z hz y hy ?_⟩
  rwa [Scheme.Hom.fiberι_fiberHomeo_symm] at hgy


/-- **Stacks Project, Tag 05HU.** Let `X ⟶ S` be a finite-type morphism of schemes and `F` a
finite-type quasi-coherent module on `X`. For every point `s` of `S` there is an elementary étale
neighbourhood `(S', s') ⟶ (S, s)` and finitely many étale morphisms `hᵢ : Yᵢ ⟶ X ×_S S'` whose
images cover the fibre `(X ×_S S')_{s'} = X_s`, such that the pullback of `F` to each `Yᵢ` has a
complete dévissage along `Yᵢ ⟶ S'` over `s'`. -/
@[stacks 05HU]
theorem exists_etaleNeighborhood_completeDevissage_cover {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (s : S) :
    ∃ (S' : EtaleNeighborhood S s) (_ : S'.IsElementary) (n : ℕ) (Y : Fin n → Scheme.{u})
      (h : ∀ i, Y i ⟶ pullback f S'.toBase) (_ : ∀ i, Etale (h i))
      (hl : ∀ i, LocallyOfFiniteType (h i ≫ pullback.snd f S'.toBase))
      (hq : ∀ i, ((Scheme.Modules.pullback
        (h i ≫ pullback.fst f S'.toBase)).obj F).IsQuasicoherent)
      (ht : ∀ i, ((Scheme.Modules.pullback
        (h i ≫ pullback.fst f S'.toBase)).obj F).IsFiniteType),
      (∀ i, Nonempty (@CompleteDevissage _ _ (h i ≫ pullback.snd f S'.toBase)
        ((Scheme.Modules.pullback (h i ≫ pullback.fst f S'.toBase)).obj F) S'.point
        (hl i) (hq i) (ht i))) ∧
        pullback.snd f S'.toBase ⁻¹' {S'.point} ⊆ ⋃ i, Set.range (h i) := by
  obtain ⟨S', hS', -, n, Y, h, het, hl, hq, ht, hD, hcov⟩ :=
    exists_isAffine_etaleNeighborhood_completeDevissage_cover f F s
  exact ⟨S', hS', n, Y, h, het, hl, hq, ht, hD, hcov⟩

end AlgebraicGeometry

end
