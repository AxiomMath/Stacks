module

public import StacksFrontier.Deformation.Artin.Obstruction.DualSituation
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityOpenness

/-!
# Reading a naive obstruction datum in raw variables

`Deformation.Artin.NaiveObstructionAt` packages hypotheses (1) and (2) of [Stacks, Tag 07YN]
at a `Deformation.Artin.ChartedObject`: an object `x` of the fibred category over the spectrum
of a ring `A`, bundled with the affine chart `Spec Λ ⊆ S` through which `Spec A → S` factors.
The same hypotheses can be stated in *raw variables* — a bare pair of rings `Λ A : Type u`, the
morphisms `toS`, `baseMap`, the object `x` with its witness `hx`, a lifting hypothesis phrased
with `Deformation.Artin.SquareZeroThickening`, and a tangent hypothesis phrased as an `AddEquiv`
into a `Hom`-group of the derived category.

This file compares the two presentations: each result is a definitional identity, a repackaging
of a bijection, or a transport of the comparison between the two descriptions of the category of
lifts.

## Main results

* `Deformation.Artin.hasLift_iff_nonempty_underFiber` — the two descriptions of "`x` lifts
  across a deformation situation" agree: the source's `Lift(x, A')` is nonempty exactly when
  the fibre of `Under.post p` over the arrow of the thickening is.
* `Deformation.Artin.NaiveObstructionAt.nonempty_underFiber_iff_comp_eq_zero` — hypothesis (1)
  of the tag, read at a `Deformation.Artin.SquareZeroThickening`.
* `Deformation.Artin.NaiveObstructionAt.tangentEquiv`,
  `Deformation.Artin.NaiveObstructionAt.tangentEquiv_natural`,
  `Deformation.Artin.NaiveObstructionAt.tangentEquiv_canonical` — hypothesis (2) of the tag,
  read as an additive equivalence onto a `Hom`-group of the derived category.
* `Deformation.Artin.extZeroAddEquiv` — the identification `Ext⁰(E, Y) ≃+ (E ⟶ Y)`, which is
  `CategoryTheory.ShiftedHom.homEquiv` at degree `0` made additive.

## Implementation notes

The chart dictionary of a `Deformation.Artin.ChartedObject` is definitional: `P.ring`,
`P.point`, `P.naiveCotangent` and `P.tangent` are `abbrev`s, and
`Deformation.Artin.algebraOver P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem` is the same
object of the site as `P.obj.alg.over`. The lemmas recording this, in the section
`ChartedDictionary` below, hold by `rfl`.

The comparison of the lifting criteria needs one hypothesis that a bare
`Deformation.Artin.SquareZeroThickening` does not carry: that the structure morphism of
`Spec A'` is the one obtained from the chart, i.e. `Spec A' → Spec Λ → S`. This is exactly the
field `_hchart` of `Deformation.Artin.NaiveObstructionAt.hasLift_iff_xi_comp_eq_zero`, and it
is genuinely extra data — a square-zero thickening only forces
`Spec A → Spec A' → S` to agree with `Spec A → S`, and `Spec A → Spec A'` is not an
epimorphism of schemes, so the structure morphism of `Spec A'` is not determined. The
thickenings produced by `Deformation.Artin.squareZeroThickeningOfTower` satisfy it by
construction.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07YN](https://stacks.math.columbia.edu/tag/07YN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v w

attribute [local instance] HasDerivedCategory.standard

/-! ### Degree-zero `Ext` as a group of morphisms -/

section ExtZero

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **Degree-zero `Ext` is a `Hom`-group.** `DerivedCategory.Ext E Y 0` is `E ⟶ Y⟦(0 : ℤ)⟧`, so
`CategoryTheory.ShiftedHom.homEquiv` identifies it with `E ⟶ Y`; the identification is additive
because `CategoryTheory.ShiftedHom.mk₀` is postcomposition with a fixed morphism. -/
public def extZeroAddEquiv (E Y : DerivedCategory C) :
    (E ⟶ Y) ≃+ DerivedCategory.Ext E Y 0 :=
  { ShiftedHom.homEquiv (X := E) (Y := Y) (0 : ℤ) rfl with
    map_add' := fun f g => ShiftedHom.mk₀_add (0 : ℤ) rfl f g }

/-- The identification of degree-zero `Ext` with morphisms sends `f` to
`CategoryTheory.ShiftedHom.mk₀ 0 rfl f`. -/
public theorem extZeroAddEquiv_apply {E Y : DerivedCategory C} (f : E ⟶ Y) :
    extZeroAddEquiv E Y f = ShiftedHom.mk₀ (0 : ℤ) rfl f :=
  rfl

/-- The identification of degree-zero `Ext` with morphisms turns the pushforward of a class
along `g` into postcomposition with `g`. -/
public theorem extZeroAddEquiv_symm_comp_shift {E Y Z : DerivedCategory C}
    (α : DerivedCategory.Ext E Y 0) (g : Y ⟶ Z) :
    (extZeroAddEquiv E Z).symm (α ≫ g⟦(0 : ℤ)⟧') = (extZeroAddEquiv E Y).symm α ≫ g := by
  change (α ≫ g⟦(0 : ℤ)⟧') ≫ (shiftFunctorZero' (DerivedCategory C) (0 : ℤ) rfl).hom.app Z =
    (α ≫ (shiftFunctorZero' (DerivedCategory C) (0 : ℤ) rfl).hom.app Y) ≫ g
  rw [Category.assoc, Category.assoc,
    (shiftFunctorZero' (DerivedCategory C) (0 : ℤ) rfl).hom.naturality g]
  rfl

end ExtZero

/-! ### The two descriptions of the category of lifts -/

section LiftBridge

variable {C₀ : Type*} [Category C₀] {D₀ : Type*} [Category D₀]

/-- **The two descriptions of a lift agree.** For a category fibred in groupoids `q`, an object
`y` of the fibre over `U` and an arrow `f : U ⟶ V`, the source's `Lift(y, V)` — an object of
the fibre over `V` whose pullback along `f` is isomorphic to `y` — is nonempty exactly when the
fibre of `Under.post q` over `Under.mk (eqToHom y.2 ≫ f)` is. -/
public theorem nonempty_pullbackIso_iff_nonempty_underFiber (q : D₀ ⥤ C₀)
    (hq : q.IsFiberedInGroupoids) (ch : q.ChoiceOfPullbacks) {U V : C₀} (f : U ⟶ V)
    (y : q.Fiber U) :
    (∃ y' : q.Fiber V, Nonempty ((ch.pullbackFunctor f).obj y' ≅ y)) ↔
      Nonempty ((Under.post q).Fiber (Under.mk (eqToHom y.2 ≫ f))) := by
  constructor
  · rintro ⟨y', ⟨e⟩⟩
    exact ⟨isoFiberToUnderObj q ch f y
      ⟨CostructuredArrow.mk e.hom, show IsIso e.hom from inferInstance⟩⟩
  · rintro ⟨a⟩
    obtain ⟨t₀, -⟩ := isoFiberToUnder_surjective q hq ch f y a
    have : IsIso t₀.obj.hom := t₀.property
    exact ⟨t₀.obj.left, ⟨asIso t₀.obj.hom⟩⟩

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS}

/-- **`Deformation.Artin.AffineObject.HasLift` in the `Under.post` presentation.** The object
`x` of a `Deformation.Artin.AffineObject` lifts across a deformation situation `A' → A` exactly
when the fibre of `Under.post p` over the arrow `eqToHom P.obj.2 ≫ t.hom.specMap` is nonempty. -/
public theorem hasLift_iff_nonempty_underFiber (hp : p.IsFiberedInGroupoids)
    (P : AffineObject B S hS p) (t : DeformationSituation B S hS P.alg) :
    AffineObject.HasLift hp P t ↔
      Nonempty ((Under.post p).Fiber (Under.mk (eqToHom P.obj.2 ≫ t.hom.specMap))) := by
  let : p.IsFibered := hp.isFibered
  exact nonempty_pullbackIso_iff_nonempty_underFiber p hp p.chosenPullbacks t.hom.specMap P.obj

end LiftBridge

/-! ### The chart dictionary -/

section ChartedDictionary

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {c : AffineChart S}
variable (P : ChartedObject B S hS p c)

/-- The ring of a charted object is the carrier of its site algebra. -/
public theorem ChartedObject.ring_eq : P.ring = P.obj.alg.carrier := rfl

/-- The point of a charted object is the underlying object of its fibre element. -/
public theorem ChartedObject.point_eq : P.point = P.obj.obj.1 := rfl

/-- `Spec A`, built from the raw structure morphism of a charted object, is the object of the
site underlying the charted object. -/
public theorem ChartedObject.algebraOver_eq :
    algebraOver P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem = P.obj.alg.over := rfl

/-- The witness that the point of a charted object lies over `Spec A`, in the raw-variable
form `p.obj x = algebraOver A B S hS toS hA`. -/
public theorem ChartedObject.obj_eq_algebraOver :
    p.obj P.point = algebraOver P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem :=
  P.obj.obj.2

/-- The naive cotangent complex of a charted object is `NL_{A/Λ}` for its raw rings. -/
public theorem ChartedObject.naiveCotangent_eq :
    P.naiveCotangent = derivedNaiveCotangentComplex c.ring P.ring := rfl

/-- The tangent functor of a charted object is the raw-variable tangent functor. -/
public theorem ChartedObject.tangent_eq (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp) :
    P.tangent hp hRS = tangentFunctor P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p
      P.point P.obj.obj.2 hp hRS :=
  rfl

/-- The factorization of a charted object is the raw-variable base factorization through the
chart. -/
public theorem ChartedObject.factorization_eq :
    Spec.map (CommRingCat.ofHom (algebraMap c.ring P.ring)) ≫ c.immersion =
      P.obj.alg.toScheme :=
  P.factorization

/-- The witness that the point of a charted object lies over `Spec A` as a scheme over `S` is
the raw-variable witness obtained by rewriting with `P.obj.obj.2` (proof irrelevance). -/
public theorem ChartedObject.overScheme_eq_raw :
    P.overScheme_eq =
      (show (p ⋙ Over.post B.inclusion).obj P.point = Over.mk P.obj.alg.toScheme by
        change (Over.post B.inclusion).obj (p.obj P.point) = _
        rw [P.obj.obj.2]
        rfl) :=
  rfl

end ChartedDictionary

/-! ### Hypothesis (1): lifting across a square-zero thickening -/

section Lifting

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {c : AffineChart S}

/-- A square-zero thickening of `Spec A` in the site, read as a deformation situation over the
site algebra of a charted object. The two structures carry the same data: a surjection with
square-zero kernel, the membership of `Spec A'` in the site, its structure morphism, and the
arrow of the site that the surjection induces. -/
public abbrev ChartedObject.deformationSituationOfThickening (P : ChartedObject B S hS p c)
    {A' : Type u} [CommRing A']
    (D : SquareZeroThickening P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem A') :
    DeformationSituation B S hS P.obj.alg where
  top := { carrier := A', mem := D.hA', toBase := D.toS' }
  hom := { ringMap := D.q, specMap := D.arrow, specMap_spec := D.arrow_spec }
  surjective := D.squareZeroSurjection.1
  sq_eq_bot := D.squareZeroSurjection.2

variable {hp : p.IsFiberedInGroupoids} {hRS : SatisfiesRSStar B S hS p hp}
variable {P : ChartedObject B S hS p c}
variable {hΩ : B.Contains (Spec (squareZeroRing P.ring (differentialsModule c.ring P.ring)))}
variable {E : DerivedCategory (ModuleCat.{u} P.ring)} {ξ : E ⟶ P.naiveCotangent}

/-- **Hypothesis (1) of [Stacks, Tag 07YN] in raw variables.** The lifting criterion carried by
a `Deformation.Artin.NaiveObstructionAt`, read at a `Deformation.Artin.SquareZeroThickening`
`A' → A` of `Λ`-algebras whose structure morphism is the one through the chart: the object `x`
lifts over `Spec A'` exactly when `E ⟶ NL_{A/Λ} ⟶ NL_{A/A'}` vanishes.

The hypothesis `hchart` is the field `_hchart` of the structure and cannot be dropped: a
`Deformation.Artin.SquareZeroThickening` only records that `Spec A → Spec A' → S` agrees with
`Spec A → S`, and `Spec A → Spec A'` is not an epimorphism of schemes. -/
public theorem NaiveObstructionAt.nonempty_underFiber_iff_comp_eq_zero
    (data : NaiveObstructionAt hp hRS P hΩ E ξ)
    {A' : Type u} [CommRing A'] [Algebra A' P.ring] [Algebra c.ring A']
    [IsScalarTower c.ring A' P.ring]
    (D : SquareZeroThickening P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem A')
    (hq : D.q = algebraMap A' P.ring)
    (hchart : Spec.map (CommRingCat.ofHom (algebraMap c.ring A')) ≫ c.immersion =
      B.inclusion.map D.toS') :
    Nonempty ((Under.post p).Fiber (Under.mk (eqToHom P.obj.obj.2 ≫ D.arrow))) ↔
      ξ ≫ naiveCotangentBaseMap c.ring A' P.ring = 0 :=
  (hasLift_iff_nonempty_underFiber hp P.obj
      (P.deformationSituationOfThickening D)).symm.trans
    (data.hasLift_iff_xi_comp_eq_zero (P.deformationSituationOfThickening D) hq.symm hchart)

/-- **Hypothesis (1), lifting direction.** For every square-zero thickening `A' → A` of
`Λ`-algebras whose structure morphism comes from the chart, if `E ⟶ NL_{A/Λ} ⟶ NL_{A/A'}`
vanishes then `x` lifts over `Spec A'`. -/
public theorem NaiveObstructionAt.nonempty_underFiber_of_comp_eq_zero
    (data : NaiveObstructionAt hp hRS P hΩ E ξ) :
    ∀ (A' : Type u) [CommRing A'] [Algebra c.ring A'] [Algebra A' P.ring]
      [IsScalarTower c.ring A' P.ring]
      (D : SquareZeroThickening P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem A'),
      D.q = algebraMap A' P.ring →
      Spec.map (CommRingCat.ofHom (algebraMap c.ring A')) ≫ c.immersion =
        B.inclusion.map D.toS' →
      ξ ≫ naiveCotangentBaseMap c.ring A' P.ring = 0 →
      Nonempty ((Under.post p).Fiber (Under.mk (eqToHom P.obj.obj.2 ≫ D.arrow))) :=
  fun _ _ _ _ _ D hq hchart =>
    (data.nonempty_underFiber_iff_comp_eq_zero D hq hchart).mpr

/-- **Hypothesis (1), obstruction direction.** For every square-zero thickening `A' → A` of
`Λ`-algebras whose structure morphism comes from the chart, if `x` lifts over `Spec A'` then
`E ⟶ NL_{A/Λ} ⟶ NL_{A/A'}` vanishes. -/
public theorem NaiveObstructionAt.comp_eq_zero_of_nonempty_underFiber
    (data : NaiveObstructionAt hp hRS P hΩ E ξ) :
    ∀ (A' : Type u) [CommRing A'] [Algebra c.ring A'] [Algebra A' P.ring]
      [IsScalarTower c.ring A' P.ring]
      (D : SquareZeroThickening P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem A'),
      D.q = algebraMap A' P.ring →
      Spec.map (CommRingCat.ofHom (algebraMap c.ring A')) ≫ c.immersion =
        B.inclusion.map D.toS' →
      Nonempty ((Under.post p).Fiber (Under.mk (eqToHom P.obj.obj.2 ≫ D.arrow))) →
      ξ ≫ naiveCotangentBaseMap c.ring A' P.ring = 0 :=
  fun _ _ _ _ _ D hq hchart =>
    (data.nonempty_underFiber_iff_comp_eq_zero D hq hchart).mp

end Lifting

/-! ### Hypothesis (2): the tangent functor -/

section Tangent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {c : AffineChart S}
variable {hp : p.IsFiberedInGroupoids} {hRS : SatisfiesRSStar B S hS p hp}
variable {P : ChartedObject B S hS p c}
variable {hΩ : B.Contains (Spec (squareZeroRing P.ring (differentialsModule c.ring P.ring)))}
variable {E : DerivedCategory (ModuleCat.{u} P.ring)} {ξ : E ⟶ P.naiveCotangent}

/-- **Hypothesis (2) of [Stacks, Tag 07YN] as an additive equivalence.** The transformation
`T_x(M) ⟶ Ext⁰_A(E, M)` carried by a `Deformation.Artin.NaiveObstructionAt` is additive and
bijective, so it is an additive equivalence; composed with the identification of degree-zero
`Ext` with morphisms of `D(A)`, it is an isomorphism `T_x(M) ≃+ Hom_{D(A)}(E, M[0])`. -/
public def NaiveObstructionAt.tangentEquiv (data : NaiveObstructionAt hp hRS P hΩ E ξ)
    (M : SiteModule P.ring B) :
    ((P.tangent hp hRS).functor.obj M : Type (max (u + 1) v w)) ≃+
      (E ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} P.ring) 0).obj M.obj) :=
  (AddEquiv.ofBijective
    (AddMonoidHom.mk' (data.tangentMap M) (data.tangentMap_add M))
    (data.tangentMap_bijective M)).trans
      (extZeroAddEquiv E ((DerivedCategory.singleFunctor (ModuleCat.{u} P.ring) 0).obj
        M.obj)).symm

/-- The additive equivalence of hypothesis (2) is the degree-zero `Ext` identification applied
to the transformation it is built from. -/
public theorem NaiveObstructionAt.tangentEquiv_apply
    (data : NaiveObstructionAt hp hRS P hΩ E ξ) (M : SiteModule P.ring B)
    (a : ((P.tangent hp hRS).functor.obj M : Type (max (u + 1) v w))) :
    data.tangentEquiv M a =
      (extZeroAddEquiv E ((DerivedCategory.singleFunctor (ModuleCat.{u} P.ring) 0).obj
        M.obj)).symm (data.tangentMap M a) :=
  rfl

/-- **Hypothesis (2) in raw variables: naturality.** The additive equivalence of
`Deformation.Artin.NaiveObstructionAt.tangentEquiv` is natural in the coefficient module, with
the pushforward of `Ext` classes replaced by postcomposition of morphisms. -/
public theorem NaiveObstructionAt.tangentEquiv_natural
    (data : NaiveObstructionAt hp hRS P hΩ E ξ) {M N : SiteModule P.ring B} (f : M ⟶ N)
    (z : ((P.tangent hp hRS).functor.obj M : Type (max (u + 1) v w))) :
    data.tangentEquiv N ((P.tangent hp hRS).functor.map f z) =
      data.tangentEquiv M z ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} P.ring) 0).map f.hom := by
  rw [data.tangentEquiv_apply, data.tangentEquiv_apply, data.tangentMap_natural M N f z]
  exact extZeroAddEquiv_symm_comp_shift _ _

/-- **Hypothesis (2) in raw variables: the canonical element.** Under the additive equivalence
of `Deformation.Artin.NaiveObstructionAt.tangentEquiv`, the canonical element of
`T_x(Ω_{A/Λ})` is the composition `E ⟶ NL_{A/Λ} ⟶ Ω_{A/Λ}`. -/
public theorem NaiveObstructionAt.tangentEquiv_canonical
    (data : NaiveObstructionAt hp hRS P hΩ E ξ) :
    data.tangentEquiv (differentialsSiteModule c.ring P.ring B hΩ)
        (canonicalDeformationElement c.ring P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem
          p P.point P.obj.obj.2 hp hRS hΩ c.immersion P.factorization).element =
      ξ ≫ naiveCotangentToDifferentials c.ring P.ring := by
  rw [data.tangentEquiv_apply, data.tangentMap_canonicalElement]
  exact (extZeroAddEquiv E _).symm_apply_apply _

/-- **Hypothesis (2) in raw variables.** For the tangent functor spelled out in raw variables,
there are additive equivalences `T_x(M) ≃+ Hom_{D(A)}(E, M[0])`, natural in the coefficient
module `M`, sending the canonical element of `T_x(Ω_{A/Λ})` to the composition
`E ⟶ NL_{A/Λ} ⟶ Ω_{A/Λ}`. -/
public theorem NaiveObstructionAt.exists_tangentEquiv
    (data : NaiveObstructionAt hp hRS P hΩ E ξ) :
    ∃ teq : ∀ M : SiteModule P.ring B,
        ((tangentFunctor P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p P.point
            P.obj.obj.2 hp hRS).functor.obj M : Type (max (u + 1) v w)) ≃+
          (E ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} P.ring) 0).obj M.obj),
      (∀ {M N : SiteModule P.ring B} (f : M ⟶ N)
          (z : (tangentFunctor P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p P.point
            P.obj.obj.2 hp hRS).functor.obj M),
        teq N ((tangentFunctor P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem p P.point
            P.obj.obj.2 hp hRS).functor.map f z) =
          teq M z ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} P.ring) 0).map f.hom) ∧
      teq (differentialsSiteModule c.ring P.ring B hΩ)
          (canonicalDeformationElement c.ring P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem
            p P.point P.obj.obj.2 hp hRS hΩ c.immersion P.factorization).element =
        ξ ≫ naiveCotangentToDifferentials c.ring P.ring :=
  ⟨data.tangentEquiv, fun f z => data.tangentEquiv_natural f z, data.tangentEquiv_canonical⟩

end Tangent

end Deformation.Artin
