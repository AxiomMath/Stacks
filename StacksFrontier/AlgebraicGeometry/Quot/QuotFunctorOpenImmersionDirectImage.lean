module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange

/-!
# The direct image along an open immersion as a morphism of Quot functors

Let `B` be an algebraic space, let `j : X ⟶ Y` be an open immersion of algebraic spaces which
are separated and of finite presentation over `B`, let `G` be a quasi-coherent `𝒪_Y`-module and
set `F = j^*G`.  Stacks 0DP3 asserts that there is an open immersion
`Quot_{F/X/B} ⟶ Quot_{G/Y/B}` of algebraic spaces over `B`.

The morphism underlying that open immersion is the direct image.  Over a test scheme `T` of `B`
a quotient `F_T ⟶ Q` is sent to the composite `G_T ⟶ j_{T,*}F_T ⟶ j_{T,*}Q`, which is surjective
because `Q` has support proper over `T` and therefore closed in `Y_T` and contained in `X_T`, so
the stalks of `j_{T,*}Q` away from `X_T` vanish; and `j_{T,*}Q` is of finite presentation, flat
over `T` and has support proper over `T` by the morphism of stacks `Coh_{X/B} ⟶ Coh_{Y/B}` of
Stacks 0DN9.  Recording quotients by their kernels turns this into a map
`Quot_{F/X/B}(T) ⟶ Quot_{G/Y/B}(T)`, and its compatibility with pullback along a morphism of
test schemes makes the family of these maps a morphism of the Quot functors.

## Main definitions

* `AlgebraicGeometry.Space.QuotOpenImmersionSituation`: **Stacks 0DP3, the standing data** — the
  open immersion, the two structure morphisms to the base and the module `G` on the target.
* `AlgebraicGeometry.Space.QuotOpenImmersionSituation.pullbackModule`: the module `F = j^*G`.
* `AlgebraicGeometry.Space.QuotOpenImmersionSituation.sourceSituation` and
  `AlgebraicGeometry.Space.QuotOpenImmersionSituation.targetSituation`: the two quotient
  situations of Stacks 09TR, for `F/X/B` and for `G/Y/B`.
* `AlgebraicGeometry.Space.QuotOpenImmersionSituation.baseChangeOfMap`: the base change
  `j_T : X_T ⟶ Y_T`, again an open immersion.
* `AlgebraicGeometry.Space.QuotOpenImmersionSituation.directImageProjection`: the surjection
  `G_T ⟶ j_{T,*}(F_T/K)` of the source's first step.
* `AlgebraicGeometry.Space.QuotOpenImmersionSituation.directImageQuotient`: **the direct image of
  a quotient**, recorded — as the quotients themselves are — by its kernel.
* `AlgebraicGeometry.Space.QuotOpenImmersionSituation.quotFunctorMap`: **Stacks 0DP3**, the
  induced morphism `Quot_{F/X/B} ⟶ Quot_{G/Y/B}`.

## Main results

* `AlgebraicGeometry.Space.QuotOpenImmersionSituation.isOpenImmersion_baseChangeOfMap`: the base
  change `j_T : X_T ⟶ Y_T` is again an open immersion.
* `AlgebraicGeometry.Space.QuotOpenImmersionSituation.directImageQuotientCokernelIso`: the
  quotient of `G_T` by the direct image of a quotient is `j_{T,*}(F_T/K)`.
* `AlgebraicGeometry.Space.QuotOpenImmersionSituation.directImageQuotient_mem`: **Stacks 0DP3**,
  the direct image of a member of `Quot_{F/X/B}(T)` is a member of `Quot_{G/Y/B}(T)`.

## Implementation notes

**What is covered and what is not.**  The source's statement has two halves: there *is* a
morphism `Quot_{F/X/B} ⟶ Quot_{G/Y/B}`, which the source constructs, and that morphism is an
*open immersion*, whose proof the source omits, leaving only the hint that the condition
`Supp(Q_t) ⊆ |X_t|` on a member of `Quot_{G/Y/B}(T)` is open in `t`.  Only the first half is
covered here, and the attributes say so.  The second half needs the inverse construction — the
inverse image of a quotient of `G_T` whose support lies in `X_T` — which rests on
`j_T^* j_{T,*} ≅ 𝟭`, and then needs the openness of that locus; neither the adjunction of
Stacks 03LU in the form that identifies the composite of the inverse and direct images, nor any
form of the omitted argument, is available in this development.

**The surjection is a hypothesis, as are the conditions on the direct image.**  Unlike
Stacks 0DP1, where the comparison `G_T ≅ π_{T,*}F_T` of Stacks 07U8 makes the direct image of a
quotient a quotient formally, here `G_T ⟶ j_{T,*}F_T` is only a morphism and its surjectivity
onto `j_{T,*}Q` is the stalk computation of the source's proof.  That, the unit `G_T ⟶ j_{T,*}F_T`
itself, the morphism of stacks of Stacks 0DN9 and the compatibility of the direct image with base
change of the test scheme are carried as the fields of
`AlgebraicGeometry.Space.QuotOpenImmersionSituation.DirectImageInputs` and
`AlgebraicGeometry.Space.QuotOpenImmersionSituation.QuotDirectImageInputs`, each naming the
result it stands for.  Quasi-coherence of `F = j^*G` is *not* among them: it is Stacks 03GA,
proved here from the inverse-image presentations the situation carries.

## References

* [Stacks Project, Tag 0DP3](https://stacks.math.columbia.edu/tag/0DP3)
* [Stacks Project, Tag 0DN9](https://stacks.math.columbia.edu/tag/0DN9)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The standing data -/

/-- **Stacks 0DP3, the standing data.**  An open immersion `j : X ⟶ Y` of algebraic spaces which
are separated and of finite presentation over an algebraic space `B`, together with a
quasi-coherent `𝒪_Y`-module `G`: the data along which the direct image induces a morphism
`Quot_{j^*G/X/B} ⟶ Quot_{G/Y/B}`. -/
@[stacks 0DP3 "the standing data"]
structure QuotOpenImmersionSituation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) where
  /-- The base algebraic space over which the two spaces live. -/
  base : AlgebraicSpaces B S hS
  /-- The open subspace, on which the pulled-back module lives. -/
  X : AlgebraicSpaces B S hS
  /-- The ambient space, on which the given module lives. -/
  Y : AlgebraicSpaces B S hS
  /-- The open immersion. -/
  j : X ⟶ Y
  /-- The structure morphism of the open subspace over the base. -/
  structureX : X ⟶ base
  /-- The structure morphism of the ambient space over the base. -/
  structureY : Y ⟶ base
  /-- The open immersion is a morphism over the base. -/
  comp : j ≫ structureY = structureX
  /-- The module on the ambient space. -/
  G : Modules.{u, u} B S hS Y.1 Y.2
  /-- It is quasi-coherent (Stacks 03G9). -/
  quasicoherent : G.IsQuasicoherentOnSite
  /-- The morphism is an open immersion. -/
  openImmersion : IsOpenImmersion B S hS j.hom
  /-- The inverse-image input of Stacks 03GA along the open immersion, which makes `j^*G`
  quasi-coherent. -/
  pullbackPresentations : HasLocalInverseImagePresentations B S hS j
  /-- The open subspace is separated over the base. -/
  separatedX : IsSeparated B S hS structureX.hom
  /-- The ambient space is separated over the base. -/
  separatedY : IsSeparated B S hS structureY.hom
  /-- The open subspace is of finite presentation over the base (Stacks 03XP). -/
  finitePresentationX : IsFinitePresentation B S hS structureX.hom
  /-- The ambient space is of finite presentation over the base (Stacks 03XP). -/
  finitePresentationY : IsFinitePresentation B S hS structureY.hom

namespace QuotOpenImmersionSituation

variable (D : QuotOpenImmersionSituation B S hS)

/-! ### The two quotient situations -/

/-- The module `F = j^*G`, the restriction of `G` to the open subspace. -/
def pullbackModule : Modules.{u, u} B S hS D.X.1 D.X.2 :=
  (modulePullback B S hS D.j).obj D.G

/-- **Stacks 03GA for the open immersion of the situation**: the restriction `F = j^*G` is
quasi-coherent, granted the inverse-image presentations the situation carries. -/
theorem isQuasicoherentOnSite_pullbackModule : D.pullbackModule.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback B S hS D.j D.pullbackPresentations D.G D.quasicoherent

/-- The quotient situation `F/X/B` of Stacks 09TR for `F = j^*G`, whose Quot functor is the
source of the morphism of Stacks 0DP3. -/
def sourceSituation : QuotSituation B S hS where
  X := D.X
  Y := D.base
  f := D.structureX
  F := D.pullbackModule
  quasicoherent := D.isQuasicoherentOnSite_pullbackModule
  finitePresentation := D.finitePresentationX

/-- The quotient situation `G/Y/B` of Stacks 09TR, whose Quot functor is the target of the
morphism of Stacks 0DP3. -/
def targetSituation : QuotSituation B S hS where
  X := D.Y
  Y := D.base
  f := D.structureY
  F := D.G
  quasicoherent := D.quasicoherent
  finitePresentation := D.finitePresentationY

/-! ### The base change of the open immersion -/

/-- The base change `j_T : X_T ⟶ Y_T` of the open immersion of the situation to a test scheme
`T` over the base. -/
def baseChangeOfMap (T : SchemesOver D.base) :
    baseChangeSpace D.structureX T ⟶ baseChangeSpace D.structureY T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.structureY T.hom).lift
    (baseChangeProjection D.structureX T ≫ D.j) (baseChangeInclusion D.structureX T) (by
      rw [Category.assoc, D.comp]
      exact (AlgebraicSpaces.isPullback_fiberProduct B S hS D.structureX T.hom).w)

/-- The base change `j_T` followed by the projection `Y_T ⟶ Y` is the projection `X_T ⟶ X`
followed by `j`. -/
@[reassoc (attr := simp)]
theorem baseChangeOfMap_comp_projection (T : SchemesOver D.base) :
    D.baseChangeOfMap T ≫ baseChangeProjection D.structureY T =
      baseChangeProjection D.structureX T ≫ D.j :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.structureY T.hom).lift_fst _ _ _

/-- The base change `j_T` followed by the map `Y_T ⟶ T` is the map `X_T ⟶ T`. -/
@[reassoc (attr := simp)]
theorem baseChangeOfMap_comp_inclusion (T : SchemesOver D.base) :
    D.baseChangeOfMap T ≫ baseChangeInclusion D.structureY T =
      baseChangeInclusion D.structureX T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.structureY T.hom).lift_snd _ _ _

/-- The base change of the open immersion over the base is a base change in the strict sense:
`X_T` is the fibre product of `Y_T` and `X` over `Y`. -/
theorem isPullback_baseChangeOfMap (T : SchemesOver D.base) :
    IsPullback (D.baseChangeOfMap T) (baseChangeProjection D.structureX T)
      (baseChangeProjection D.structureY T) D.j := by
  have outer : IsPullback (D.baseChangeOfMap T ≫ baseChangeInclusion D.structureY T)
      (baseChangeProjection D.structureX T) T.hom (D.j ≫ D.structureY) := by
    rw [D.baseChangeOfMap_comp_inclusion T, D.comp]
    exact (AlgebraicSpaces.isPullback_fiberProduct B S hS D.structureX T.hom).flip
  exact outer.of_right (D.baseChangeOfMap_comp_projection T)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.structureY T.hom).flip

/-- **The base change of the open immersion is an open immersion**, by Stacks 02YW. -/
theorem isOpenImmersion_baseChangeOfMap (T : SchemesOver D.base) :
    IsOpenImmersion B S hS (D.baseChangeOfMap T).hom :=
  isOpenImmersion_of_isPullback B S hS (D.isPullback_baseChangeOfMap T).flip D.openImmersion

/-! ### The surjection onto the direct image of a quotient -/

/-- **The two steps of the source's construction that this development does not have**, carried
as hypotheses.

The first field is the morphism `G_T ⟶ j_{T,*}F_T` the source writes down, which is the unit of
the adjunction of Stacks 03LU read through the identification `F_T = j_T^*G_T`; the adjunction is
not available for `AlgebraicGeometry.Space.modulePushforward` in this development.  The second is
the source's "looking at stalks one finds that this is surjective": the composite
`G_T ⟶ j_{T,*}F_T ⟶ j_{T,*}(F_T/K)` is an epimorphism, which holds because the support of the
quotient is closed in `Y_T` and contained in `X_T`. -/
structure DirectImageInputs (D : QuotOpenImmersionSituation B S hS) where
  /-- The morphism `G_T ⟶ j_{T,*}F_T` of the source's first step. -/
  unit : ∀ T : SchemesOver D.base,
    D.targetSituation.baseChangeModule T ⟶
      (modulePushforward B S hS (D.baseChangeOfMap T)).obj
        (D.sourceSituation.baseChangeModule T)
  /-- The composite onto the direct image of a quotient is surjective. -/
  epi : ∀ (T : SchemesOver D.base) (K : Subobject (D.sourceSituation.baseChangeModule T)),
    Epi (unit T ≫ (modulePushforward B S hS (D.baseChangeOfMap T)).map
      (D.sourceSituation.quotientProjection T K))

/-- The surjection `G_T ⟶ j_{T,*}(F_T/K)` presenting the direct image of a quotient of `F_T` as
a quotient of `G_T`. -/
def directImageProjection (ν : DirectImageInputs D) (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T)) :
    D.targetSituation.baseChangeModule T ⟶
      (modulePushforward B S hS (D.baseChangeOfMap T)).obj
        (D.sourceSituation.quotientModule T K) :=
  ν.unit T ≫ (modulePushforward B S hS (D.baseChangeOfMap T)).map
    (D.sourceSituation.quotientProjection T K)

/-- The morphism `G_T ⟶ j_{T,*}(F_T/K)` is an epimorphism. -/
instance epi_directImageProjection (ν : DirectImageInputs D) (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T)) :
    Epi (D.directImageProjection ν T K) :=
  ν.epi T K

/-- **Stacks 0DP3, the direct image of a quotient.**  The quotient `G_T ⟶ j_{T,*}(F_T/K)` of
`G_T`, recorded — as the quotients themselves are — by its kernel. -/
@[stacks 0DP3 "the direct image of a quotient, recorded by its kernel"]
def directImageQuotient (ν : DirectImageInputs D) (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T)) :
    Subobject (D.targetSituation.baseChangeModule T) :=
  kernelSubobject (D.directImageProjection ν T K)

/-- **The quotient of `G_T` by the direct image of a quotient is the direct image of that
quotient**: the quotient of `G_T` by `directImageQuotient ν T K` is `j_{T,*}(F_T/K)`. -/
def directImageQuotientCokernelIso (ν : DirectImageInputs D) (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T)) :
    D.targetSituation.quotientModule T (D.directImageQuotient ν T K) ≅
      (modulePushforward B S hS (D.baseChangeOfMap T)).obj
        (D.sourceSituation.quotientModule T K) :=
  Abelian.cokernelKernelSubobjectIso (D.directImageProjection ν T K)

/-! ### The inputs the morphism of Quot functors is built from -/

/-- **The inputs the morphism of Stacks 0DP3 is built from**, bundled: the two steps of the
construction above, the morphism of stacks `Coh_{X/B} ⟶ Coh_{Y/B}` of Stacks 0DN9, which is what
the source cites for the conditions on `j_{T,*}Q`, and the compatibility of the direct image with
base change of the test scheme, which is part (b) of the proof of Stacks 0DN9.

Of Stacks 0DN9 this development has only the two reduction steps of the proof, in
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackPushforwardReduction.lean`. -/
structure QuotDirectImageInputs (D : QuotOpenImmersionSituation B S hS) where
  /-- The morphism `G_T ⟶ j_{T,*}F_T` and the surjectivity of its composites. -/
  projections : DirectImageInputs D
  /-- **Stacks 0DN9 for the situation**: the direct image along `j_T` of a module satisfying the
  four conditions of Stacks 09TR over `T` again satisfies them. -/
  pushforwardMem : ∀ (T : SchemesOver D.base)
      (Q : Modules.{u, u} B S hS (D.sourceSituation.space T).1 (D.sourceSituation.space T).2),
    D.sourceSituation.IsQuotModule T Q →
      D.targetSituation.IsQuotModule T
        ((modulePushforward B S hS (D.baseChangeOfMap T)).obj Q)
  /-- **Part (b) of the proof of Stacks 0DN9 for the situation**: forming the direct image
  commutes with pullback along a morphism of test schemes, read on the kernels of the
  quotients. -/
  directImageQuotient_quotientPullback : ∀ {T' T : SchemesOver D.base} (m : T' ⟶ T)
      (K : Subobject (D.sourceSituation.baseChangeModule T)),
    D.directImageQuotient projections T' (D.sourceSituation.quotientPullback m K) =
      D.targetSituation.quotientPullback m (D.directImageQuotient projections T K)

/-! ### The morphism of Quot functors -/

/-- **Stacks 0DP3.**  The direct image of a quotient in `Quot_{F/X/B}(T)` lies in
`Quot_{G/Y/B}(T)`: the quotient of `G_T` by it is `j_{T,*}(F_T/K)`, which is quasi-coherent, of
finite presentation, flat over `T` and has support proper over `T` because `F_T/K` is, this being
the morphism of stacks `Coh_{X/B} ⟶ Coh_{Y/B}` of Stacks 0DN9. -/
@[stacks 0DP3 "the direct image of a quotient of the Quot functor is one"]
theorem directImageQuotient_mem (I : QuotDirectImageInputs D) (T : SchemesOver D.base)
    (K : Subobject (D.sourceSituation.baseChangeModule T))
    (hK : K ∈ D.sourceSituation.properlySupportedQuotients T) :
    D.directImageQuotient I.projections T K ∈
      D.targetSituation.properlySupportedQuotients T :=
  (D.targetSituation.mem_properlySupportedQuotients_iff T
      (D.directImageQuotient I.projections T K)).mpr
    (QuotSituation.IsQuotModule.of_iso
      (D.directImageQuotientCokernelIso I.projections T K).symm
      (I.pushforwardMem T (D.sourceSituation.quotientModule T K)
        ((D.sourceSituation.mem_properlySupportedQuotients_iff T K).mp hK)))

/-- **Stacks 0DP3, the morphism of Quot functors.**  The morphism
`Quot_{F/X/B} ⟶ Quot_{G/Y/B}` induced by the direct image: over a test scheme it sends a quotient
`F_T ⟶ Q` to `G_T ⟶ j_{T,*}Q`.  This is the morphism the source constructs; that it is an open
immersion is the half of the statement whose proof the source omits, and is not proved here.

Naturality is the compatibility of the direct image with pullback along a morphism of test
schemes, part (b) of the proof of Stacks 0DN9. -/
@[stacks 0DP3 "the morphism of Quot functors the source constructs, not its being open"]
def quotFunctorMap (I : QuotDirectImageInputs D) :
    D.sourceSituation.quotFunctor ⟶ D.targetSituation.quotFunctor where
  app T := ↾fun K ↦
    ⟨D.directImageQuotient I.projections T.unop K.1,
      D.directImageQuotient_mem I T.unop K.1 K.2⟩
  naturality _ _ m := ConcreteCategory.hom_ext _ _ fun K ↦
    Subtype.ext (I.directImageQuotient_quotientPullback m.unop K.1)

end QuotOpenImmersionSituation

end AlgebraicGeometry.Space

end
