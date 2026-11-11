module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Subobject.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical

/-!
# Subspaces of an algebraic space and invariant subschemes of a chart

Let `X` be an algebraic space over a scheme `S` and let `φ : U ⟶ X` be a surjective étale chart
of `X` by an object `U` of the big fppf site of `S`. The fibre product `R = U ×_X U` is a
scheme of the site and carries two morphisms `t, s : R ⟶ U`, the two projections. A subscheme
`Z ⊆ U` is *invariant* when its two pullbacks along `t` and along `s` agree.

The content of Stacks 07TW is that invariant locally closed subschemes of `U` correspond
bijectively to locally closed subspaces of `X`, by pullback along `φ`, and that the bijection
matches closed subschemes with closed subspaces and open subschemes with open subspaces.

The subspace attached to an invariant subscheme `Z` of `U` is constructed directly, as the
subfunctor `AlgebraicGeometry.Space.invariantSubspace` of `X` whose sections over `T` are the
sections `x` of `X` every one of whose lifts to `U`, after an arbitrary base change, factors
through `Z`. Invariance of `Z` is used exactly once, to identify the preimage of that
subfunctor along `φ` with the functor of points of `Z`.

## Main definitions

* `AlgebraicGeometry.Space.subschemePoints` is the functor of points of a subscheme of an
  object `U` of the site, as a subfunctor of the functor of points of `U`. The subscheme is a
  subobject of the underlying scheme of `U` and is not required to be an object of the site.
* `AlgebraicGeometry.Space.subschemeObject` and `AlgebraicGeometry.Space.subschemeι` present an
  immersed subscheme of `U` as an object of the site over `U`; this is possible because the
  size cutoff of the site is inherited by the source of an immersion.
* `AlgebraicGeometry.Space.atlasRelation`, with its two legs
  `AlgebraicGeometry.Space.atlasRelationTarget` and
  `AlgebraicGeometry.Space.atlasRelationSource`, is the relation `R = U ×_X U` of a chart, and
  `AlgebraicGeometry.Space.IsInvariantSubscheme` is invariance of a subscheme of `U` under it.
* `AlgebraicGeometry.Space.invariantSubspace` is the subfunctor of `X` cut out by a subscheme
  of the chart.
* `AlgebraicGeometry.Space.InvariantLocallyClosedSubscheme` and
  `AlgebraicGeometry.Space.LocallyClosedQuotientSubspace` are the two sides of the bijection.

## Main results

* `AlgebraicGeometry.Space.preimage_invariantSubspace` is the characterising property of the
  construction: the preimage along `φ` of the subspace cut out by an invariant subscheme `Z`
  is the functor of points of `Z`.
* `AlgebraicGeometry.Space.exists_invariantSubspace_eq` is its surjectivity: every locally
  closed subspace of `X` is cut out by its own base change to `U`.
* `AlgebraicGeometry.Space.subschemePoints_injective` is its injectivity: an immersed
  subscheme of `U` is determined by its functor of points.
* `AlgebraicGeometry.Space.invariantLocallyClosedSubschemeEquiv` is the bijection of Stacks
  07TW, and `AlgebraicGeometry.Space.closed_iff` and `AlgebraicGeometry.Space.open_iff` are
  its compatibility with closedness and with openness.
* `CategoryTheory.Subfunctor.isPullback_fromPreimage`,
  `CategoryTheory.Subfunctor.isIso_lift` and `CategoryTheory.Subfunctor.mem_obj_iff_exists`
  are the three facts about subfunctors of a presheaf of types which the construction needs
  and which Mathlib does not have.

## Implementation notes

The bijection is assembled with `Equiv.ofBijective` from the map which sends an invariant
subscheme to the subspace it cuts out. Its inverse is therefore not given by a formula, but
nothing is lost: surjectivity is proved by exhibiting the base change of a subspace to the
chart as a preimage of that map, which is the inverse construction of the source, and the
characterising property of the subtype is the defining equation of the forward map.

That the forward map lands in the locally closed subspaces is the only step which is not
formal. It is Stacks 03I2 at the property `IsImmersion`, which rests on the effective fppf
descent of immersions, Stacks 02W8. This library does not have that descent, so it is carried
as the explicit hypothesis
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale B S hS @IsImmersion` of
`AlgebraicGeometry.Space.invariantLocallyClosedSubschemeEquiv`, exactly as
`AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent`
carries it.
No further descent hypothesis is needed: `AlgebraicGeometry.Space.closed_iff` and
`AlgebraicGeometry.Space.open_iff` only have to descend the *property* along the chart, not
the object, and that is
`AlgebraicGeometry.Space.presheaf_invariantSubspace_of_isLocalAtTarget`, which runs on
`CategoryTheory.MorphismProperty.IsLocalAtTarget` for the fpqc precoverage — available for
closed immersions from `Stacks.Descent.isClosedImmersion_isLocalAtTarget_fpqc` and for open
immersions from `Stacks.Descent.isLocalAtTarget_fpqcPrecoverage` together with Mathlib's fppf
descent of open immersions.

The three statements of Stacks 07TW are proved here *under* effective descent for immersions.
That descent is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isImmersion`, and the three
statements with the hypothesis supplied, which carry the tag, are
`AlgebraicGeometry.Space.invariantLocallyClosedSubschemeEquiv_of_isAlgebraicSpace`,
`AlgebraicGeometry.Space.closed_iff_of_isAlgebraicSpace` and
`AlgebraicGeometry.Space.open_iff_of_isAlgebraicSpace` in
`StacksFrontier/AlgebraicGeometry/Descent/ImmersionEtaleDescent.lean`.

The sheaf condition of `AlgebraicGeometry.Space.invariantSubspace` reduces to the statement
that factoring through an immersion is local for the fppf topology. That is obtained without
any descent argument: an immersed subscheme of `U` is again an object of the site, by the size
bounds of Stacks 000R, so its functor of points is a sheaf by subcanonicality of the big fppf
site, and `CategoryTheory.Subfunctor.isSheaf_iff` turns the sheaf condition into exactly the
required locality.

The defining condition of `AlgebraicGeometry.Space.invariantSubspace` quantifies over *all*
lifts of a section to the chart, after an arbitrary base change, rather than over the
canonical lift given by the represented fibre product. Both the subfunctor condition and the
locality are then immediate, and the comparison with the functor of points of `Z` needs only
the universal property of `R = U ×_X U` and the invariance of `Z`, and in particular neither
the unit of the relation nor its being an equivalence relation.

## References

* [Stacks Project, Tag 07TW](https://stacks.math.columbia.edu/tag/07TW)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03BC](https://stacks.math.columbia.edu/tag/03BC)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Subfunctor

/-- The preimage of a subfunctor along a morphism of type-valued functors is a fibre
product. -/
@[sga "3 VIB 6.2.4" "Example 6.2.4 a)"]
theorem isPullback_fromPreimage {C : Type u} [Category.{v} C] {F G : C ⥤ Type v}
    (W : Subfunctor G) (p : F ⟶ G) :
    IsPullback (W.fromPreimage p) ((W.preimage p).ι) W.ι p := by
  have hsq : CommSq (W.fromPreimage p) ((W.preimage p).ι) W.ι p := ⟨W.fromPreimage_ι p⟩
  have hle : Subfunctor.range (Limits.pullback.snd W.ι p) ≤ W.preimage p := by
    rintro T y ⟨z, rfl⟩
    have h := ConcreteCategory.congr_hom
      (congr_app (Limits.pullback.condition (f := W.ι) (g := p)) T) z
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
    change p.app T _ ∈ W.obj T
    rw [← h]
    exact ((Limits.pullback.fst W.ι p).app T z).2
  refine IsPullback.of_iso_pullback hsq
    ⟨Limits.pullback.lift (W.fromPreimage p) ((W.preimage p).ι) (W.fromPreimage_ι p),
      Subfunctor.lift (Limits.pullback.snd W.ι p) hle, ?_, ?_⟩
    (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)
  · rw [← cancel_mono (W.preimage p).ι, Category.assoc, Subfunctor.lift_ι,
      Limits.pullback.lift_snd, Category.id_comp]
  · apply Limits.pullback.hom_ext
    · rw [← cancel_mono W.ι]
      simp only [Category.assoc, Category.id_comp, Limits.pullback.lift_fst_assoc,
        W.fromPreimage_ι p, Subfunctor.lift_ι_assoc, ← Limits.pullback.condition]
    · rw [Category.assoc, Limits.pullback.lift_snd, Subfunctor.lift_ι, Category.id_comp]

/-- A subfunctor which is the range of a monomorphism is isomorphic to the source of that
monomorphism. -/
theorem isIso_lift {C : Type u} [Category.{v} C] {F G : C ⥤ Type v}
    {W : Subfunctor G} {p : F ⟶ G} [Mono p] (h : Subfunctor.range p ≤ W)
    (h' : W ≤ Subfunctor.range p) : IsIso (Subfunctor.lift p h) := by
  have hmono : Mono (Subfunctor.lift p h) := mono_of_mono_fac (Subfunctor.lift_ι p h)
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  rw [isIso_iff_bijective]
  refine ⟨?_, ?_⟩
  · rw [← mono_iff_injective]
    exact (NatTrans.mono_iff_mono_app _).1 hmono T
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := h' T hy
    exact ⟨z, Subtype.ext hz⟩

/-- A section of a presheaf, presented as a morphism from a representable presheaf, lies in a
subfunctor exactly when that morphism factors through the subfunctor. -/
theorem mem_obj_iff_exists {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type v} (V : Subfunctor F)
    {T : C} (ψ : yoneda.obj T ⟶ F) :
    yonedaEquiv ψ ∈ V.obj (Opposite.op T) ↔
      ∃ χ : yoneda.obj T ⟶ V.toFunctor, χ ≫ V.ι = ψ := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ : ∃ y : V.toFunctor.obj (Opposite.op T),
        (y : F.obj (Opposite.op T)) = yonedaEquiv ψ := ⟨⟨yonedaEquiv ψ, h⟩, rfl⟩
    refine ⟨yonedaEquiv.symm y, ?_⟩
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨χ, rfl⟩
    rw [yonedaEquiv_comp]
    exact (yonedaEquiv χ).2

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The functor of points of a subscheme of an object of the site -/

section Subscheme

variable {U : BigFppfOver B S hS}

/-- The functor of points of a subscheme of an object `U` of the site, as a subfunctor of the
functor of points of `U`. -/
def subschemePoints (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U)) :
    Subfunctor (yoneda.obj U) where
  obj T := {f | ∃ g : (BigFppfOver.toScheme B S hS).obj T.unop ⟶ (Z : Scheme.{u}),
    g ≫ Z.arrow = (BigFppfOver.toScheme B S hS).map f}
  map := by
    intro T T' i f ⟨g, hg⟩
    refine ⟨(BigFppfOver.toScheme B S hS).map i.unop ≫ g, ?_⟩
    simp only [Category.assoc, hg, ← Functor.map_comp]
    rfl

/-- A morphism of the site is a point of a subscheme of its target exactly when the underlying
morphism of schemes factors through that subscheme. -/
theorem mem_subschemePoints_iff {Z : Subobject ((BigFppfOver.toScheme B S hS).obj U)}
    {T : (BigFppfOver B S hS)ᵒᵖ} (f : (yoneda.obj U).obj T) :
    f ∈ (subschemePoints B S hS Z).obj T ↔
      Z.Factors ((BigFppfOver.toScheme B S hS).map f) :=
  (Subobject.factors_iff _ _).symm

/-- The source of an immersion into a scheme of a big fppf site again lies in that site: an
immersion factors as a closed immersion into an open subscheme, and the size cutoff is
inherited by both. -/
theorem contains_of_isImmersion {T Y : Scheme.{u}} (hY : B.Contains Y) (f : T ⟶ Y)
    [AlgebraicGeometry.IsImmersion f] : B.Contains T :=
  Scheme.size_lt_of_isClosedImmersion f.liftCoborder
    (Scheme.size_lt_of_isOpenImmersion f.coborderRange.ι hY)

variable (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (hZ : AlgebraicGeometry.IsImmersion Z.arrow)

/-- An immersed subscheme of an object `U` of the site, as an object of the site over the
structure morphism of `U`. -/
noncomputable def subschemeObject : BigFppfOver B S hS :=
  haveI := hZ
  Over.mk (⟨Z.arrow ≫ U.hom.hom⟩ :
    B.obj (contains_of_isImmersion B U.left.2 Z.arrow) ⟶ B.obj hS)

/-- The inclusion of an immersed subscheme of `U` into `U`, as a morphism of the site. -/
noncomputable def subschemeι : subschemeObject B S hS Z hZ ⟶ U :=
  Over.homMk (⟨Z.arrow⟩) rfl

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.subschemeι` is the arrow of
the subobject. -/
@[simp]
theorem toScheme_map_subschemeι :
    (BigFppfOver.toScheme B S hS).map (subschemeι B S hS Z hZ) = Z.arrow := rfl

include hZ in
/-- An immersed subscheme of an object of the site is presented, up to an isomorphism of
schemes, by a morphism of the site. -/
theorem exists_presentation : ∃ (V : BigFppfOver B S hS) (i : V ⟶ U)
    (e : (BigFppfOver.toScheme B S hS).obj V ≅ (Z : Scheme.{u})),
      e.hom ≫ Z.arrow = (BigFppfOver.toScheme B S hS).map i :=
  ⟨subschemeObject B S hS Z hZ, subschemeι B S hS Z hZ, Iso.refl _, Category.id_comp _⟩

end Subscheme

/-! ### Subschemes presented by a morphism of the site -/

section Presented

variable {U V : BigFppfOver B S hS}
    {Z : Subobject ((BigFppfOver.toScheme B S hS).obj U)} (i : V ⟶ U)
    (e : (BigFppfOver.toScheme B S hS).obj V ≅ (Z : Scheme.{u}))
    (he : e.hom ≫ Z.arrow = (BigFppfOver.toScheme B S hS).map i)

include he in
/-- The underlying morphism of schemes of a presenting morphism is a monomorphism. -/
theorem mono_toScheme_map_of_presentation :
    Mono ((BigFppfOver.toScheme B S hS).map i) := by
  rw [← he]
  infer_instance

include he in
/-- A presenting morphism of the site has exactly the properties, stable under isomorphism, of
the arrow of the subscheme it presents. -/
theorem property_toScheme_map_iff_of_presentation (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] :
    P ((BigFppfOver.toScheme B S hS).map i) ↔ P Z.arrow := by
  rw [← he]
  exact MorphismProperty.cancel_left_of_respectsIso P _ _

include he in
/-- Factoring through a presented subscheme of `U` is factoring through the presenting
morphism. -/
theorem factors_iff_exists_comp {T : Scheme.{u}}
    (k : T ⟶ (BigFppfOver.toScheme B S hS).obj U) :
    Z.Factors k ↔ ∃ g : T ⟶ (BigFppfOver.toScheme B S hS).obj V,
      g ≫ (BigFppfOver.toScheme B S hS).map i = k := by
  refine ⟨fun h => ⟨Z.factorThru k h ≫ e.inv, ?_⟩, fun ⟨g, hg⟩ => ?_⟩
  · rw [← he, Category.assoc, e.inv_hom_id_assoc]
    exact Subobject.factorThru_arrow _ _ _
  · rw [← hg, ← he, ← Category.assoc]
    exact Subobject.factors_comp_arrow _

include he in
/-- The functor of points of a subscheme of `U` presented by a morphism `i` of the site is
the range of the functor of points of `i`. -/
theorem subschemePoints_eq_range :
    subschemePoints B S hS Z = Subfunctor.range (yoneda.map i) := by
  have hwi : (BigFppfOver.toScheme B S hS).map i ≫ U.hom.hom = V.hom.hom :=
    congrArg (fun m => m.hom) (Over.w i)
  refine le_antisymm ?_ ?_
  · intro T f hf
    obtain ⟨g, hg⟩ :=
      (factors_iff_exists_comp B S hS i e he _).1 ((mem_subschemePoints_iff B S hS f).1 hf)
    refine ⟨Over.homMk (⟨g⟩ : T.unop.left ⟶ V.left) ?_, ?_⟩
    · ext
      change g ≫ V.hom.hom = T.unop.hom.hom
      rw [← hwi, ← Category.assoc, hg]
      exact congrArg (fun m => m.hom) (Over.w f)
    · apply Over.OverMorphism.ext
      ext
      exact hg
  · rintro T f ⟨h, rfl⟩
    refine (mem_subschemePoints_iff B S hS _).2
      ((factors_iff_exists_comp B S hS i e he _).2 ?_)
    exact ⟨(BigFppfOver.toScheme B S hS).map h,
      ((BigFppfOver.toScheme B S hS).map_comp h i).symm⟩

include he in
/-- The functor of points of a presented subscheme of `U` is an fppf sheaf, by
subcanonicality of the big fppf site. -/
theorem isSheaf_subschemePoints :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (subschemePoints B S hS Z).toFunctor := by
  have h₁ : Mono i := (BigFppfOver.toScheme B S hS).mono_of_mono_map
    (mono_toScheme_map_of_presentation B S hS i e he)
  have h₂ : Mono (yoneda.map i) := inferInstance
  rw [subschemePoints_eq_range B S hS i e he]
  exact (Presheaf.isSheaf_of_iso_iff (asIso (Subfunctor.toRange (yoneda.map i)))).1
    (BigFppfOver.isSheaf_yoneda_obj B S hS V)

include he in
/-- Factoring through a presented subscheme of `U` is local for the fppf topology. -/
theorem mem_subschemePoints_of_sieveOfSection {T : BigFppfOver B S hS} (f : T ⟶ U)
    (hf : (subschemePoints B S hS Z).sieveOfSection (U := op T) f ∈
      BigFppfOver.topology B S hS T) :
    f ∈ (subschemePoints B S hS Z).obj (op T) :=
  ((Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type _ _).1
      (BigFppfOver.isSheaf_yoneda_obj B S hS U))).1
    ((isSheaf_iff_isSheaf_of_type _ _).1
      (isSheaf_subschemePoints B S hS i e he))) _ f hf

end Presented

/-! ### Covering sieves generated by a single morphism -/

/-- A morphism of the underlying category of a big fppf site whose singleton presieve is an fppf
covering of schemes generates a covering sieve. -/
theorem sieve_generate_singleton_mem_topology_of_fppfPrecoverage {T' T : B.Schemes} (q : T' ⟶ T)
    (hq : Presieve.singleton (B.inclusion.map q) ∈
      Scheme.fppfPrecoverage (B.inclusion.obj T)) :
    Sieve.generate (Presieve.singleton q) ∈ B.topology T := by
  have hE : IsFppfCovering (⟨T, PreZeroHypercover.singleton q⟩ : Covering B.Schemes) := by
    change (PreZeroHypercover.singleton q).presieve₀.map B.inclusion ∈
      Scheme.fppfPrecoverage (B.inclusion.obj T)
    simpa only [PreZeroHypercover.presieve₀_singleton, Presieve.map_singleton] using hq
  obtain ⟨E', hE', hEquiv⟩ := B.fppf_has_representative _ hE
  have hpre : (PreZeroHypercover.singleton q).presieve₀ ∈ B.precoverage T := by
    obtain ⟨hT, hComb⟩ := hEquiv
    cases hT
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb]
    exact ⟨E'.2, rfl, hE'⟩
  simpa [PreZeroHypercover.presieve₀_singleton] using
    Precoverage.generate_mem_toGrothendieck hpre

/-- A surjective étale morphism of the underlying category of a big fppf site generates a
covering sieve. -/
theorem sieve_generate_singleton_mem_topology {T' T : B.Schemes} (q : T' ⟶ T)
    (hqs : Surjective (B.inclusion.map q)) (hqe : Etale (B.inclusion.map q)) :
    Sieve.generate (Presieve.singleton q) ∈ B.topology T := by
  refine sieve_generate_singleton_mem_topology_of_fppfPrecoverage B q ?_
  refine Scheme.etalePrecoverage_le_fppfPrecoverage _ ?_
  have : Surjective (B.inclusion.map q) := hqs
  exact (Scheme.singleton_mem_precoverage_iff (@Etale.{u} : MorphismProperty Scheme.{u})
    (B.inclusion.map q)).2 ⟨Scheme.Hom.surjective _, hqe⟩

/-- A surjective flat morphism locally of finite presentation of the underlying category of a
big fppf site generates a covering sieve. This is the fppf-topology counterpart of
`AlgebraicGeometry.Space.sieve_generate_singleton_mem_topology`: it asks of the morphism only
what the fppf precoverage asks, and so applies to a morphism which is not étale. -/
theorem sieve_generate_singleton_mem_topology_of_flat {T' T : B.Schemes} (q : T' ⟶ T)
    (hqs : Surjective (B.inclusion.map q)) (hqf : Flat (B.inclusion.map q))
    (hqp : LocallyOfFinitePresentation (B.inclusion.map q)) :
    Sieve.generate (Presieve.singleton q) ∈ B.topology T := by
  refine sieve_generate_singleton_mem_topology_of_fppfPrecoverage B q ?_
  have : Surjective (B.inclusion.map q) := hqs
  exact (Scheme.singleton_mem_precoverage_iff
    (@Flat.{u} ⊓ @LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    (B.inclusion.map q)).2 ⟨Scheme.Hom.surjective _, hqf, hqp⟩

/-- A morphism of the big fppf site of `S` whose singleton presieve is an fppf covering of
schemes generates a covering sieve. -/
theorem sieve_generate_singleton_mem_topology_over_of_fppfPrecoverage
    {T' T : BigFppfOver B S hS} (q : T' ⟶ T)
    (hq : Presieve.singleton (B.inclusion.map ((BigFppfOver.forget B S hS).map q)) ∈
      Scheme.fppfPrecoverage (B.inclusion.obj ((BigFppfOver.forget B S hS).obj T))) :
    Sieve.generate (Presieve.singleton q) ∈ BigFppfOver.topology B S hS T := by
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (B.topology.overEquiv_symm_mem_over T _
      (sieve_generate_singleton_mem_topology_of_fppfPrecoverage B
        ((BigFppfOver.forget B S hS).map q) hq))
  intro W k hk
  have hk₀ : Sieve.generate
      (Presieve.singleton ((BigFppfOver.forget B S hS).map q)) k.left := by simpa using hk
  obtain ⟨Y, a₀, b₀, hb₀, hfac₀⟩ := hk₀
  cases hb₀
  refine ⟨T', Over.homMk a₀ ?_, q, Presieve.singleton.mk, Over.OverMorphism.ext hfac₀⟩
  calc a₀ ≫ T'.hom = a₀ ≫ q.left ≫ T.hom := by rw [← Over.w q]
    _ = (a₀ ≫ (BigFppfOver.forget B S hS).map q) ≫ T.hom := by rw [← Category.assoc]; rfl
    _ = k.left ≫ T.hom := by rw [hfac₀]
    _ = W.hom := Over.w k

/-- A surjective étale morphism of the big fppf site of `S` generates a covering sieve. -/
theorem sieve_generate_singleton_mem_topology_over {T' T : BigFppfOver B S hS} (q : T' ⟶ T)
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q)) :
    Sieve.generate (Presieve.singleton q) ∈ BigFppfOver.topology B S hS T := by
  refine sieve_generate_singleton_mem_topology_over_of_fppfPrecoverage B S hS q ?_
  refine Scheme.etalePrecoverage_le_fppfPrecoverage _ ?_
  have : Surjective ((BigFppfOver.toScheme B S hS).map q) := hqs
  exact (Scheme.singleton_mem_precoverage_iff (@Etale.{u} : MorphismProperty Scheme.{u})
    ((BigFppfOver.toScheme B S hS).map q)).2 ⟨Scheme.Hom.surjective _, hqe⟩

/-- A surjective flat morphism locally of finite presentation of the big fppf site of `S`
generates a covering sieve. This is the hypothesis under which a sheaf on the site is a sheaf
for a single morphism, asked of a morphism which need not be étale: it is what the fppf
precoverage itself asks, together with surjectivity. -/
theorem sieve_generate_singleton_mem_topology_over_of_flat {T' T : BigFppfOver B S hS}
    (q : T' ⟶ T) (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q)) :
    Sieve.generate (Presieve.singleton q) ∈ BigFppfOver.topology B S hS T := by
  refine sieve_generate_singleton_mem_topology_over_of_fppfPrecoverage B S hS q ?_
  have : Surjective ((BigFppfOver.toScheme B S hS).map q) := hqs
  exact (Scheme.singleton_mem_precoverage_iff
    (@Flat.{u} ⊓ @LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    ((BigFppfOver.toScheme B S hS).map q)).2 ⟨Scheme.Hom.surjective _, hqf, hqp⟩

/-! ### The subspace cut out by a subscheme of a chart -/

section Invariant

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
    {φ : yoneda.obj U ⟶ X}

/-- The subfunctor of `X` cut out by a subscheme `Z` of a chart `U` of `X`: a section `x` of
`X` lies in it exactly when every lift of `x` to `U` factors through `Z`. -/
def invariantSubspace (φ : yoneda.obj U ⟶ X)
    (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U)) : Subfunctor X where
  obj T := {x | ∀ (T' : BigFppfOver B S hS) (g : T' ⟶ T.unop) (f : T' ⟶ U),
    φ.app (op T') f = X.map g.op x → f ∈ (subschemePoints B S hS Z).obj (op T')}
  map := by
    intro T T' i x hx T'' g f hf
    refine hx T'' (g ≫ i.unop) f ?_
    rw [hf, ← Functor.map_comp_apply]
    rfl

variable (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)

/-- The scheme of arrows of the relation `R = U ×_X U` presented by a chart `φ` of `X`. -/
noncomputable abbrev atlasRelation : BigFppfOver B S hS := hs.rep.pullback φ

/-- The target map of the relation presented by a chart of `X`. -/
noncomputable abbrev atlasRelationTarget : atlasRelation B S hS hs ⟶ U :=
  yoneda.preimage (hs.rep.fst φ)

/-- The source map of the relation presented by a chart of `X`. -/
noncomputable abbrev atlasRelationSource : atlasRelation B S hS hs ⟶ U := hs.rep.snd φ

/-- A subscheme of `U` is invariant under the relation `R = U ×_X U` when its two pullbacks
to `R` agree. This is part (4) of Stacks 03BC for the canonical groupoid of the relation. -/
abbrev IsInvariantSubscheme (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U)) : Prop :=
  (Subobject.pullback ((BigFppfOver.toScheme B S hS).map
      (atlasRelationTarget B S hS hs))).obj Z =
    (Subobject.pullback ((BigFppfOver.toScheme B S hS).map
      (atlasRelationSource B S hS hs))).obj Z

include hs in
/-- The preimage along the chart `φ` of the subspace cut out by `Z` is the functor of points
of `Z` itself. The inclusion which uses the invariance of `Z` is the nontrivial one. -/
theorem preimage_invariantSubspace (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (hinv : IsInvariantSubscheme B S hS hs Z) :
    (invariantSubspace B S hS φ Z).preimage φ = subschemePoints B S hS Z := by
  refine le_antisymm (fun T f hf => ?_) (fun T f hf => ?_)
  · exact hf T.unop (𝟙 _) f (by simp)
  · intro T' g f' hcomm
    have hnat : φ.app (op T') (g ≫ f) = X.map g.op (φ.app T f) :=
      NatTrans.naturality_apply φ g.op f
    have hw : yoneda.map f' ≫ φ = yoneda.map (g ≫ f) ≫ φ := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map,
        hcomm, ← hnat]
    have h1 : hs.rep.lift' f' (g ≫ f) hw ≫ atlasRelationTarget B S hS hs = f' :=
      hs.rep.lift'_fst _ _ _
    have h2 : hs.rep.lift' f' (g ≫ f) hw ≫ atlasRelationSource B S hS hs = g ≫ f :=
      hs.rep.lift'_snd _ _ _
    rw [mem_subschemePoints_iff, ← h1, Functor.map_comp,
      ← CategoryTheory.Limits.pullback_factors_iff, hinv,
      CategoryTheory.Limits.pullback_factors_iff, ← Functor.map_comp, h2, Functor.map_comp]
    exact Subobject.factors_of_factors_right _
      ((mem_subschemePoints_iff B S hS f).1 hf)

/-- A point of the preimage of a subfunctor along a chart is a factorisation of the
corresponding morphism through the subfunctor. -/
theorem mem_preimage_iff {V : Subfunctor X} (p : yoneda.obj U ⟶ X)
    {T : BigFppfOver B S hS} (f : T ⟶ U) :
    f ∈ (V.preimage p).obj (op T) ↔
      ∃ χ : yoneda.obj T ⟶ V.toFunctor, χ ≫ V.ι = yoneda.map f ≫ p := by
  have h0 : yonedaEquiv (yoneda.map f ≫ p) = p.app (op T) f := by
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  rw [Subfunctor.preimage_obj, Set.mem_preimage, ← h0, Subfunctor.mem_obj_iff_exists]

/-- The preimage of a representable subspace along a chart is the functor of points of the
represented base change. -/
theorem range_yoneda_snd_eq_preimage {V : Subfunctor X} (p : yoneda.obj U ⟶ X)
    (hVi : yoneda.relativelyRepresentable V.ι) :
    Subfunctor.range (yoneda.map (hVi.snd p)) = V.preimage p := by
  refine le_antisymm (fun T f hf => ?_) (fun T f hf => ?_)
  · obtain ⟨h, rfl⟩ := hf
    refine (mem_preimage_iff B S hS p _).2 ⟨yoneda.map h ≫ hVi.fst p, ?_⟩
    rw [Category.assoc, hVi.w p, ← Category.assoc, ← Functor.map_comp]
    rfl
  · obtain ⟨χ, hχ⟩ := (mem_preimage_iff B S hS p f).1 hf
    exact ⟨hVi.lift χ f hχ, hVi.lift_snd χ f hχ⟩

/-- The base change along `yoneda.map r ≫ p` of a representable morphism into `X` is the base
change along `r` of its base change along `p`. -/
theorem exists_isPullback_snd_comp {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : G ⟶ X}
    (hf : yoneda.relativelyRepresentable f) {A A' : BigFppfOver B S hS}
    (p : yoneda.obj A ⟶ X) (r : A' ⟶ A) (ψ : yoneda.obj A' ⟶ X)
    (hψ : yoneda.map r ≫ p = ψ) :
    ∃ l : hf.pullback ψ ⟶ hf.pullback p,
      IsPullback ((BigFppfOver.toScheme B S hS).map l)
        ((BigFppfOver.toScheme B S hS).map (hf.snd ψ))
        ((BigFppfOver.toScheme B S hS).map (hf.snd p))
        ((BigFppfOver.toScheme B S hS).map r) := by
  subst hψ
  have hw : hf.fst (yoneda.map r ≫ p) ≫ f =
      yoneda.map (hf.snd (yoneda.map r ≫ p) ≫ r) ≫ p := by
    rw [hf.w, Functor.map_comp, Category.assoc]
  have hlfst : yoneda.map (hf.lift (hf.fst (yoneda.map r ≫ p))
      (hf.snd (yoneda.map r ≫ p) ≫ r) hw) ≫ hf.fst p =
      hf.fst (yoneda.map r ≫ p) := hf.lift_fst _ _ _
  have hlsnd : hf.lift (hf.fst (yoneda.map r ≫ p))
      (hf.snd (yoneda.map r ≫ p) ≫ r) hw ≫ hf.snd p =
      hf.snd (yoneda.map r ≫ p) ≫ r := hf.lift_snd _ _ _
  have hsqp : IsPullback (yoneda.map (hf.lift (hf.fst (yoneda.map r ≫ p))
        (hf.snd (yoneda.map r ≫ p) ≫ r) hw))
      (yoneda.map (hf.snd (yoneda.map r ≫ p)))
      (yoneda.map (hf.snd p)) (yoneda.map r) := by
    refine IsPullback.of_right ?_ ?_ (hf.isPullback p)
    · rw [hlfst]; exact hf.isPullback (yoneda.map r ≫ p)
    · rw [← Functor.map_comp, ← Functor.map_comp, hlsnd]
  exact ⟨_, ((IsPullback.of_map_of_faithful yoneda hsqp)).map (BigFppfOver.toScheme B S hS)⟩

/-- The two base changes of a representable subspace of `X` to the relation of a chart, taken
along a morphism of the site and along the chart, agree with the base change along the
composite. -/
theorem pullback_obj_mk_snd {V : Subfunctor X} (p : yoneda.obj U ⟶ X)
    (hVi : yoneda.relativelyRepresentable V.ι)
    {R : BigFppfOver B S hS} (r : R ⟶ U) (ψ : yoneda.obj R ⟶ X)
    (hψ : yoneda.map r ≫ p = ψ)
    [Mono ((BigFppfOver.toScheme B S hS).map (hVi.snd p))]
    [Mono ((BigFppfOver.toScheme B S hS).map (hVi.snd ψ))] :
    (Subobject.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
        (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hVi.snd p)))
      = Subobject.mk ((BigFppfOver.toScheme B S hS).map (hVi.snd ψ)) :=
  Subobject.pullback_obj_mk (exists_isPullback_snd_comp B S hS hVi p r ψ hψ).choose_spec

/-- A property stable under base change passes from the base change of a representable
morphism along a chart to its base change along any morphism of the site over that chart. -/
theorem property_snd_comp {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : G ⟶ X}
    (hf : yoneda.relativelyRepresentable f) {A A' : BigFppfOver B S hS}
    (p : yoneda.obj A ⟶ X) (r : A' ⟶ A) (ψ : yoneda.obj A' ⟶ X)
    (hψ : yoneda.map r ≫ p = ψ)
    (hPp : P ((BigFppfOver.toScheme B S hS).map (hf.snd p))) :
    P ((BigFppfOver.toScheme B S hS).map (hf.snd ψ)) :=
  MorphismProperty.of_isPullback
    (exists_isPullback_snd_comp B S hS hf p r ψ hψ).choose_spec hPp

/-- A represented base change of a representable morphism has every property, stable under
isomorphism, of any other presentation of that base change. -/
theorem property_snd_of_isPullback {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : G ⟶ X}
    (hf : yoneda.relativelyRepresentable f) {A V : BigFppfOver B S hS}
    {p : yoneda.obj A ⟶ X} {i : V ⟶ A} {k : yoneda.obj V ⟶ G}
    (hsq : IsPullback k (yoneda.map i) f p)
    (hPi : P ((BigFppfOver.toScheme B S hS).map i)) :
    P ((BigFppfOver.toScheme B S hS).map (hf.snd p)) := by
  have hmap : yoneda.map (yoneda.preimage
      (hsq.isoIsPullback _ _ (hf.isPullback p)).hom) ≫ yoneda.map (hf.snd p) =
      yoneda.map i := by
    rw [yoneda.map_preimage]
    exact hsq.isoIsPullback_hom_snd _ _ (hf.isPullback p)
  have hcomp : yoneda.preimage (hsq.isoIsPullback _ _ (hf.isPullback p)).hom ≫ hf.snd p = i :=
    yoneda.map_injective (by rw [Functor.map_comp]; exact hmap)
  have hiso : IsIso (yoneda.map (yoneda.preimage
      (hsq.isoIsPullback _ _ (hf.isPullback p)).hom)) := by
    rw [yoneda.map_preimage]; infer_instance
  have hiso' : IsIso (yoneda.preimage (hsq.isoIsPullback _ _ (hf.isPullback p)).hom) :=
    isIso_of_reflects_iso _ yoneda
  rw [← hcomp, Functor.map_comp] at hPi
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).1 hPi

/-- The subspace cut out by an immersed subscheme of a chart is an fppf sheaf: its defining
condition is local, because factoring through an immersion is. -/
theorem isSheaf_invariantSubspace
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (hZ : AlgebraicGeometry.IsImmersion Z.arrow) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (invariantSubspace B S hS φ Z).toFunctor := by
  obtain ⟨V, i, e, he⟩ := exists_presentation B S hS Z hZ
  rw [isSheaf_iff_isSheaf_of_type,
    Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type _ _).1 hX)]
  intro T x hx T' g f hcomm
  refine mem_subschemePoints_of_sieveOfSection B S hS i e he f
    ((BigFppfOver.topology B S hS).superset_covering ?_
      ((BigFppfOver.topology B S hS).pullback_stable g hx))
  intro W k hk
  refine hk W (𝟙 W) (k ≫ f) ?_
  rw [op_id, Functor.map_id_apply, op_comp, Functor.map_comp_apply, ← hcomm]
  exact NatTrans.naturality_apply φ k.op f

variable (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)

include hs in
/-- The base change along the chart `φ` of the inclusion of the subspace cut out by an
invariant immersed subscheme `Z` of `U` is the functor of points of a presenting morphism
of `Z`. -/
theorem exists_isPullback_yoneda_presentation
    (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (hinv : IsInvariantSubscheme B S hS hs Z) {V : BigFppfOver B S hS} (i : V ⟶ U)
    (e : (BigFppfOver.toScheme B S hS).obj V ≅ (Z : Scheme.{u}))
    (hei : e.hom ≫ Z.arrow = (BigFppfOver.toScheme B S hS).map i) :
    ∃ k : yoneda.obj V ⟶ (invariantSubspace B S hS φ Z).toFunctor,
      IsPullback k (yoneda.map i) (invariantSubspace B S hS φ Z).ι φ := by
  have hmono : Mono i := (BigFppfOver.toScheme B S hS).mono_of_mono_map
    (mono_toScheme_map_of_presentation B S hS i e hei)
  have hmi : Mono (yoneda.map i) := inferInstance
  have key : (invariantSubspace B S hS φ Z).preimage φ = Subfunctor.range (yoneda.map i) :=
    (preimage_invariantSubspace B S hS hs Z hinv).trans
      (subschemePoints_eq_range B S hS i e hei)
  have hkι : Subfunctor.lift (yoneda.map i) key.ge ≫
      ((invariantSubspace B S hS φ Z).preimage φ).ι = yoneda.map i := Subfunctor.lift_ι _ _
  have hkiso := Subfunctor.isIso_lift key.ge key.le
  have h₁ := Subfunctor.isPullback_fromPreimage (invariantSubspace B S hS φ Z) φ
  refine ⟨Subfunctor.lift (yoneda.map i) key.ge ≫
    (invariantSubspace B S hS φ Z).fromPreimage φ, ?_⟩
  refine IsPullback.of_iso_pullback
    ⟨by rw [Category.assoc, (invariantSubspace B S hS φ Z).fromPreimage_ι φ,
      ← Category.assoc, hkι]⟩
    (asIso (Subfunctor.lift (yoneda.map i) key.ge) ≪≫ h₁.isoPullback) ?_ ?_
  · simp [h₁.isoPullback_hom_fst]
  · simp [h₁.isoPullback_hom_snd, hkι]

include hs he in
/-- For a property `P` of scheme morphisms satisfying effective descent along surjective
étale morphisms of the site, the subspace cut out by an invariant subscheme `Z` of a
surjective étale chart `U` of `X` is an algebraic space and its inclusion into `X` is
representable with `P`, as soon as `Z ⟶ U` has `P`.

This is Stacks 03I2 applied to the inclusion; its hypothesis `hdesc` is the only input which
is not formal.  The containment of `P` in the monomorphisms was dropped along with the same
vestigial hypothesis on 03I2 itself: the proof never used it. -/
theorem isAlgebraicSpace_and_presheaf_invariantSubspace
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS P)
    (hX : IsAlgebraicSpace B S hS X)
    (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (hZ : AlgebraicGeometry.IsImmersion Z.arrow) (hPZ : P Z.arrow)
    (hinv : IsInvariantSubscheme B S hS hs Z) :
    IsAlgebraicSpace B S hS (invariantSubspace B S hS φ Z).toFunctor ∧
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
        (invariantSubspace B S hS φ Z).ι := by
  have hRI : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hRI' : (MorphismProperty.presheaf
      (P.inverseImage (BigFppfOver.toScheme B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
      (P.inverseImage (BigFppfOver.toScheme B S hS))).respectsIso
  obtain ⟨V, i, e, hei⟩ := exists_presentation B S hS Z hZ
  obtain ⟨k, h₂⟩ := exists_isPullback_yoneda_presentation B S hS hs Z hinv i e hei
  have hPι : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map i) :=
    presheaf_yoneda_map_of_inverseImage B S hS inferInstance _
      ((property_toScheme_map_iff_of_presentation B S hS i e hei P).2 hPZ)
  have hV : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (Limits.pullback.snd (invariantSubspace B S hS φ Z).ι φ) := by
    refine (MorphismProperty.arrow_mk_iso_iff _
      (Arrow.isoMk (h₂.isoIsPullback _ _
        (IsPullback.of_hasPullback (invariantSubspace B S hS φ Z).ι φ)) (Iso.refl _) ?_)).1 hPι
    simp
  exact isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent hdesc
    (isSheaf_invariantSubspace B S hS hX.isSheaf Z hZ) hX hs he hV

include hs he in
/-- The second half of Stacks 07TW for a property which is fppf-local on the target. Unlike
`AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_invariantSubspace` this needs no
effective descent: the representability of the inclusion is assumed, and only the property is
descended, along the surjective étale covering furnished by the chart. -/
theorem presheaf_invariantSubspace_of_isLocalAtTarget
    {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget Scheme.fpqcPrecoverage]
    (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (hZ : AlgebraicGeometry.IsImmersion Z.arrow) (hPZ : P Z.arrow)
    (hinv : IsInvariantSubscheme B S hS hs Z)
    (hrep : yoneda.relativelyRepresentable (invariantSubspace B S hS φ Z).ι) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (invariantSubspace B S hS φ Z).ι := by
  have hRI : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hRI' : (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hloc : P.IsLocalAtTarget Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  obtain ⟨V, i, e, hei⟩ := exists_presentation B S hS Z hZ
  obtain ⟨k, h₂⟩ := exists_isPullback_yoneda_presentation B S hS hs Z hinv i e hei
  have hPφ : P ((BigFppfOver.toScheme B S hS).map (hrep.snd φ)) :=
    property_snd_of_isPullback B S hS hrep h₂
      ((property_toScheme_map_iff_of_presentation B S hS i e hei P).2 hPZ)
  refine MorphismProperty.relative_of_snd hrep (fun a g => ?_)
  change P ((BigFppfOver.toScheme B S hS).map (hrep.snd g))
  have hqs : Surjective ((BigFppfOver.toScheme B S hS).map (hs.rep.snd g)) :=
    hs.property_snd g
  have hqe : Etale ((BigFppfOver.toScheme B S hS).map (hs.rep.snd g)) := he.property_snd g
  have hfl : Flat ((BigFppfOver.toScheme B S hS).map (hs.rep.snd g)) := inferInstance
  have hfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (hs.rep.snd g)) :=
    inferInstance
  have hr : yoneda.map (yoneda.preimage (hs.rep.fst g)) ≫ φ =
      yoneda.map (hs.rep.snd g) ≫ g := by
    rw [yoneda.map_preimage]
    exact hs.rep.w g
  have hPψ : P ((BigFppfOver.toScheme B S hS).map
      (hrep.snd (yoneda.map (hs.rep.snd g) ≫ g))) :=
    property_snd_comp B S hS hrep φ _ _ hr hPφ
  obtain ⟨l, hsq⟩ := exists_isPullback_snd_comp B S hS hrep g (hs.rep.snd g) _ rfl
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (Scheme.Hom.singleton_mem_fppfPrecoverage
      ((BigFppfOver.toScheme B S hS).map (hs.rep.snd g))) ?_
  intro Y g' _ hg'
  cases hg'
  rw [← hsq.isoPullback_inv_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso P hsq.isoPullback.inv _).2 hPψ

/-- An immersed subscheme of a chart of `X` is determined by its functor of points. -/
theorem subschemePoints_injective {Z₁ Z₂ : Subobject ((BigFppfOver.toScheme B S hS).obj U)}
    (hZ₁ : AlgebraicGeometry.IsImmersion Z₁.arrow)
    (hZ₂ : AlgebraicGeometry.IsImmersion Z₂.arrow)
    (h : subschemePoints B S hS Z₁ = subschemePoints B S hS Z₂) : Z₁ = Z₂ := by
  have key : ∀ (Y₁ Y₂ : Subobject ((BigFppfOver.toScheme B S hS).obj U))
      (hY₁ : AlgebraicGeometry.IsImmersion Y₁.arrow),
      subschemePoints B S hS Y₁ ≤ subschemePoints B S hS Y₂ → Y₁ ≤ Y₂ := by
    intro Y₁ Y₂ hY₁ hle
    refine Subobject.le_of_factors ?_
    have h₁ : subschemeι B S hS Y₁ hY₁ ∈
        (subschemePoints B S hS Y₁).obj (op (subschemeObject B S hS Y₁ hY₁)) :=
      (mem_subschemePoints_iff B S hS _).2 (Subobject.factors_self Y₁)
    exact (mem_subschemePoints_iff B S hS _).1 (hle _ h₁)
  exact le_antisymm (key _ _ hZ₁ h.le) (key _ _ hZ₂ h.ge)

/-- A subscheme of `U` which is the image of a monomorphism of the site has the same properties,
stable under isomorphism, as that monomorphism. -/
private theorem property_mk_arrow_iff {V U : BigFppfOver B S hS} {i : V ⟶ U}
    [Mono ((BigFppfOver.toScheme B S hS).map i)] (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] :
    P ((BigFppfOver.toScheme B S hS).map i) ↔
      P (Subobject.mk ((BigFppfOver.toScheme B S hS).map i)).arrow :=
  property_toScheme_map_iff_of_presentation B S hS i
    (Subobject.underlyingIso ((BigFppfOver.toScheme B S hS).map i)).symm
    (Subobject.underlyingIso_arrow ((BigFppfOver.toScheme B S hS).map i)) P

/-- A subscheme of `U` which is the image of a monomorphism of the site is an immersion exactly
when that monomorphism is. -/
private theorem isImmersion_mk_arrow_iff {V U : BigFppfOver B S hS} {i : V ⟶ U}
    [Mono ((BigFppfOver.toScheme B S hS).map i)] :
    AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map i) ↔
      AlgebraicGeometry.IsImmersion (Subobject.mk ((BigFppfOver.toScheme B S hS).map i)).arrow :=
  haveI : MorphismProperty.RespectsIso (@AlgebraicGeometry.IsImmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  property_mk_arrow_iff B S hS (@AlgebraicGeometry.IsImmersion.{u})

/-- The functor of points of the subscheme of `U` given by a base change of a representable
subspace along a chart is the preimage of that subspace. -/
private theorem subschemePoints_mk_snd {V : Subfunctor X} (p : yoneda.obj U ⟶ X)
    (hVi : yoneda.relativelyRepresentable V.ι)
    [Mono ((BigFppfOver.toScheme B S hS).map (hVi.snd p))] :
    subschemePoints B S hS (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hVi.snd p))) =
      V.preimage p := by
  rw [subschemePoints_eq_range B S hS _
    (Subobject.underlyingIso ((BigFppfOver.toScheme B S hS).map (hVi.snd p))).symm
    (Subobject.underlyingIso_arrow ((BigFppfOver.toScheme B S hS).map (hVi.snd p)))]
  exact range_yoneda_snd_eq_preimage B S hS p hVi

include hs in
/-- The two legs of the relation of a chart have the same composite with the chart. -/
theorem yoneda_map_atlasRelationSource_comp :
    yoneda.map (atlasRelationSource B S hS hs) ≫ φ =
      yoneda.map (atlasRelationTarget B S hS hs) ≫ φ := by
  rw [show yoneda.map (atlasRelationTarget B S hS hs) = hs.rep.fst φ from
    yoneda.map_preimage _]
  exact (hs.rep.w φ).symm

include hs he in
/-- Every locally closed subspace of `X` is cut out by an invariant immersed subscheme of a
surjective étale chart `U`: namely by its own base change to `U`. -/
theorem exists_invariantSubspace_eq (hX : IsAlgebraicSpace B S hS X)
    (W : Subfunctor X) (hW : IsLocallyClosedSubspace B S hS W) :
    ∃ Z : Subobject ((BigFppfOver.toScheme B S hS).obj U),
      (AlgebraicGeometry.IsImmersion Z.arrow ∧ IsInvariantSubscheme B S hS hs Z) ∧
        invariantSubspace B S hS φ Z = W := by
  have him : AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map (hW.2.rep.snd φ)) := hW.2.property_snd φ
  have himψ : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map
      (hW.2.rep.snd (yoneda.map (atlasRelationTarget B S hS hs) ≫ φ))) :=
    hW.2.property_snd _
  have hmono : Mono ((BigFppfOver.toScheme B S hS).map (hW.2.rep.snd φ)) := inferInstance
  have hmonoψ : Mono ((BigFppfOver.toScheme B S hS).map
      (hW.2.rep.snd (yoneda.map (atlasRelationTarget B S hS hs) ≫ φ))) := inferInstance
  refine ⟨Subobject.mk ((BigFppfOver.toScheme B S hS).map (hW.2.rep.snd φ)), ⟨?_, ?_⟩, ?_⟩
  · exact (isImmersion_mk_arrow_iff B S hS).1 him
  · exact (pullback_obj_mk_snd B S hS φ hW.2.rep (atlasRelationTarget B S hS hs) _ rfl).trans
      (pullback_obj_mk_snd B S hS φ hW.2.rep (atlasRelationSource B S hS hs) _
        (yoneda_map_atlasRelationSource_comp B S hS hs)).symm
  · refine le_antisymm (fun T x hx => ?_) (fun T x hx T' g f hcomm => ?_)
    · have h1 : yonedaEquiv (yoneda.map (yoneda.preimage (hs.rep.fst (yonedaEquiv.symm x)))
          ≫ φ) = φ.app (op (hs.rep.pullback (yonedaEquiv.symm x)))
            (yoneda.preimage (hs.rep.fst (yonedaEquiv.symm x))) := by
        rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      have h2 : yoneda.map (yoneda.preimage (hs.rep.fst (yonedaEquiv.symm x))) ≫ φ =
          yoneda.map (hs.rep.snd (yonedaEquiv.symm x)) ≫ yonedaEquiv.symm x := by
        rw [yoneda.map_preimage]
        exact hs.rep.w _
      have hlift : φ.app (op (hs.rep.pullback (yonedaEquiv.symm x)))
          (yoneda.preimage (hs.rep.fst (yonedaEquiv.symm x))) =
          X.map (hs.rep.snd (yonedaEquiv.symm x)).op x := by
        rw [← h1, h2, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]
      have hα := hx _ (hs.rep.snd (yonedaEquiv.symm x))
        (yoneda.preimage (hs.rep.fst (yonedaEquiv.symm x))) hlift
      rw [subschemePoints_mk_snd B S hS φ hW.2.rep, Subfunctor.preimage_obj, Set.mem_preimage,
      hlift] at hα
      refine ((Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type _ _).1 hX.isSheaf)).1
        ((isSheaf_iff_isSheaf_of_type _ _).1 hW.1.isSheaf)) T x ?_
      refine (BigFppfOver.topology B S hS).superset_covering ?_
        (sieve_generate_singleton_mem_topology_over B S hS
          (hs.rep.snd (yonedaEquiv.symm x)) (hs.property_snd _) (he.property_snd _))
      rintro V k ⟨Y, a, b, hb, hfac⟩
      cases hb
      change X.map k.op x ∈ W.obj (op V)
      rw [← hfac, op_comp, Functor.map_comp_apply]
      exact W.map a.op hα
    · rw [subschemePoints_mk_snd B S hS φ hW.2.rep, Subfunctor.preimage_obj, Set.mem_preimage,
        hcomm]
      exact W.map g.op hx

/-! ### The bijection of Stacks 07TW -/

/-- Immersions are monomorphisms. -/
theorem isImmersion_le_monomorphisms :
    (@AlgebraicGeometry.IsImmersion.{u}) ≤ MorphismProperty.monomorphisms Scheme.{u} :=
  fun _ _ f hf => by have := hf; exact (inferInstance : Mono f)

/-- Locally closed subschemes of a surjective étale chart `U` of `X`, invariant under the
relation `R = U ×_X U`. -/
noncomputable abbrev InvariantLocallyClosedSubscheme :=
  {Z : Subobject ((BigFppfOver.toScheme B S hS).obj U) //
    AlgebraicGeometry.IsImmersion Z.arrow ∧ IsInvariantSubscheme B S hS hs Z}

/-- Locally closed subspaces of `X`. -/
abbrev LocallyClosedQuotientSubspace :=
  {W : Subfunctor X // IsLocallyClosedSubspace B S hS W}

/-- For a fpqc-local property `P` of immersions, the subspace cut out by an invariant immersed
subscheme `Z` of the chart is an algebraic space with inclusion having `P` exactly when `Z ⟶ U`
has `P`. -/
private theorem isAlgebraicSpace_and_presheaf_iff
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fpqcPrecoverage]
    (hPI : P ≤ @AlgebraicGeometry.IsImmersion.{u})
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS (@AlgebraicGeometry.IsImmersion.{u}))
    (hX : IsAlgebraicSpace B S hS X) (Z : InvariantLocallyClosedSubscheme B S hS hs) :
    (IsAlgebraicSpace B S hS (invariantSubspace B S hS φ Z.1).toFunctor ∧
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
        (invariantSubspace B S hS φ Z.1).ι) ↔ P Z.1.arrow := by
  have hRI : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hle : IsLocallyClosedSubspace B S hS (invariantSubspace B S hS φ Z.1) :=
    isAlgebraicSpace_and_presheaf_invariantSubspace B S hS hs he hdesc
      hX Z.1 Z.2.1 Z.2.1 Z.2.2
  refine ⟨fun hc => ?_, fun hP => ⟨hle.1,
    presheaf_invariantSubspace_of_isLocalAtTarget B S hS hs he Z.1 Z.2.1 hP Z.2.2 hle.2.rep⟩⟩
  have hP : P ((BigFppfOver.toScheme B S hS).map (hc.2.rep.snd φ)) := hc.2.property_snd φ
  have hIm := hPI _ hP
  have hZeq : Subobject.mk ((BigFppfOver.toScheme B S hS).map (hc.2.rep.snd φ)) = Z.1 :=
    subschemePoints_injective B S hS
      ((isImmersion_mk_arrow_iff B S hS).1 hIm) Z.2.1
      ((subschemePoints_mk_snd B S hS φ hc.2.rep).trans
        (preimage_invariantSubspace B S hS hs Z.1 Z.2.2))
  rw [← hZeq]
  exact (property_mk_arrow_iff B S hS P).1 hP

include hs he in
/-- **Stacks 07TW**, the canonical bijection. For an algebraic space `X` over `S` with a
surjective étale chart `φ : U ⟶ X`, the invariant locally closed subschemes of `U` correspond
bijectively to the locally closed subspaces of `X`, and the bijection is characterised by
pullback along `φ`.

The hypothesis `hdesc` is effective descent of immersions along surjective étale morphisms of
the site, Stacks 02W8 in the form Stacks 03I2 consumes; see
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`. -/
noncomputable def invariantLocallyClosedSubschemeEquiv
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@AlgebraicGeometry.IsImmersion.{u}))
    (hX : IsAlgebraicSpace B S hS X) :
    {e : InvariantLocallyClosedSubscheme B S hS hs ≃
      LocallyClosedQuotientSubspace B S hS (X := X) //
      ∀ Z, ((e Z).1.preimage φ) = subschemePoints B S hS Z.1} := by
  refine ⟨Equiv.ofBijective (fun Z => ⟨invariantSubspace B S hS φ Z.1,
      isAlgebraicSpace_and_presheaf_invariantSubspace B S hS hs he hdesc
        hX Z.1 Z.2.1 Z.2.1 Z.2.2⟩) ⟨?_, ?_⟩,
    fun Z => preimage_invariantSubspace B S hS hs Z.1 Z.2.2⟩
  · intro Z₁ Z₂ h
    refine Subtype.ext (subschemePoints_injective B S hS Z₁.2.1 Z₂.2.1 ?_)
    rw [← preimage_invariantSubspace B S hS hs Z₁.1 Z₁.2.2,
      ← preimage_invariantSubspace B S hS hs Z₂.1 Z₂.2.2]
    exact congrArg (fun W => Subfunctor.preimage W.1 φ) h
  · intro W
    obtain ⟨Z, hZ, hWZ⟩ := exists_invariantSubspace_eq B S hS hs he hX W.1 W.2
    exact ⟨⟨Z, hZ⟩, Subtype.ext hWZ⟩

include hs he in
/-- **Stacks 07TW**, closedness: the subspace of `X` corresponding to an invariant subscheme
of the chart is closed exactly when that subscheme is closed in the chart. -/
theorem closed_iff
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@AlgebraicGeometry.IsImmersion.{u}))
    (hX : IsAlgebraicSpace B S hS X) (Z : InvariantLocallyClosedSubscheme B S hS hs) :
    IsClosedSubspace B S hS
        ((invariantLocallyClosedSubschemeEquiv B S hS hs he hdesc hX).1 Z).1 ↔
      AlgebraicGeometry.IsClosedImmersion Z.1.arrow := by
  exact isAlgebraicSpace_and_presheaf_iff B S hS hs he
    (fun _ _ _ hf => by have := hf; infer_instance) hdesc hX Z

include hs he in
/-- **Stacks 07TW**, openness: the subspace of `X` corresponding to an invariant subscheme of
the chart is open exactly when that subscheme is open in the chart. -/
theorem open_iff
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@AlgebraicGeometry.IsImmersion.{u}))
    (hX : IsAlgebraicSpace B S hS X) (Z : InvariantLocallyClosedSubscheme B S hS hs) :
    IsOpenSubspace B S hS
        ((invariantLocallyClosedSubschemeEquiv B S hS hs he hdesc hX).1 Z).1 ↔
      AlgebraicGeometry.IsOpenImmersion Z.1.arrow := by
  have hloc : MorphismProperty.IsLocalAtTarget (@AlgebraicGeometry.IsOpenImmersion.{u})
      Scheme.fpqcPrecoverage := Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _
  exact isAlgebraicSpace_and_presheaf_iff B S hS hs he
    (fun _ _ _ hf => by have := hf; infer_instance) hdesc hX Z

end Invariant

end AlgebraicGeometry.Space

end
