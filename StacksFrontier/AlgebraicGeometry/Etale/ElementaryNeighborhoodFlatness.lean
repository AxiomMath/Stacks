module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Etale.NeighborhoodStalkFiber
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraicFlatness
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.BaseChangeAt
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Existence
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.ShrinkingOverBase
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.SpecTranslation
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Reducing the elementary-étale-neighbourhood flatness statement to its module content

Stacks Tag 05I5 says: if `f : X ⟶ S` is locally of finite presentation and `F` is a finite type
quasi-coherent `𝒪_X`-module which is flat over `S` at `x`, then there is an elementary étale
neighbourhood `U` of `(S, f x)` and an open `V ⊆ X ×_S Spec 𝒪_{U, u}` containing *the unique
point* of `X ×_S Spec 𝒪_{U, u}` over `x` on which the pullback of `F` is of finite presentation
and flat over `Spec 𝒪_{U, u}`.

Its conclusion splits into two independent assertions about the produced open `V`: that `V`
contains a point lying over `x` and that this point is the only such point of the whole fibre
product, and that the pullback of `F` to `V` is finitely presented and flat. The second is the
substance of the source's induction; the first is automatic, by
`AlgebraicGeometry.EtaleNeighborhood.preimage_fst_eq_singleton_of_apply_eq`.

The first part of this file records that reduction, and names both statements as propositions so
that the consumers of Tag 05I5 may take it as a single hypothesis.

The second part proves Tag 05I5, by the source's *second* proof. Its last input, the dictionary
of Stacks 05I0 — `AlgebraicGeometry.geometricCompleteDevissageAtGivesAlgebraic` — is now a
theorem, so the proposition is proved outright. Stacks 05HR produces
elementary étale neighbourhoods `U` of `(X, x)` and `U' ⟶ S` of `(S, f x)` together with a
morphism `h : U ⟶ U'` over `f` such that the inverse image of `F` on `U` has a complete
dévissage at the distinguished point; Stacks 05HJ and Stacks 05HK base change that dévissage to
`Spec 𝒪_{U', u'}`; Stacks 05I0 and Stacks 05I4 turn it into finite presentation and flatness
there; and Stacks 05H2 descends the conclusion to an open subscheme of `X ×_S Spec 𝒪_{U', u'}`.

## Main definitions

* `AlgebraicGeometry.ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOver` is the
  statement of Tag 05I5 itself, named once as a proposition so that the consumers which need it
  — Tag 05I7 in `StacksFrontier/AlgebraicGeometry/Morphisms/Flat/StalkFinitePresentation.lean`,
  and through it Tags 05M9 and 05IK — can take it as a single hypothesis.
* `AlgebraicGeometry.ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOverOfMem` is the
  pointwise variant.

## Main results

* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_isFinitePresentation_isFlatOver_of_mem`
  upgrades the pointwise fibre condition to the uniqueness condition in the conclusion of Tag
  05I5.
* `AlgebraicGeometry.ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOver.of_mem` is that
  upgrade read on the two propositions.
* `AlgebraicGeometry.existsElementaryEtaleNeighborhoodFinitePresentationFlatOverOfMem` and
  `AlgebraicGeometry.existsElementaryEtaleNeighborhoodFinitePresentationFlatOver` prove the two
  propositions; the second is **Tag 05I5**, with the statement written out in its type.
* `AlgebraicGeometry.exists_open_isFinitePresentation_isFlatOver_of_etale` and
  `AlgebraicGeometry.exists_open_of_etale_stalk_pullback` are the two étale descent steps of
  that proof.

## Implementation notes

The upgrade theorem takes no hypothesis on `f` or `F` at all: it uses only that the
neighbourhood is elementary. In particular it is stated more generally than the hypotheses of Tag
05I5, which are needed exclusively for the finite-presentation and flatness clauses that the
hypothesis `h` carries.

The hypothesis and conclusion keep the `let`-bound `b : Spec 𝒪_{U, u} ⟶ S` of the source
statement, so that the two agree syntactically clause by clause outside the fibre condition.

## References

* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The conclusion of **Stacks Project, Tag 05I5** follows from the variant in which the open
subscheme `V` is only required to contain *some* point over `x`, rather than to contain the
unique one: for an elementary étale neighbourhood `U` of `(S, f x)` the fibre of
`X ×_S Spec 𝒪_{U, u} ⟶ X` over `x` is a singleton, so any point of `V` over `x` exhausts it.

This is the whole of Tag 05I5 except for the finite-presentation and flatness clauses, which the
hypothesis `h` carries unchanged. -/
theorem exists_elementaryEtaleNeighborhood_isFinitePresentation_isFlatOver_of_mem
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    (h : ∃ (U : EtaleNeighborhood S (f x)) (_ : U.IsElementary),
      let b : Spec (U.scheme.presheaf.stalk U.point) ⟶ S :=
        U.scheme.fromSpecStalk U.point ≫ U.toBase
      ∃ (V : (pullback f b).Opens) (v : V),
        (pullback.fst f b (V.ι v) = x) ∧
        ((Scheme.Modules.pullback (V.ι ≫ pullback.fst f b)).obj F).IsFinitePresentation ∧
        IsFlatOver
          (LocallyRingedSpace.forgetToSheafedSpace.map (V.ι ≫ pullback.snd f b).toLRSHom)
          ((Scheme.Modules.pullback (V.ι ≫ pullback.fst f b)).obj F)) :
    ∃ (U : EtaleNeighborhood S (f x)) (_ : U.IsElementary),
      let b : Spec (U.scheme.presheaf.stalk U.point) ⟶ S :=
        U.scheme.fromSpecStalk U.point ≫ U.toBase
      ∃ (V : (pullback f b).Opens) (v : V),
        (pullback.fst f b ⁻¹' {x} = {V.ι v}) ∧
        ((Scheme.Modules.pullback (V.ι ≫ pullback.fst f b)).obj F).IsFinitePresentation ∧
        IsFlatOver
          (LocallyRingedSpace.forgetToSheafedSpace.map (V.ι ≫ pullback.snd f b).toLRSHom)
          ((Scheme.Modules.pullback (V.ι ≫ pullback.fst f b)).obj F) := by
  obtain ⟨U, hU, V, v, hv, hfp, hflat⟩ := h
  exact ⟨U, hU, V, v,
    EtaleNeighborhood.preimage_fst_eq_singleton_of_apply_eq f x U hU hv, hfp, hflat⟩

/-- **Stacks Project, Tag 05I5**, as a proposition. For a morphism `f : X ⟶ S` locally of finite
presentation and a finite type quasi-coherent `𝒪_X`-module `F` which is flat over `S` at `x`,
there is an elementary étale neighbourhood `U` of `(S, f x)` and an open
`V ⊆ X ×_S Spec 𝒪_{U, u}` containing the unique point of `X ×_S Spec 𝒪_{U, u}` over `x` on which
the pullback of `F` is of finite presentation and flat over `Spec 𝒪_{U, u}`.

This is the statement named once, so that a consumer may take it as a hypothesis rather than
restate it.

`AlgebraicGeometry.existsElementaryEtaleNeighborhoodFinitePresentationFlatOver` proves this
proposition by the source's second proof, and carries the tag. Its last input was Stacks 05I0,
the dictionary taking a geometric `AlgebraicGeometry.CompleteDevissageAt` to a ring-theoretic
`Module.CompleteDevissageAt`; that is now
`AlgebraicGeometry.geometricCompleteDevissageAtGivesAlgebraic`. -/
def ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOver : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (F : X.Modules)
      [F.IsQuasicoherent] [F.IsFiniteType] (x : X),
    IsFlatOverAt f.toLRSHom.toShHom F x →
    ∃ (U : EtaleNeighborhood S (f x)) (_ : U.IsElementary),
      let b : Spec (U.scheme.presheaf.stalk U.point) ⟶ S :=
        U.scheme.fromSpecStalk U.point ≫ U.toBase
      ∃ (V : (pullback f b).Opens) (v : V),
        (pullback.fst f b ⁻¹' {x} = {V.ι v}) ∧
        ((Scheme.Modules.pullback (V.ι ≫ pullback.fst f b)).obj F).IsFinitePresentation ∧
        IsFlatOver
          (LocallyRingedSpace.forgetToSheafedSpace.map (V.ι ≫ pullback.snd f b).toLRSHom)
          ((Scheme.Modules.pullback (V.ι ≫ pullback.fst f b)).obj F)

/-- The variant of `AlgebraicGeometry.ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOver`
in which the produced open subscheme is only required to contain *some* point over `x`. This is
the weaker statement that
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_isFinitePresentation_isFlatOver_of_mem`
upgrades, and therefore the form in which Stacks 05I5 still has to be proved. -/
def ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOverOfMem : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (F : X.Modules)
      [F.IsQuasicoherent] [F.IsFiniteType] (x : X),
    IsFlatOverAt f.toLRSHom.toShHom F x →
    ∃ (U : EtaleNeighborhood S (f x)) (_ : U.IsElementary),
      let b : Spec (U.scheme.presheaf.stalk U.point) ⟶ S :=
        U.scheme.fromSpecStalk U.point ≫ U.toBase
      ∃ (V : (pullback f b).Opens) (v : V),
        (pullback.fst f b (V.ι v) = x) ∧
        ((Scheme.Modules.pullback (V.ι ≫ pullback.fst f b)).obj F).IsFinitePresentation ∧
        IsFlatOver
          (LocallyRingedSpace.forgetToSheafedSpace.map (V.ι ≫ pullback.snd f b).toLRSHom)
          ((Scheme.Modules.pullback (V.ι ≫ pullback.fst f b)).obj F)

/-- The pointwise form of Stacks 05I5 implies the full form, by
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_isFinitePresentation_isFlatOver_of_mem`
applied at every datum. -/
theorem ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOver.of_mem
    (h : ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOverOfMem.{u}) :
    ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOver.{u} := by
  intro X S f _ F _ _ x hflat
  exact exists_elementaryEtaleNeighborhood_isFinitePresentation_isFlatOver_of_mem f F x
    (h f F x hflat)

/-! ### The second proof of Tag 05I5 -/

/-- In a commutative square whose two horizontal arrows are étale, the morphism above a
morphism locally of finite presentation is itself locally of finite presentation: it factors
as an étale morphism into the base change, which is locally of finite presentation. -/
theorem locallyOfFinitePresentation_of_etaleSquare {X S U V : Scheme.{u}} (f : X ⟶ S)
    (u : U ⟶ X) (v : V ⟶ S) (h : U ⟶ V) [LocallyOfFinitePresentation f] [Etale u] [Etale v]
    (hsq : u ≫ f = h ≫ v) : LocallyOfFinitePresentation h := by
  have : Etale (pullback.lift u h hsq ≫ pullback.fst f v) := by
    rw [pullback.lift_fst]
    infer_instance
  have := Etale.of_comp (pullback.lift u h hsq) (pullback.fst f v)
  rw [← pullback.lift_snd u h hsq]
  infer_instance

/-- Finite presentation and flatness over the base transfer along an isomorphism of modules. -/
private theorem isFinitePresentation_isFlatOver_of_iso {Y S : Scheme.{u}} (g : Y ⟶ S)
    {M N : Y.Modules} (E : M ≅ N) (hfp : M.IsFinitePresentation)
    (hflat : IsFlatOver g.toLRSHom.toShHom M) :
    N.IsFinitePresentation ∧ IsFlatOver g.toLRSHom.toShHom N :=
  ⟨(SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso E hfp,
    isFlatOver_of_moduleIso _ E hflat⟩

/-- **Étale descent onto an open image.** If the inverse image of a quasi-coherent module along
an étale morphism `e : Y ⟶ X` is of finite presentation and flat over `S`, then so is the
restriction of the module to the open image of `e`, which contains the image of any point of
`Y`. The image is open because `e` is étale, and `e` factors through it by a surjective étale
morphism. -/
theorem exists_open_isFinitePresentation_isFlatOver_of_etale
    {Y X S : Scheme.{u}} (e : Y ⟶ X) [Etale e] (g : X ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent]
    (hfp : ((Scheme.Modules.pullback e).obj F).IsFinitePresentation)
    (hflat : IsFlatOver (e ≫ g).toLRSHom.toShHom ((Scheme.Modules.pullback e).obj F))
    (y : Y) :
    ∃ (O : X.Opens) (v : O), O.ι v = e y ∧
      ((Scheme.Modules.pullback O.ι).obj F).IsFinitePresentation ∧
      IsFlatOver (O.ι ≫ g).toLRSHom.toShHom ((Scheme.Modules.pullback O.ι).obj F) := by
  let O : X.Opens := ⟨Set.range e, e.isOpenMap.isOpen_range⟩
  let k : Y ⟶ O := IsOpenImmersion.lift O.ι e (by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨e a, ⟨a, rfl⟩⟩, rfl⟩)
  have hk : k ≫ O.ι = e := IsOpenImmersion.lift_fac _ _ _
  have : Etale (k ≫ O.ι) := hk.symm ▸ inferInstance
  have : Etale k := Etale.of_comp k O.ι
  have : Surjective k := by
    refine ⟨fun a ↦ ?_⟩
    obtain ⟨b, hb⟩ := a.property
    refine ⟨b, O.ι.injective ?_⟩
    show (k ≫ O.ι) b = a.val
    rw [hk, hb]
  let G := (Scheme.Modules.pullback O.ι).obj F
  have : G.IsQuasicoherent := Stacks.Modules.isQuasicoherent_pullback O.ι F inferInstance
  let E : (Scheme.Modules.pullback k).obj G ≅ (Scheme.Modules.pullback e).obj F :=
    (Scheme.Modules.pullbackComp k O.ι).app F ≪≫ eqToIso (by rw [hk])
  obtain ⟨hfp', hflat'⟩ := isFinitePresentation_isFlatOver_of_iso (e ≫ g) E.symm hfp hflat
  rw [← hk, Category.assoc] at hflat'
  obtain ⟨hfpO, hflatO⟩ :=
    isFinitePresentation_isFlatOver_of_surjective_etale_pullback k (O.ι ≫ g) G hfp' hflat'
  exact ⟨O, k y, congrArg (fun m : Y ⟶ X ↦ m y) hk, hfpO, hflatO⟩

/-- **Stacks 05H2 brings the conclusion back to `X ×_S Spec 𝒪_{V, v}`.** In the situation
produced by Stacks 05HR — étale neighbourhoods `U` of `(X, x)` and `V` of `(S, f x)` and a
morphism `h : U ⟶ V` over `f` — the comparison morphism
`U ×_V Spec 𝒪_{V, v} ⟶ X ×_S Spec 𝒪_{V, v}` is étale, so finite presentation and flatness over
`Spec 𝒪_{V, v}` of the inverse image of `F` on the left descend to an open subscheme of the
right containing a point over `x`. -/
theorem exists_open_of_etale_stalk_pullback
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent] (x : X)
    (U : EtaleNeighborhood X x) (V : EtaleNeighborhood S (f x)) (h : U.scheme ⟶ V.scheme)
    (hcomm : U.toBase ≫ f = h ≫ V.toBase)
    (z : (pullback h (V.scheme.fromSpecStalk V.point) : Scheme.{u}))
    (hz : pullback.fst h (V.scheme.fromSpecStalk V.point) z = U.point)
    (hfp : ((Scheme.Modules.pullback
      (pullback.fst h (V.scheme.fromSpecStalk V.point))).obj
        ((Scheme.Modules.pullback U.toBase).obj F)).IsFinitePresentation)
    (hflat : IsFlatOver
      (pullback.snd h (V.scheme.fromSpecStalk V.point)).toLRSHom.toShHom
      ((Scheme.Modules.pullback
        (pullback.fst h (V.scheme.fromSpecStalk V.point))).obj
          ((Scheme.Modules.pullback U.toBase).obj F))) :
    let b : Spec (V.scheme.presheaf.stalk V.point) ⟶ S :=
      V.scheme.fromSpecStalk V.point ≫ V.toBase
    ∃ (O : (pullback f b).Opens) (v : O),
      (pullback.fst f b (O.ι v) = x) ∧
      ((Scheme.Modules.pullback (O.ι ≫ pullback.fst f b)).obj F).IsFinitePresentation ∧
      IsFlatOver (O.ι ≫ pullback.snd f b).toLRSHom.toShHom
        ((Scheme.Modules.pullback (O.ι ≫ pullback.fst f b)).obj F) := by
  intro b
  let bV := V.scheme.fromSpecStalk V.point
  let e := stalkBaseChangeMap h U.toBase V.toBase f hcomm V.point
  have : Etale e := etale_stalkBaseChangeMap h U.toBase V.toBase f hcomm V.point
  have heX : e ≫ pullback.fst f b = pullback.fst h bV ≫ U.toBase := by
    simp only [e, b, bV, stalkBaseChangeMap, etaleBaseChangeMap, pullback.lift_fst]
  have heS : e ≫ pullback.snd f b = pullback.snd h bV := by
    simp only [e, b, bV, stalkBaseChangeMap, etaleBaseChangeMap, pullback.lift_snd,
      Category.comp_id]
  let G := (Scheme.Modules.pullback (pullback.fst f b)).obj F
  have : G.IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback (pullback.fst f b) F inferInstance
  let E : (Scheme.Modules.pullback e).obj G ≅
      (Scheme.Modules.pullback (pullback.fst h bV)).obj
        ((Scheme.Modules.pullback U.toBase).obj F) :=
    (Scheme.Modules.pullbackComp e (pullback.fst f b)).app F ≪≫ eqToIso (by rw [heX]) ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst h bV) U.toBase).app F).symm
  obtain ⟨hfp', hflat'⟩ :=
    isFinitePresentation_isFlatOver_of_iso (pullback.snd h bV) E.symm hfp hflat
  rw [← heS] at hflat'
  obtain ⟨O, v, hv, hfpO, hflatO⟩ :=
    exists_open_isFinitePresentation_isFlatOver_of_etale e (pullback.snd f b) G hfp' hflat' z
  let E' := (Scheme.Modules.pullbackComp O.ι (pullback.fst f b)).app F
  refine ⟨O, v, ?_, isFinitePresentation_isFlatOver_of_iso (O.ι ≫ pullback.snd f b) E' hfpO
    hflatO⟩
  · rw [hv]
    show (e ≫ pullback.fst f b) z = x
    rw [heX]
    show U.toBase (pullback.fst h bV z) = x
    rw [hz, U.map_point]

/-- **Stacks Project, Tag 05I5**, the pointwise form. The dictionary of Stacks 05I0 enters as
`AlgebraicGeometry.geometricCompleteDevissageAtGivesAlgebraic`.

This is the source's *second* proof. Stacks 05HR provides elementary étale neighbourhoods `U`
of `(X, x)` and `V` of `(S, f x)` and a morphism `h : U ⟶ V` over `f` such that the inverse
image of `F` on `U` has a complete dévissage at the distinguished point. Stacks 02JZ and
Stacks 05B9 move the flatness hypothesis to that inverse image along `h`, Stacks 05HJ and
Stacks 05HK base change the dévissage to `Spec 𝒪_{V, v}`, and
`AlgebraicGeometry.isFinitePresentation_isFlatOver_of_completeDevissageAt` — which is Stacks
05I0 followed by Stacks 05I4 — concludes that the inverse image of `F` on
`U ×_V Spec 𝒪_{V, v}` is of finite presentation and flat over `Spec 𝒪_{V, v}`. Stacks 05H2
descends that to an open subscheme of `X ×_S Spec 𝒪_{V, v}`. -/
theorem existsElementaryEtaleNeighborhoodFinitePresentationFlatOverOfMem :
    ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOverOfMem.{u} := by
  intro X S f hfpf F hqF htF x hflat
  obtain ⟨U, V, h, hUE, hVE, hcomm, hpoint, hl, hqU, htU, hCD⟩ :=
    hasEtaleNeighborhoodCompleteDevissageAt f F x
  have hlfph : LocallyOfFinitePresentation h :=
    locallyOfFinitePresentation_of_etaleSquare f U.toBase V.toBase h hcomm
  set F' := (Scheme.Modules.pullback U.toBase).obj F
  -- Move the flatness hypothesis to `F'` along `h`.
  have hflatU : IsFlatOverAt (U.toBase ≫ f).toLRSHom.toShHom F' U.point :=
    (isFlatOverAt_iff_modulePullback_isFlatOverAt U.toBase f F U.point
      (Flat.stalkMap U.toBase U.point)).mp (by rwa [U.map_point])
  rw [hcomm] at hflatU
  have hflatD : IsFlatOverAt h.toLRSHom.toShHom F' U.point :=
    (isFlatOverAt_comp_iff_of_etale h V.toBase F' U.point).mp hflatU
  -- The local ring of `V` at its distinguished point.
  let bV := V.scheme.fromSpecStalk V.point
  let sLocal : (Spec (V.scheme.presheaf.stalk V.point) : Scheme.{u}) :=
    IsLocalRing.closedPoint (V.scheme.presheaf.stalk V.point)
  have hzbase : bV sLocal = h U.point :=
    Scheme.fromSpecStalk_closedPoint.trans hpoint.symm
  obtain ⟨z, hzfst, hzsnd⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := h) (g := bV) U.point sLocal hzbase.symm
  refine ⟨V, hVE, ?_⟩
  -- The pullback of `F'` to `U ×_V Spec 𝒪_{V, v}` and its two finiteness conditions.
  set G := (Scheme.Modules.pullback (pullback.fst h bV)).obj F'
  have hqG : G.IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback (pullback.fst h bV) F' inferInstance
  have htG : G.IsFiniteType :=
    SheafOfModules.pullback_isFiniteType (pullback.fst h bV).toLRSHom.toShHom F'
  have hXpb : IsPullback (pullback.fst h bV) (pullback.snd h bV) h bV :=
    IsPullback.of_hasPullback h bV
  have hl₂ : LocallyOfFiniteType (pullback.snd h bV) :=
    MorphismProperty.of_isPullback hXpb (P := @LocallyOfFiniteType) inferInstance
  have hlfp₂ : LocallyOfFinitePresentation (pullback.snd h bV) :=
    MorphismProperty.of_isPullback hXpb (P := @LocallyOfFinitePresentation) inferInstance
  have hflatG : IsFlatOverAt (pullback.snd h bV).toLRSHom.toShHom G z :=
    @modulePullback_isFlatOverAt _ _ _ _ _ _ _ _ hXpb F' hqU z (by rwa [hzfst])
  -- Both finiteness conditions for `G`, from the complete dévissage.
  have key : G.IsFinitePresentation ∧ IsFlatOver (pullback.snd h bV).toLRSHom.toShHom G := by
    obtain ⟨D⟩ := hCD
    cases D with
    | empty hzero =>
      have hGzero : IsZero G := (Scheme.Modules.pullback (pullback.fst h bV)).map_isZero hzero
      exact ⟨isFinitePresentation_of_isZero G hGzero,
        isFlatOver_of_isZero (pullback.snd h bV) G hGzero⟩
    | nonempty D =>
      have hVaff : IsAffine V.scheme :=
        isAffine_of_devissageChain D.toNonemptyCompleteDevissage.chain
      have hsbase : bV (pullback.snd h bV z) = h U.point := by rwa [hzsnd]
      have hsres : IsIso (bV.residueFieldMap (pullback.snd h bV z)) := by
        rw [Scheme.Hom.isIso_residueFieldMap_congr bV hzsnd]
        exact bV.isIso_residueFieldMap_of_surjectiveOnStalks sLocal
      obtain ⟨D', hbc⟩ := exists_completeDevissage_baseChange
        (s' := pullback.snd h bV z) hsbase D.toNonemptyCompleteDevissage
        (pullback.fst h bV) hXpb (Iso.refl _)
      obtain ⟨DAt', -, -⟩ := exists_completeDevissageAt_baseChange (x' := z) hsbase hsres D
        (pullback.fst h bV) hXpb (Iso.refl _) hzfst D' hbc
      have hpbaff : IsAffine (pullback h bV) :=
        isAffine_source_of_devissageChain DAt'.toNonemptyCompleteDevissage.chain
      have hlocal : IsLocalRing (V.scheme.presheaf.stalk V.point : Type u) :=
        V.scheme.toLocallyRingedSpace.isLocalRing V.point
      exact @isFinitePresentation_isFlatOver_of_completeDevissageAt
        geometricCompleteDevissageAtGivesAlgebraic
        (V.scheme.presheaf.stalk V.point : Type u) _ hlocal _ hpbaff (pullback.snd h bV)
        hlfp₂ G hqG htG z hzsnd ⟨.nonempty DAt'⟩ hflatG
  exact exists_open_of_etale_stalk_pullback f F x U V h hcomm z hzfst key.1 key.2

/-- **Stacks Project, Tag 05I5.** For `f` locally of finite presentation and `F` quasi-coherent of
finite type and flat over `S` at `x`, there is an elementary étale neighbourhood `(S', s')` of
`(S, f x)` and an open subscheme of `X ×_S Spec 𝒪_{S', s'}` containing the unique point over `x`
on which the pullback of `F` is of finite presentation and flat over `𝒪_{S', s'}`.

Here `U` is the elementary étale neighbourhood `(S', s')`, the base change is along the composite
`Spec 𝒪_{S', s'} ⟶ S' ⟶ S`, `V` is the open subscheme and `v` the point of `V` over `x`; the
first clause says that `v` is the only point of `X ×_S Spec 𝒪_{S', s'}` over `x`. Its type is
the body of `AlgebraicGeometry.ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOver`,
written out.

The pointwise form above composed with
`AlgebraicGeometry.ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOver.of_mem`, which
supplies the uniqueness of the point over `x`. -/
@[stacks 05I5]
theorem existsElementaryEtaleNeighborhoodFinitePresentationFlatOver
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F x) :
    ∃ (U : EtaleNeighborhood S (f x)) (_ : U.IsElementary)
      (V : (pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)).Opens) (v : V),
      (pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) ⁻¹' {x} = {V.ι v}) ∧
      ((Scheme.Modules.pullback
        (V.ι ≫ pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase))).obj
          F).IsFinitePresentation ∧
      IsFlatOver
        (LocallyRingedSpace.forgetToSheafedSpace.map
          (V.ι ≫ pullback.snd f (U.scheme.fromSpecStalk U.point ≫ U.toBase)).toLRSHom)
        ((Scheme.Modules.pullback
          (V.ι ≫ pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase))).obj F) :=
  ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOver.of_mem
    existsElementaryEtaleNeighborhoodFinitePresentationFlatOverOfMem f F x hflat

end AlgebraicGeometry

end
