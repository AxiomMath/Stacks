module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsZariskiSheaf

/-!
# McQuillan's variant of the category of formal schemes

A *weakly admissible* topological ring is a complete, separated, linearly topologized ring
possessing a weak ideal of definition: an open ideal `I` such that `fⁿ → 0` for every `f ∈ I`.
McQuillan's formal spectrum of such a ring is the space of its open primes carrying the limit,
over the *weak* ideals of definition `I_λ`, of the pseudo-discretised structure sheaves of the
`Spec (A/I_λ)`; an object of `LTRS` is a formal scheme in the sense of McQuillan when every
point has an open neighbourhood isomorphic to such a formal spectrum. This is the larger
category of formal schemes of Stacks 0AI3.

The weak ideals of definition of a weakly admissible ring have exactly the two properties that
the arguments about a formal spectrum consume — each is an open ideal of topologically nilpotent
elements, and they are closed under intersection — so they are a
`AlgebraicGeometry.IsWeakIdealSystem`, and the source's counterparts of Lemmas 87.2.1 and 87.2.2
hold in this setting with the same proof: the proofs below instantiate the arguments already
carried out for an arbitrary weak ideal system and for an arbitrary locally topologically ringed
space.

## Main definitions

* `AlgebraicGeometry.Spfw`: McQuillan's formal spectrum of a weakly admissible topological ring.
* `AlgebraicGeometry.IsMcQuillanFormalScheme` and
  `AlgebraicGeometry.McQuillanFormalScheme`: the objects of `LTRS` locally isomorphic to such a
  formal spectrum, and the category they form.
* `AlgebraicGeometry.schemeToMcQuillanFormalScheme`: a scheme as a McQuillan formal scheme.
* `AlgebraicGeometry.mcQuillanFormalSchemeFunctorOfPoints` and
  `AlgebraicGeometry.mcQuillanFormalSchemePoints`: the functor of points of a McQuillan formal
  scheme, on the schemes of size below a cutoff and on all schemes.
* `AlgebraicGeometry.IsSizeBoundedMcQuillanFormalScheme`: the size condition of Lemma 87.2.1 in
  this setting.

## Main results

* `AlgebraicGeometry.injective_mcQuillanFormalSchemeFunctorOfPoints_map`: the counterpart of
  Lemma 87.2.1. A morphism of McQuillan formal schemes whose source satisfies the size condition
  is determined by the natural transformation it induces on functors of points.
* `AlgebraicGeometry.injective_mcQuillanFormalSchemePointsFunctor_map`: the same with no size
  hypothesis, the size condition being satisfiable for some cutoff.
* `AlgebraicGeometry.isSeparated_fpqcTopology_mcQuillanFormalSchemePoints` and
  `AlgebraicGeometry.isSeparatedFor_mcQuillanFormalSchemeFunctorOfPoints`: the counterpart of
  Lemma 87.2.2. A point of a McQuillan formal scheme over a scheme `T` is determined by its
  restrictions along an fpqc covering of `T`.
* `AlgebraicGeometry.existsUnique_mcQuillanHom_of_openCover_scheme` and
  `AlgebraicGeometry.isSheaf_zariskiTopology_mcQuillanFormalSchemePoints`: the counterpart of
  Lemma 87.2.2 for a Zariski covering. A matching family of points of a McQuillan formal scheme
  on the members of a Zariski covering of a scheme has a unique amalgamation.

## Implementation notes

`AlgebraicGeometry.Spfw` is `AlgebraicGeometry.SpfOn` taken along the weak ideals of definition,
exactly as `AlgebraicGeometry.Spf` is that construction taken along the ideals of definition, so
the two formal spectra are the two instances of one construction and every lemma about it
applies to both.

The chart condition `AlgebraicGeometry.IsSizeBoundedMcQuillanFormalScheme` feeds into
`AlgebraicGeometry.IsSizeBoundedFormalSpectrumCharted`, the shape of chart data on which the
separation argument of Lemma 87.2.1 rests; that argument is
`AlgebraicGeometry.ltrs_hom_ext_of_isSizeBoundedFormalSpectrumCharted`. Likewise the fpqc
statement rests on `AlgebraicGeometry.ltrs_hom_ext_of_mem_fpqcTopology`, which asks nothing of
its target beyond being an object of `LTRS`.

## References

* [Stacks Project, Tag 0AI3](https://stacks.math.columbia.edu/tag/0AI3)
* [Stacks Project, Tag 0AI1](https://stacks.math.columbia.edu/tag/0AI1)
* [Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open TopologicalRing

/-! ### McQuillan's formal spectrum -/

/-- McQuillan's formal spectrum of a topological ring `A`: the space of open primes of `A`
carrying the limit, over the *weak* ideals of definition of `A`, of the pseudo-discretised
structure sheaves of the `Spec (A/I_λ)`.

For a weakly admissible `A` the weak ideals of definition are a fundamental system of open
neighbourhoods of zero, which is what makes this the right analogue of `AlgebraicGeometry.Spf`;
the construction itself is `AlgebraicGeometry.SpfOn` taken along that family. -/
@[reducible] noncomputable def Spfw (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : PresheafedSpace TopCommRingCat.{u} :=
  SpfOn A IsWeakIdealOfDefinition

/-- A discrete topological ring is weakly admissible: the zero ideal is a weak ideal of
definition, and the discrete uniformity is complete and Hausdorff. -/
theorem isWeaklyAdmissible_discrete (R : Type u) [CommRing R] [TopologicalSpace R]
    [DiscreteTopology R] [IsTopologicalRing R] [IsLinearTopology R R] :
    IsWeaklyAdmissible R :=
  ⟨isWeaklyPreAdmissible_of_isPreAdmissible (isAdmissible_discrete R).1,
    (isAdmissible_discrete R).2.2, (isAdmissible_discrete R).2.1⟩

/-! ### McQuillan's formal schemes -/

/-- An object of `LTRS` is a *formal scheme in the sense of McQuillan* when every point has an
open neighbourhood isomorphic to the formal spectrum, taken along the weak ideals of definition,
of a weakly admissible topological ring. As for `AlgebraicGeometry.IsFormalScheme`, the
isomorphism is asked for as one of presheafed spaces of topological rings, which for objects of
`LTRS` is the same as an isomorphism in `LTRS`. -/
@[stacks 0AI3 "the larger category of formal schemes based on weak admissibility: its objects"]
def IsMcQuillanFormalScheme : ObjectProperty LTRS.{u} := fun X =>
  ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (A : TopCommRingCat.{u}),
    ∃ (hlinear : IsLinearTopology A.α A.α),
    letI := hlinear
    TopologicalRing.IsWeaklyAdmissible A.α ∧
      Nonempty (X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ Spfw A.α)

/-- The category of *McQuillan formal schemes*: the full subcategory of `LTRS` on the objects
locally isomorphic to a formal spectrum taken along the weak ideals of definition of a weakly
admissible topological ring. A morphism is a morphism of `LTRS`. -/
@[stacks 0AI3 "the larger category of formal schemes based on weak admissibility: the category"]
abbrev McQuillanFormalScheme := IsMcQuillanFormalScheme.FullSubcategory

/-- A scheme, pseudo-discretised, is a formal scheme in the sense of McQuillan. Every point lies
in an affine open `Spec R`; the discrete topological ring `R` is weakly admissible, and `0` is
an initial object of its ordered family of weak ideals of definition, so the limit defining the
structure sheaf of the formal spectrum is canonically its component at `0`. -/
theorem isMcQuillanFormalScheme_schemeToLTRSObj (X : Scheme.{u}) :
    IsMcQuillanFormalScheme (schemeToLTRSObj X) := by
  intro point
  obtain ⟨U, R, ⟨affineIso⟩⟩ := X.local_affine point
  let _ : TopologicalSpace R := ⊥
  let _ : DiscreteTopology R := discreteTopology_bot R
  refine ⟨U.1, U.2, TopCommRingCat.of R, inferInstance, isWeaklyAdmissible_discrete R, ?_⟩
  refine ⟨?_ ≪≫ pseudoDiscreteSpaceIso ((LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace).mapIso affineIso)
    ≪≫ discreteSpecSpfIsoOn R (isWeakIdealOfDefinition_bot_discrete R)⟩
  exact PresheafedSpace.isoOfComponents (Iso.refl _)
    (pseudoDiscreteWhiskerIso U.1.inclusion' U.1.isOpenEmbedding' X.presheaf).symm

/-- The functor `Schemes ⟶ McQuillan Formal Schemes`: pseudo-discretisation, a scheme being a
McQuillan formal scheme by `AlgebraicGeometry.isMcQuillanFormalScheme_schemeToLTRSObj`. -/
noncomputable def schemeToMcQuillanFormalScheme : Scheme.{u} ⥤ McQuillanFormalScheme.{u} :=
  IsMcQuillanFormalScheme.lift schemeToLTRS isMcQuillanFormalScheme_schemeToLTRSObj

/-! ### The functor of points -/

/-- The *functor of points* of a McQuillan formal scheme on the schemes of size below `κ`: the
presheaf `h_𝔛(S) = Mor(S, 𝔛)` on `Sch_κ`, a scheme being viewed as a McQuillan formal scheme
through its pseudo-discretisation. -/
noncomputable def mcQuillanFormalSchemeFunctorOfPoints (κ : Cardinal.{u}) :
    McQuillanFormalScheme.{u} ⥤ ((schemeCutoff κ).FullSubcategory)ᵒᵖ ⥤ Type u :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
    (((schemeCutoff κ).ι ⋙ schemeToMcQuillanFormalScheme).op)

/-- The points of `𝔛` on a scheme `S` of `Sch_κ` are the morphisms from `S` to `𝔛`. -/
@[simp]
theorem mcQuillanFormalSchemeFunctorOfPoints_obj_obj (κ : Cardinal.{u})
    (X : McQuillanFormalScheme.{u}) (S : (schemeCutoff κ).FullSubcategory) :
    ((mcQuillanFormalSchemeFunctorOfPoints κ).obj X).obj (op S) =
      (schemeToMcQuillanFormalScheme.obj S.obj ⟶ X) := rfl

/-- A morphism of McQuillan formal schemes acts on points by postcomposition. -/
@[simp]
theorem mcQuillanFormalSchemeFunctorOfPoints_map_app (κ : Cardinal.{u})
    {X Y : McQuillanFormalScheme.{u}} (f : X ⟶ Y) (S : (schemeCutoff κ).FullSubcategory)
    (g : schemeToMcQuillanFormalScheme.obj S.obj ⟶ X) :
    ((mcQuillanFormalSchemeFunctorOfPoints κ).map f).app (op S) g = g ≫ f := rfl

/-- The functor of points of a McQuillan formal scheme on the category of all schemes. -/
noncomputable def mcQuillanFormalSchemePoints (X : McQuillanFormalScheme.{u}) :
    (Scheme.{u})ᵒᵖ ⥤ Type u :=
  schemeToMcQuillanFormalScheme.op ⋙ yoneda.obj X

/-- The functor of points on all schemes, as a functor of the McQuillan formal scheme. -/
noncomputable def mcQuillanFormalSchemePointsFunctor :
    McQuillanFormalScheme.{u} ⥤ (Scheme.{u})ᵒᵖ ⥤ Type u :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj schemeToMcQuillanFormalScheme.op

/-- The value of that functor is the functor of points. -/
@[simp]
theorem mcQuillanFormalSchemePointsFunctor_obj (X : McQuillanFormalScheme.{u}) :
    mcQuillanFormalSchemePointsFunctor.obj X = mcQuillanFormalSchemePoints X := rfl

/-- The points of `𝔛` on a scheme `T` are the morphisms from `T` to `𝔛`. -/
@[simp]
theorem mcQuillanFormalSchemePoints_obj (X : McQuillanFormalScheme.{u}) (T : Scheme.{u}) :
    (mcQuillanFormalSchemePoints X).obj (op T) =
      (schemeToMcQuillanFormalScheme.obj T ⟶ X) := rfl

/-! ### The size condition -/

/-- The size condition of Lemma 87.2.1 on a McQuillan formal scheme `𝔛`: every point has a
neighbourhood `𝔛|_𝔘` isomorphic to the formal spectrum of a weakly admissible `A` taken along
its weak ideals of definition, in such a way that every quotient `Spec (A/I)` by a weak ideal of
definition of `A` is an object of `Sch_κ`. -/
def IsSizeBoundedMcQuillanFormalScheme (κ : Cardinal.{u}) (X : LTRS.{u}) : Prop :=
  ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (A : TopCommRingCat.{u}),
    ∃ hlinear : IsLinearTopology A.α A.α,
      letI := hlinear
      TopologicalRing.IsWeaklyAdmissible A.α ∧
      (∀ I : WeakIdealsOfDefinition A.α, (Spec (spfQuotientOn A.α I)).size < κ) ∧
      Nonempty (X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ Spfw A.α)

/-- A McQuillan formal scheme bounded by the cutoff is a McQuillan formal scheme. -/
theorem IsSizeBoundedMcQuillanFormalScheme.isMcQuillanFormalScheme {κ : Cardinal.{u}}
    {X : LTRS.{u}} (hX : IsSizeBoundedMcQuillanFormalScheme κ X) :
    IsMcQuillanFormalScheme X := fun x => by
  obtain ⟨U, hxU, A, hlin, hwadm, _, he⟩ := hX x
  exact ⟨U, hxU, A, hlin, hwadm, he⟩

/-- A McQuillan formal scheme bounded by the cutoff is charted by formal spectra: the weak
ideals of definition of a weakly admissible topological ring form a weak ideal system with at
least one member. -/
theorem IsSizeBoundedMcQuillanFormalScheme.isSizeBoundedFormalSpectrumCharted {κ : Cardinal.{u}}
    {X : LTRS.{u}} (hX : IsSizeBoundedMcQuillanFormalScheme κ X) :
    IsSizeBoundedFormalSpectrumCharted κ X := fun x => by
  obtain ⟨U, hxU, A, _, hwadm, hsize, he⟩ := hX x
  exact ⟨U, hxU, ⟨A, IsWeakIdealOfDefinition, inferInstance⟩,
    ⟨⟨hwadm.1.choose, hwadm.1.choose_spec⟩⟩, hsize, he⟩

/-- Every McQuillan formal scheme satisfies the size condition for some cutoff cardinal: a
cardinal above the sizes of all the schemes cut out of one chart around each point will do. -/
theorem exists_isSizeBoundedMcQuillanFormalScheme {X : LTRS.{u}}
    (hX : IsMcQuillanFormalScheme X) :
    ∃ κ : Cardinal.{u}, IsSizeBoundedMcQuillanFormalScheme κ X := by
  choose U hmem A hlin hwadm hiso using hX
  classical
  refine ⟨Order.succ (⨆ p : Σ x : X, WeakIdealsOfDefinition (A x).α,
    (Spec (spfQuotientOn (A p.1).α p.2)).size), fun x => ?_⟩
  refine ⟨U x, hmem x, A x, hlin x, hwadm x, fun I => ?_, hiso x⟩
  exact lt_of_le_of_lt (le_ciSup_of_le (f := fun p : Σ x : X, WeakIdealsOfDefinition (A x).α =>
      (Spec (spfQuotientOn (A p.1).α p.2)).size) Cardinal.bddAbove_of_small ⟨x, I⟩ le_rfl)
    (Order.lt_succ _)

/-! ### The counterpart of Lemma 87.2.1 -/

/-- **Stacks 0AI3**, the counterpart of Lemma 87.2.1 in McQuillan's setting. A morphism of
McQuillan formal schemes whose source satisfies the size condition is determined by the natural
transformation it induces on functors of points on the schemes of size below `κ`.

The proof is the source's: the morphisms `Spec (A/I_λ) → 𝔛|_𝔘 → 𝔛` attached to the charts of
`𝔛` are jointly epimorphic, and the size condition makes them points of `𝔛` seen by the functor
of points. Their underlying maps cover `𝔛` because each `Spec (A/I_λ)` is carried
homeomorphically onto the space of open primes of `A`, a prime being open exactly when it
contains the weak ideal of definition `I_λ`; and they separate the sections of `𝒪_𝔛` because
`𝒪_𝔛` is a sheaf and the sections of the structure presheaf of the chart are the limit over the
weak ideals of definition. -/
@[stacks 0AI3 "the counterpart of Lemma 87.2.1: a morphism of McQuillan formal \
schemes is determined by the induced transformation of functors of points"]
theorem injective_mcQuillanFormalSchemeFunctorOfPoints_map {κ : Cardinal.{u}}
    {X Y : McQuillanFormalScheme.{u}} (hX : IsSizeBoundedMcQuillanFormalScheme κ X.obj) :
    Function.Injective fun f : X ⟶ Y => (mcQuillanFormalSchemeFunctorOfPoints κ).map f := by
  intro f g hfg
  refine InducedCategory.hom_ext
    (ltrs_hom_ext_of_isSizeBoundedFormalSpectrumCharted
      hX.isSizeBoundedFormalSpectrumCharted fun T hT φ => ?_)
  exact congrArg (·.hom)
    (congrFun (congrArg (fun η => η.app (op ⟨T, hT⟩)) hfg) (ObjectProperty.homMk φ))

/-- **Stacks 0AI3**, the counterpart of Lemma 87.2.1 in McQuillan's setting, with no size
hypothesis: a morphism of McQuillan formal schemes is determined by the transformation it
induces on functors of points on all schemes. Every McQuillan formal scheme satisfies the size
condition for some cutoff, and the functor of points on `Sch_κ` is the restriction of the
functor of points on all schemes. -/
@[stacks 0AI3 "the counterpart of Lemma 87.2.1: injectivity of the functor of points \
on morphisms of McQuillan formal schemes, with no size hypothesis"]
theorem injective_mcQuillanFormalSchemePointsFunctor_map {X Y : McQuillanFormalScheme.{u}} :
    Function.Injective fun f : X ⟶ Y => mcQuillanFormalSchemePointsFunctor.map f := by
  intro f g hfg
  obtain ⟨κ, hκ⟩ := exists_isSizeBoundedMcQuillanFormalScheme X.property
  refine injective_mcQuillanFormalSchemeFunctorOfPoints_map (κ := κ) hκ
    (NatTrans.ext (funext fun S => ?_))
  exact congrArg (fun η : mcQuillanFormalSchemePoints X ⟶ mcQuillanFormalSchemePoints Y =>
    η.app (op S.unop.obj)) hfg

/-! ### The counterpart of Lemma 87.2.2 -/

/-- **Stacks 0AI3**, the counterpart of Lemma 87.2.2 in McQuillan's setting. The functor of
points of a McQuillan formal scheme, on the category of all schemes, is separated for the fpqc
topology: a point of `𝔛` over a scheme `T` is determined by its restrictions along any fpqc
covering sieve of `T`.

The proof is the source's: an fpqc covering sieve contains an fpqc covering family, whose
members are flat and jointly surjective, and a morphism from a scheme to a locally topologically
ringed space is determined by its restrictions along such a family. -/
@[stacks 0AI3 "the counterpart of Lemma 87.2.2: the functor of points of a McQuillan \
formal scheme on all schemes is separated for the fpqc topology"]
theorem isSeparated_fpqcTopology_mcQuillanFormalSchemePoints (X : McQuillanFormalScheme.{u}) :
    Presieve.IsSeparated Scheme.fpqcTopology.{u} (mcQuillanFormalSchemePoints X) := by
  intro T S hS x t₁ t₂ h₁ h₂
  refine InducedCategory.hom_ext (ltrs_hom_ext_of_mem_fpqcTopology hS fun Z π hπ => ?_)
  exact congrArg (·.hom)
    ((h₁ π hπ).trans (h₂ π hπ).symm)

/-- **Stacks 0AI3**, the counterpart of Lemma 87.2.2 in McQuillan's setting, for the functor of
points on the schemes of size below `κ`: a point of `𝔛` over a scheme `T` of `Sch_κ` is
determined by its restrictions along a family of morphisms of `Sch_κ` which is an fpqc covering
of `T`. -/
@[stacks 0AI3 "the counterpart of Lemma 87.2.2: the functor of points of a McQuillan \
formal scheme on the schemes of size below the cutoff is separated for the fpqc topology"]
theorem isSeparatedFor_mcQuillanFormalSchemeFunctorOfPoints {κ : Cardinal.{u}}
    (X : McQuillanFormalScheme.{u}) {T : (schemeCutoff κ).FullSubcategory} {R : Presieve T}
    (hR : R ∈ Scheme.fpqcPrecoverage.{u}.comap (schemeCutoff κ).ι T) :
    Presieve.IsSeparatedFor ((mcQuillanFormalSchemeFunctorOfPoints κ).obj X) R := by
  obtain ⟨J, S, u, rfl⟩ := R.exists_eq_ofArrows
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hR
  simp only [ObjectProperty.ι_obj, ObjectProperty.ι_map] at hR
  have hdata := (Scheme.presieve₀_mem_precoverage_iff (P := @Flat)
      (⟨J, fun j => (S j).obj, fun j => (u j).hom⟩ : PreZeroHypercover T.obj)).mp
    (Scheme.propQCPrecoverage_le_precoverage (P := @Flat) T.obj hR)
  intro y t₁ t₂ h₁ h₂
  refine InducedCategory.hom_ext
    (ltrs_hom_ext_of_flat_of_jointlySurjective (fun j => (u j).hom) (fun j => hdata.2 j)
      (fun t => hdata.1 t) fun j => ?_)
  exact congrArg (·.hom)
    ((h₁ _ (Presieve.ofArrows.mk j)).trans (h₂ _ (Presieve.ofArrows.mk j)).symm)

/-! ### The counterpart of Lemma 87.2.2 for a Zariski covering -/

/-- **The gluing clause for a Zariski open covering**, for a McQuillan formal scheme: the
morphisms of McQuillan formal schemes out of a scheme are the morphisms of `LTRS` out of its
pseudo-discretisation, and the gluing is
`AlgebraicGeometry.existsUnique_ltrsHom_of_openCover_scheme`. -/
theorem existsUnique_mcQuillanHom_of_openCover_scheme {T : Scheme.{u}}
    {X : McQuillanFormalScheme.{u}} {ι : Type*} (V : ι → T.Opens) (hV : iSup V = ⊤)
    (g : ∀ i, schemeToMcQuillanFormalScheme.obj (V i).toScheme ⟶ X)
    (hg : ∀ i j,
      schemeToMcQuillanFormalScheme.map (T.homOfLE (inf_le_left : V i ⊓ V j ≤ V i)) ≫ g i
        = schemeToMcQuillanFormalScheme.map
            (T.homOfLE (inf_le_right : V i ⊓ V j ≤ V j)) ≫ g j) :
    ∃! f : schemeToMcQuillanFormalScheme.obj T ⟶ X,
      ∀ i, schemeToMcQuillanFormalScheme.map (V i).ι ≫ f = g i := by
  obtain ⟨f₀, hf₀, huniq⟩ := existsUnique_ltrsHom_of_openCover_scheme V hV (fun i => (g i).hom)
    fun i j => congrArg (·.hom) (hg i j)
  refine ⟨ObjectProperty.homMk f₀, fun i => InducedCategory.hom_ext (hf₀ i),
    fun f' hf' => InducedCategory.hom_ext (huniq f'.hom fun i =>
      congrArg (·.hom) (hf' i))⟩

/-- The functor of points of a McQuillan formal scheme satisfies the sheaf condition for the
presieve generated by a covering of a scheme by open subschemes: matching for this presieve is
compatibility on every common refinement, and the pairwise overlap `V i ⊓ V j` is the fibre
product `V i ×_T V j`. -/
theorem isSheafFor_opensCover_mcQuillanFormalSchemePoints {T : Scheme.{u}}
    (X : McQuillanFormalScheme.{u}) {ι : Type*} (V : ι → T.Opens) (hV : iSup V = ⊤) :
    Presieve.IsSheafFor (mcQuillanFormalSchemePoints X)
      (Presieve.ofArrows (fun i => (V i).toScheme) (fun i => (V i).ι)) :=
  (Presieve.isSheafFor_arrows_iff _ _).mpr fun x hx =>
    existsUnique_mcQuillanHom_of_openCover_scheme V hV x fun i j =>
      hx i j (V i ⊓ V j).toScheme (T.homOfLE inf_le_left) (T.homOfLE inf_le_right)
        (isPullback_opens_inf (V i) (V j)).w

/-- The functor of points of a McQuillan formal scheme satisfies the sheaf condition for a
jointly surjective family of arbitrary open immersions into a scheme: such a family generates
the same sieve as the family of open subschemes cut out by its ranges. -/
theorem isSheafFor_ofArrows_mcQuillanFormalSchemePoints {T : Scheme.{u}}
    (X : McQuillanFormalScheme.{u}) {ι : Type*} (U : ι → Scheme.{u}) (π : ∀ i, U i ⟶ T)
    [∀ i, IsOpenImmersion (π i)] (hsurj : ∀ x : T, ∃ i, x ∈ Set.range ⇑(π i)) :
    Presieve.IsSheafFor (mcQuillanFormalSchemePoints X) (Presieve.ofArrows U π) := by
  have hV : (iSup fun i => ((π i).opensRange)) = ⊤ :=
    iSup_eq_top_of_forall_exists_mem _ fun x => hsurj x
  rw [Presieve.isSheafFor_iff_generate,
    generate_ofArrows_eq_generate_ofArrows_opensRange U π,
    ← Presieve.isSheafFor_iff_generate]
  exact isSheafFor_opensCover_mcQuillanFormalSchemePoints X _ hV

/-- **Stacks 0AI3**, the counterpart of Lemma 87.2.2 in McQuillan's setting, for the big Zariski
topology. The functor of points of a McQuillan formal scheme, on the category of all schemes, is
a sheaf for the big Zariski topology: a matching family of points on the members of any Zariski
covering of a scheme has a unique amalgamation.

The proof is the source's: Zariski coverings are the jointly surjective families of open
immersions, and a matching family of morphisms into a locally topologically ringed space on the
members of an open covering glues uniquely. -/
@[stacks 0AI3 "the counterpart of Lemma 87.2.2: the functor of points of a McQuillan \
formal scheme on all schemes is a sheaf for the big Zariski topology"]
theorem isSheaf_zariskiTopology_mcQuillanFormalSchemePoints (X : McQuillanFormalScheme.{u}) :
    Presieve.IsSheaf Scheme.zariskiTopology.{u} (mcQuillanFormalSchemePoints X) := by
  rw [show Scheme.zariskiTopology.{u}
      = (Scheme.precoverage @IsOpenImmersion).toGrothendieck from rfl,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro Y R hR
  obtain ⟨ι, U, π, rfl⟩ := R.exists_eq_ofArrows
  have hdata := (Scheme.presieve₀_mem_precoverage_iff (P := @IsOpenImmersion)
    (⟨ι, U, π⟩ : PreZeroHypercover Y)).mp hR
  have : ∀ i, IsOpenImmersion (π i) := fun i => hdata.2 i
  exact isSheafFor_ofArrows_mcQuillanFormalSchemePoints X U π fun x => hdata.1 x

end AlgebraicGeometry

end
