module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFpqcSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The functor of points of a formal spectrum as a colimit

Let `A` be an admissible topological ring and `𝔛 = Spf A` the affine formal scheme it defines.
The source identifies the functor of points of Stacks 0AI1 with a colimit,

`h_𝔛 = colim h_{Spec (A/I)}`,

the colimit being taken over the ideals of definition `I` of `A`, ordered by reverse inclusion.
The morphisms `Spec (A/I) → Spf A` of Stacks 0AHY assemble into a cocone on the system of
quotient spectra, and `AlgebraicGeometry.spfQuotientPointsColimitMap` is the comparison map out
of the colimit it induces on functors of points. The colimit is taken in presheaves of sets on
the category of all schemes; restricting along the inclusion of the schemes of size below a
cutoff gives the functor of points of Stacks 0AI1, by
`AlgebraicGeometry.formalSchemeFunctorOfPoints_obj_eq`.

The comparison map is a monomorphism: a morphism `T → Spf A` determines the ring homomorphism
`A → Γ(T, 𝒪_T)` it induces on global sections, two morphisms `T → Spec (A/I)` and
`T → Spec (A/J)` inducing the same morphism to `Spf A` therefore induce the same homomorphism
`A → Γ(T, 𝒪_T)`, and since `A → A/(I ∩ J)` is surjective they agree already over
`Spec (A/(I ∩ J))`, which is the next stage of the system. So the colimit is a subfunctor of
`h_𝔛`, with no hypothesis beyond admissibility.

Surjectivity is the content of Stacks 0AHZ, and the source reduces it to the affine case,
checking on affine schemes being enough because both sides are fppf sheaves (Stacks 0AI2). That
reduction is carried out here: assuming every point of `Spf A` over an *affine* scheme factors
through one of the quotients, the comparison map is locally surjective — indeed already for the
Zariski topology, every scheme having an affine open cover. Together with local injectivity this
says that the comparison map becomes an isomorphism on associated sheaves, which is the source's
equality.

## Main definitions

* `AlgebraicGeometry.spfQuotientDiagram`: the system of quotient spectra `Spec (A/I)`, indexed
  by the ideals of definition with reverse inclusion.
* `AlgebraicGeometry.spfFormalScheme`: the formal spectrum of an admissible topological ring as
  an object of the category of formal schemes.
* `AlgebraicGeometry.spfQuotientPointOn`: the morphism `Spec (A/I) → Spf A` of locally
  topologically ringed spaces.
* `AlgebraicGeometry.formalSchemePointsFunctor`: the functor of points of Stacks 0AI2 as a
  functor of the formal scheme.
* `AlgebraicGeometry.spfQuotientPointsColimitMap`: the comparison map of the colimit formula.
* `AlgebraicGeometry.spfPointGammaHomOn`: the ring homomorphism `A → Γ(T, 𝒪_T)` induced by a point
  of `Spf A` over a scheme `T`.

## Main results

* `AlgebraicGeometry.injective_spfQuotientPointsColimitMap_app` and
  `AlgebraicGeometry.mono_spfQuotientPointsColimitMap`: the comparison map is injective on the
  points over every scheme, so a monomorphism of presheaves.
* `AlgebraicGeometry.isLocallyInjective_spfQuotientPointsColimitMap`: it is locally injective
  for the Zariski topology.
* `AlgebraicGeometry.isLocallySurjective_spfQuotientPointsColimitMap`: granting the affine case,
  it is locally surjective for the Zariski topology.

## Implementation notes

*What is assumed.* Only the affine case of surjectivity is taken as a hypothesis, named
explicitly in `AlgebraicGeometry.isLocallySurjective_spfQuotientPointsColimitMap`. It is the
surjectivity half of the identification
`Mor_{LTRS}(Spf B, Spf A) = Hom_cont(A, B)` of Stacks 0AHZ. That hypothesis is discharged in
`StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsAffine`, which imports this module:
`AlgebraicGeometry.exists_factor_spfQuotientPointOn` proves the affine case and
`AlgebraicGeometry.isLocallySurjective_spfQuotientPointsColimitMap_of_isAdmissible` is the
unconditional conclusion. Everything below is unconditional apart from that one named
hypothesis.

*Why local surjectivity and not surjectivity.* The equality of the source cannot hold for
presheaves: a scheme that is a disjoint union of the `Spec (A/I_n)` for a strictly decreasing
sequence of ideals of definition carries a morphism to `Spf A` factoring through no single
quotient. The colimit of the source is therefore a colimit of sheaves, and the presheaf-level
statement is local bijectivity, which is what is proved.

*Colimits of what size.* The index category is the set of ideals of definition of `A`, so it
lives in the same universe as `A`, and the colimit of presheaves of sets on `Scheme.{u}` exists
without any size cutoff. No sheafification is formed, which would not exist at this size; local
bijectivity is stated through `CategoryTheory.Presheaf.IsLocallyInjective` and
`CategoryTheory.Presheaf.IsLocallySurjective`, which do not refer to it.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ)
* [Stacks Project, Tag 0AI1](https://stacks.math.columbia.edu/tag/0AI1)
* [Stacks Project, Tag 0AIE](https://stacks.math.columbia.edu/tag/0AIE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

open TopologicalRing

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {P : Ideal A → Prop} [IsWeakIdealSystem A P]

/-- The spectra of the quotients of `A` by its ideals of definition, indexed by the ideals of
definition ordered by reverse inclusion: a smaller ideal of definition cuts out a larger
closed subscheme of `Spec A`. -/
@[ega "I 10.10.4" "more general"]
noncomputable def spfQuotientDiagram :
    OrderDual (IdealsOfDefinition A) ⥤ Scheme.{u} where
  obj I := Spec (spfQuotientOn A I.ofDual)
  map {I J} f := Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom f)))
  map_id I := by
    change Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (leOfHom (𝟙 I)))) = 𝟙 _
    simp [Ideal.Quotient.factor_eq]
  map_comp {I J K} f g := by
    have hf : J.ofDual.1 ≤ I.ofDual.1 := leOfHom f
    have hg : K.ofDual.1 ≤ J.ofDual.1 := leOfHom g
    have hfg : K.ofDual.1 ≤ I.ofDual.1 := hg.trans hf
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hfg)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hf)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hg))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (Ideal.Quotient.factor_comp hg hf).symm

/-- The formal spectrum of an admissible topological ring is a formal scheme: it is its own
affine formal chart. -/
theorem isFormalScheme_spfLTRS [IsLinearTopology A A] (hA : IsAdmissible A) :
    IsFormalScheme (spfLTRS A hA.1) := fun _ =>
  ⟨⊤, trivial, TopCommRingCat.of A, inferInstance, hA,
    ⟨PresheafedSpace.restrictTopIso _⟩⟩

/-- The formal spectrum of an admissible topological ring as an object of the category of
formal schemes. -/
@[ega "I 10.1.2"]
noncomputable def spfFormalScheme [IsLinearTopology A A] (hA : IsAdmissible A) :
    FormalScheme.{u} :=
  ⟨spfLTRS A hA.1, isFormalScheme_spfLTRS A hA⟩

/-- The morphism `Spec (A/I) → Spf A` of locally topologically ringed spaces attached to a
member of the weak ideal system. -/
noncomputable def spfQuotientPointOn (I₀ : SpfIndex A P) (I : SpfIndex A P) :
    schemeToLTRSObj (Spec (spfQuotientOn A I)) ⟶ spfLTRSOn A P I₀ where
  toHom := spfPointOn A I
  isLocalHom q := isLocalHom_stalkMap_spfPointOn A I q

/-- The morphism `Spec (A/I) → Spf A` of locally topologically ringed spaces attached to an
ideal of definition.

The ideals-of-definition case of `spfQuotientPointOn`. -/
@[reducible] noncomputable def spfQuotientPoint (hA : IsPreAdmissible A)
    (I : IdealsOfDefinition A) :
    schemeToLTRSObj (Spec (spfQuotient A I)) ⟶ spfLTRS A hA :=
  spfQuotientPointOn (A := A) (P := IsIdealOfDefinition) (I₀ := preAdmissibleSpfIndex A hA)
    (I := I)

/-- The morphisms `Spec (A/I) → Spf A` are compatible with the transition maps
`Spec (A/J) → Spec (A/I)` of the system of quotients. -/
theorem schemeToLTRSHom_comp_spfPointOn {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫
      spfPointOn A I = spfPointOn A J :=
  PresheafedSpace.hext _ _ rfl (heq_of_eq (NatTrans.ext (funext fun V => Subtype.ext
    (RingHom.ext fun s => spfProjectionOn_app_spfTransitionOn_app A h V s))))

/-- The morphisms `Spec (A/I) → Spf A` are compatible with the transition maps
`Spec (A/J) → Spec (A/I)` of the system of quotients.

The ideals-of-definition case of `schemeToLTRSHom_comp_spfPointOn`. -/
theorem schemeToLTRSHom_comp_spfPoint {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1) :
    schemeToLTRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) ≫
      spfPoint A I = spfPoint A J :=
  schemeToLTRSHom_comp_spfPointOn (A := A) (P := IsIdealOfDefinition) (I := I) (J := J) (h := h)

/-- The ring homomorphism `A → Γ(T, 𝒪_T)` attached to a point of `Spf A` over a scheme `T`:
the map the point induces on global sections, read through the canonical map
`A → Γ(Spf A, 𝒪_{Spf A})`. -/
noncomputable def spfPointGammaHomOn {I₀ : SpfIndex A P} {T : Scheme.{u}}
    (g : schemeToLTRSObj T ⟶ spfLTRSOn A P I₀) : CommRingCat.of A ⟶ Γ(T, ⊤) :=
  CommRingCat.ofHom (spfGammaHomOn A P ≫ ltrsGlobalSectionsMap g).1

/-- The ring homomorphism `A → Γ(T, 𝒪_T)` attached to a point of `Spf A` over a scheme `T`:
the map the point induces on global sections, read through the canonical map
`A → Γ(Spf A, 𝒪_{Spf A})`.

The ideals-of-definition case of `spfPointGammaHomOn`. -/
@[reducible] noncomputable def spfPointGammaHom (hA : IsPreAdmissible A) {T : Scheme.{u}}
    (g : schemeToLTRSObj T ⟶ spfLTRS A hA) : CommRingCat.of A ⟶ Γ(T, ⊤) :=
  spfPointGammaHomOn (A := A) (P := IsIdealOfDefinition) (I₀ := preAdmissibleSpfIndex A hA)
    (T := T) (g := g)

/-- The ring homomorphism attached to a point of `Spf A` that factors through the quotient
`Spec (A/I)` is the quotient map `A → A/I` followed by the ring homomorphism of the factoring
morphism of schemes. -/
theorem spfPointGammaHomOn_comp_spfQuotientPointOn (I₀ : SpfIndex A P)
    (I : SpfIndex A P) {T : Scheme.{u}} (a : T ⟶ Spec (spfQuotientOn A I)) :
    spfPointGammaHomOn A ((schemeToFormalScheme.map a).hom ≫ spfQuotientPointOn A I₀ I)
      = spfGammaComponentHomOn A I ≫ a.appTop := by
  apply CommRingCat.hom_ext
  refine RingHom.ext fun x => ?_
  have hx : ((spfProjectionOn A I).app (op ⊤)).1 ((spfGammaHomOn A P).1 x)
      = (spfGammaComponentHomOn A I).hom x :=
    congrArg (fun k : TopCommRingCat.of A ⟶
        ((spfDiagramOn A P ⋙ pseudoDiscreteFunctor).obj I).obj (op ⊤) => k.1 x)
      (spfGammaHomOn_comp_spfProjection_app_top A I)
  change (Scheme.Hom.appTop a).hom
    (((spfProjectionOn A I).app (op ⊤)).1 ((spfGammaHomOn A P).1 x)) = _
  rw [hx]
  rfl

/-- The ring homomorphism attached to a point of `Spf A` that factors through the quotient
`Spec (A/I)` is the quotient map `A → A/I` followed by the ring homomorphism of the factoring
morphism of schemes.

The ideals-of-definition case of `spfPointGammaHomOn_comp_spfQuotientPointOn`. -/
theorem spfPointGammaHom_comp_spfQuotientPoint (hA : IsPreAdmissible A)
    (I : IdealsOfDefinition A) {T : Scheme.{u}} (a : T ⟶ Spec (spfQuotient A I)) :
    spfPointGammaHom A hA ((schemeToFormalScheme.map a).hom ≫ spfQuotientPoint A hA I)
      = spfGammaComponentHom A I ≫ a.appTop :=
  spfPointGammaHomOn_comp_spfQuotientPointOn (A := A) (P := IsIdealOfDefinition)
    (I₀ := preAdmissibleSpfIndex A hA) (I := I) (T := T) (a := a)

/-- The cocone on the system of quotient spectra with vertex `Spf A`, whose legs are the
morphisms `Spec (A/I) → Spf A`. -/
noncomputable def spfQuotientCocone [IsLinearTopology A A] (hA : IsAdmissible A) :
    Cocone (spfQuotientDiagram A ⋙ schemeToFormalScheme) where
  pt := spfFormalScheme A hA
  ι :=
    { app := fun I =>
        ObjectProperty.homMk (spfQuotientPointOn A (preAdmissibleSpfIndex A hA.1) I.ofDual)
      naturality := fun _ _ f => InducedCategory.hom_ext
        (LocallyTopologicallyRingedSpace.Hom.ext'
          (schemeToLTRSHom_comp_spfPointOn A (leOfHom f))) }

/-- The functor of points of a formal scheme on the category of all schemes, as a functor of the
formal scheme. -/
noncomputable def formalSchemePointsFunctor :
    FormalScheme.{u} ⥤ (Scheme.{u})ᵒᵖ ⥤ Type u :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj schemeToFormalScheme.op

/-- The functor of points functor evaluates to the functor of points. -/
theorem formalSchemePointsFunctor_obj (X : FormalScheme.{u}) :
    formalSchemePointsFunctor.obj X = formalSchemePoints X := rfl

/-- The system of functors of points of the quotient spectra `Spec (A/I)`. -/
noncomputable def spfQuotientPointsDiagram :
    OrderDual (IdealsOfDefinition A) ⥤ (Scheme.{u})ᵒᵖ ⥤ Type u :=
  spfQuotientDiagram A ⋙ schemeToFormalScheme ⋙ formalSchemePointsFunctor

/-- The cocone on the system of functors of points of the quotient spectra with vertex the
functor of points of `Spf A`. -/
noncomputable def spfQuotientPointsCocone [IsLinearTopology A A] (hA : IsAdmissible A) :
    Cocone (spfQuotientPointsDiagram A) where
  pt := formalSchemePoints (spfFormalScheme A hA)
  ι := (formalSchemePointsFunctor.mapCocone (spfQuotientCocone A hA)).ι

/-- **Stacks 0AIE.** The comparison map of the source's colimit formula
`h_{Spf A} = colim h_{Spec (A/I)}`: the morphism out of the colimit of the functors of points of
the quotient spectra determined by the morphisms `Spec (A/I) → Spf A`. -/
@[stacks 0AIE "the comparison map h_colim → h_Spf A of the colimit formula"]
noncomputable def spfQuotientPointsColimitMap [IsLinearTopology A A] (hA : IsAdmissible A) :
    colimit (spfQuotientPointsDiagram A) ⟶ formalSchemePoints (spfFormalScheme A hA) :=
  colimit.desc (spfQuotientPointsDiagram A) (spfQuotientPointsCocone A hA)

/-- A point of the colimit is sent to the corresponding point of `Spf A`: the morphism
`T → Spec (A/I)` followed by `Spec (A/I) → Spf A`. -/
theorem spfQuotientPointsColimitMap_app_ι [IsLinearTopology A A] (hA : IsAdmissible A)
    (T : Scheme.{u}) (I : OrderDual (IdealsOfDefinition A))
    (y : ((spfQuotientPointsDiagram A).obj I).obj (op T)) :
    (spfQuotientPointsColimitMap A hA).app (op T)
        ((colimit.ι (spfQuotientPointsDiagram A) I).app (op T) y) =
      y ≫ (spfQuotientCocone A hA).ι.app I :=
  congrArg (fun m => m y)
    (colimit.ι_desc_app (spfQuotientPointsDiagram A) (spfQuotientPointsCocone A hA) I (op T))

omit [IsTopologicalRing A] in
/-- The ideals of definition, ordered by reverse inclusion, form a filtered category: the
intersection of two ideals of definition is an ideal of definition. -/
theorem isFilteredOrEmpty_orderDual_idealsOfDefinition :
    IsFilteredOrEmpty (OrderDual (IdealsOfDefinition A)) where
  cocone_objs I J :=
    ⟨OrderDual.toDual ⟨I.ofDual.1 ⊓ J.ofDual.1,
        IsIdealOfDefinition.inf I.ofDual.2 J.ofDual.2⟩,
      homOfLE (show I.ofDual.1 ⊓ J.ofDual.1 ≤ I.ofDual.1 from inf_le_left),
      homOfLE (show I.ofDual.1 ⊓ J.ofDual.1 ≤ J.ofDual.1 from inf_le_right), trivial⟩
  cocone_maps _ J _ _ := ⟨J, 𝟙 _, Subsingleton.elim _ _⟩

/-- **Stacks 0AIE.** The comparison map of the colimit formula is injective on the points over
every scheme: two morphisms `T → Spec (A/I)` and `T → Spec (A/J)` inducing the same point of
`Spf A` already agree over `Spec (A/(I ∩ J))`. -/
@[stacks 0AIE "the comparison map of the colimit formula is injective at every test scheme"]
theorem injective_spfQuotientPointsColimitMap_app [IsLinearTopology A A] (hA : IsAdmissible A)
    (T : Scheme.{u}) :
    Function.Injective ((spfQuotientPointsColimitMap A hA).app (op T)) := by
  let _ : IsFilteredOrEmpty (OrderDual (IdealsOfDefinition A)) :=
    isFilteredOrEmpty_orderDual_idealsOfDefinition A
  have hcol : IsColimit (((evaluation (Scheme.{u})ᵒᵖ (Type u)).obj (op T)).mapCocone
      (colimit.cocone (spfQuotientPointsDiagram A))) :=
    isColimitOfPreserves _ (colimit.isColimit (spfQuotientPointsDiagram A))
  intro p q hpq
  obtain ⟨I, y, rfl⟩ := Types.jointly_surjective_of_isColimit hcol p
  obtain ⟨J, z, rfl⟩ := Types.jointly_surjective_of_isColimit hcol q
  obtain ⟨a, rfl⟩ := schemeToFormalScheme.map_surjective y
  obtain ⟨b, rfl⟩ := schemeToFormalScheme.map_surjective z
  have hltrs : (schemeToFormalScheme.map a).hom ≫
        spfQuotientPointOn A (preAdmissibleSpfIndex A hA.1) I.ofDual =
      (schemeToFormalScheme.map b).hom ≫
        spfQuotientPointOn A (preAdmissibleSpfIndex A hA.1) J.ofDual :=
    congrArg (fun m : schemeToFormalScheme.obj T ⟶ spfFormalScheme A hA => m.hom)
      ((spfQuotientPointsColimitMap_app_ι A hA T I (schemeToFormalScheme.map a)).symm.trans
        (hpq.trans (spfQuotientPointsColimitMap_app_ι A hA T J (schemeToFormalScheme.map b))))
  have hgamma : spfGammaComponentHomOn A I.ofDual ≫ Scheme.Hom.appTop a =
      spfGammaComponentHomOn A J.ofDual ≫ Scheme.Hom.appTop b := by
    rw [← spfPointGammaHomOn_comp_spfQuotientPointOn A (preAdmissibleSpfIndex A hA.1) I.ofDual a,
      ← spfPointGammaHomOn_comp_spfQuotientPointOn A (preAdmissibleSpfIndex A hA.1) J.ofDual b]
    exact congrArg (spfPointGammaHomOn A) hltrs
  let K : IdealsOfDefinition A :=
    ⟨I.ofDual.1 ⊓ J.ofDual.1, IsIdealOfDefinition.inf I.ofDual.2 J.ofDual.2⟩
  have hKI : K.1 ≤ I.ofDual.1 := inf_le_left
  have hKJ : K.1 ≤ J.ofDual.1 := inf_le_right
  have hepi : Epi (spfGammaComponentHomOn A K) := by
    rw [spfGammaComponentHomOn]
    have : Epi (CommRingCat.ofHom (Ideal.Quotient.mk K.1)) :=
      ConcreteCategory.epi_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have hcancel : Scheme.Hom.appTop
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hKI))) ≫ Scheme.Hom.appTop a =
      Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hKJ))) ≫
        Scheme.Hom.appTop b :=
    (cancel_epi (spfGammaComponentHomOn A K)).1 (by
      rwa [← Category.assoc, ← Category.assoc,
        spfGammaComponentHomOn_comp A hKI, spfGammaComponentHomOn_comp A hKJ])
  have hscheme : a ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hKI)) =
      b ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hKJ)) :=
    ext_of_isAffine hcancel
  refine (Types.FilteredColimit.isColimit_eq_iff _ hcol).2
    ⟨OrderDual.toDual K, homOfLE hKI, homOfLE hKJ, ?_⟩
  change schemeToFormalScheme.map a ≫
      schemeToFormalScheme.map ((spfQuotientDiagram A).map (homOfLE hKI)) =
    schemeToFormalScheme.map b ≫
      schemeToFormalScheme.map ((spfQuotientDiagram A).map (homOfLE hKJ))
  rw [← schemeToFormalScheme.map_comp, ← schemeToFormalScheme.map_comp]
  exact congrArg schemeToFormalScheme.map hscheme

/-- **Stacks 0AIE.** The colimit of the functors of points of the quotient spectra is a
subfunctor of the functor of points of `Spf A`: the comparison map is a monomorphism of
presheaves, being injective on the points over every scheme. -/
@[stacks 0AIE "the comparison map of the colimit formula is a monomorphism of presheaves"]
theorem mono_spfQuotientPointsColimitMap [IsLinearTopology A A] (hA : IsAdmissible A) :
    Mono (spfQuotientPointsColimitMap A hA) := by
  have : ∀ T, Mono ((spfQuotientPointsColimitMap A hA).app T) := fun T =>
    ConcreteCategory.mono_of_injective _
      (injective_spfQuotientPointsColimitMap_app A hA T.unop)
  exact NatTrans.mono_of_mono_app _

/-- **Stacks 0AIE.** The comparison map of the colimit formula is locally injective for the
Zariski topology on schemes, being injective on the points over every scheme. -/
@[stacks 0AIE "the comparison map of the colimit formula is locally injective"]
theorem isLocallyInjective_spfQuotientPointsColimitMap [IsLinearTopology A A]
    (hA : IsAdmissible A) :
    Presheaf.IsLocallyInjective Scheme.zariskiTopology.{u}
      (spfQuotientPointsColimitMap A hA) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun T =>
    injective_spfQuotientPointsColimitMap_app A hA T.unop

/-- **Stacks 0AIE.** The reduction of the colimit formula to the affine case. If every point of
`Spf A` over an affine scheme factors through one of the quotients `Spec (A/I)`, then the
comparison map of the colimit formula is locally surjective for the Zariski topology, because
every scheme has an affine open cover.

The hypothesis is the surjectivity half of the identification
`Mor(Spec B, Spf A) = Hom_cont(A, Γ(Spec B, 𝒪))` of Stacks 0AHZ. It is proved in
`AlgebraicGeometry.exists_factor_spfQuotientPointOn`, so the conclusion holds with no hypothesis
beyond admissibility; that is
`AlgebraicGeometry.isLocallySurjective_spfQuotientPointsColimitMap_of_isAdmissible`. -/
@[stacks 0AIE "the colimit formula is locally surjective, assuming its affine case (the \
surjectivity half of Stacks 0AHZ)"]
theorem isLocallySurjective_spfQuotientPointsColimitMap [IsLinearTopology A A]
    (hA : IsAdmissible A)
    (haff : ∀ T : Scheme.{u}, IsAffine T →
      Function.Surjective ((spfQuotientPointsColimitMap A hA).app (op T))) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology.{u}
      (spfQuotientPointsColimitMap A hA) where
  imageSieve_mem {T} s := by
    rw [Scheme.mem_grothendieckTopology_iff]
    refine ⟨T.affineCover, ?_⟩
    rintro V g ⟨i⟩
    exact haff (T.affineCover.X i) inferInstance _

end AlgebraicGeometry

end
