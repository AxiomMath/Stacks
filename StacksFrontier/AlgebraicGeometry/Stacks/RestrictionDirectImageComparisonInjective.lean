module

public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionDirectImageChartFactorization

/-!
# Injectivity of the comparison map of equation 075M on sections over a chart

This file proves that the comparison map of equation 075M,
`AlgebraicGeometry.Space.restrictedDirectImageComparisonHom`, is **injective** on sections over
every étale scheme chart `V` of `G`.

The two inputs are the factorization lemma of
`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionDirectImageChartFactorization.lean` and the
pushforward formula of Stacks 06W6: a section of `f_*ℱ` over an object of `𝒴` is determined by
the family of its values at the pairs `(Z, κ : f(Z) ⟶ T)`, which is what
`AlgebraicGeometry.Space.ran_ext` says.

## Main definitions

* `AlgebraicGeometry.Space.ranSection`: the value at a pair `(Z, κ : f(Z) ⟶ T)` of a section of
  `f_*ℱ` over `T` — restrict along `κ` and apply the counit of the right Kan extension. The
  map of sections out of which the comparison of equation 075M is built,
  `AlgebraicGeometry.Space.restrictedDirectImageComparisonSections`, is this at the pair
  attached to a chart diagram.

## Main results

* `AlgebraicGeometry.Space.ranSection_comp`: the values are compatible with precomposition, by
  naturality of the counit.
* `AlgebraicGeometry.Space.ran_ext`: a section of `f_*ℱ` is determined by its values. This is
  Stacks 06W6, `CategoryTheory.Presheaf.pushforwardSectionsEquiv`, read as an extensionality
  principle: those values are the components of the corresponding global section over the
  2-fibre product.
* `AlgebraicGeometry.Space.FMap.app_congr_of_pushforwardHom_app_eq`: the map of sections of an
  `fSp`-map over a diagram of étale scheme charts is determined by the homomorphism the chart
  correspondence of Stacks 03G8 attaches to it, read on sections over the chart of the target.
  This is `AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse_chart` at the arrow into
  the cartesian base change that a chart diagram provides.
* `AlgebraicGeometry.Space.ranSection_congr_of_comparisonHom_app_eq` and
  `AlgebraicGeometry.Space.ranSection_congr_of_forall_chart`: two sections with the same image
  under the comparison map have the same value at every morphism out of the image of an étale
  chart of `F`, hence — by the factorization lemma and the sheaf condition — at every morphism
  of `𝒴` into `u_G V` whatever.
* `AlgebraicGeometry.Space.injective_restrictedDirectImageComparisonHom_app`: **the comparison
  map of equation 075M is injective on sections over an étale scheme chart of `G`.**

## References

* [Stacks Project, Tag 075M](https://stacks.math.columbia.edu/tag/075M)
* [Stacks Project, Tag 06W6](https://stacks.math.columbia.edu/tag/06W6)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
  (eF : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (f : 𝒳 ⥤ 𝒴) (hf : p.IsFibredOneMorphism q f)
  (fSpace : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
  (ha : schemeChartFunctor B S hS F p eF ⋙ f ≅
    CostructuredArrow.map fSpace.hom ⋙ schemeChartFunctor B S hS G q eG)
  [∀ H : 𝒳ᵒᵖ ⥤ Type u, f.op.HasPointwiseRightKanExtension H]

/-! ### The chart correspondence determines the maps of sections -/

section ChartCorrespondence

variable {X Y : AlgebraicSpaces B S hS}

/-- **The map of sections of an `fSp`-map over a diagram of étale scheme charts is determined by
the homomorphism the chart correspondence attaches to it, read on sections over the chart of the
target.**

This is the sectionwise characterization of the chart correspondence of Stacks 03G8,
`AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse_chart`, applied at the arrow into
the cartesian base change that a diagram of charts provides
(`AlgebraicGeometry.Space.baseChangeArrowOfChartDiagram`): that characterization writes the map
of sections, transported through a presentation of the source sheaf by a spaces-étale sheaf, as
a restriction of a section obtained from the homomorphism, so it depends on the latter alone.

The transporting isomorphism is a bijection on sections, which is why no information is lost. -/
theorem FMap.app_congr_of_pushforwardHom_app_eq (fSp : X ⟶ Y)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (ξ : FMap B S hS X.1 Y.1 fSp.hom P.obj Q.obj)
    (d : ChartDiagram B S hS X.1 Y.1 fSp.hom) (s t : Q.obj.obj (op d.V))
    (hst : (fMapEquivPushforwardHom_ringUniverse B S hS fSp P Q ξ).hom.app (op d.V) s =
      (fMapEquivPushforwardHom_ringUniverse B S hS fSp P Q ξ).hom.app (op d.V) t) :
    ξ.app d s = ξ.app d t := by
  set H := (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj P with hH
  set i : P ≅ (smallEtaleComparisonRestriction B S hS X).obj H :=
    ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.app P).symm with hi
  have hc := fMapEquivPushforwardHom_ringUniverse_chart B S hS fSp P Q H i ξ d
    (baseChangeArrowOfChartDiagram B S hS fSp d)
    (heq_of_eq (yoneda_map_baseChangeArrowOfChartDiagram B S hS fSp d))
  have hinj : Function.Injective
      (((sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type u)).mapIso i).app
        (op d.U)).hom :=
    (((sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type u)).mapIso i).app
      (op d.U)).toEquiv.injective
  refine hinj (Eq.trans (hc s) (Eq.trans ?_ (hc t).symm))
  exact congrArg (fun z ↦ H.obj.map (baseChangeArrowOfChartDiagram B S hS fSp d).op
    (((smallEtaleRingedToposHom B S hS fSp).toToposHom.pushforward.map i.hom ≫
      (smallEtaleRingedToposHom_pushforward B S hS fSp).hom.app H).hom.app (op d.V) z)) hst

end ChartCorrespondence

/-! ### The values of a section of a direct image -/

/-- The value at a pair `(Z, κ : f(Z) ⟶ T)` of a section of `f_*ℱ` over an object `T` of `𝒴`:
restrict along `κ`, then apply the counit of the right Kan extension that computes `f_*`.

`AlgebraicGeometry.Space.restrictedDirectImageComparisonSections`, the map of sections out of
which the comparison map of equation 075M is built, is this at the pair attached to a diagram of
étale scheme charts. -/
noncomputable def ranSection
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u))
    {Z : 𝒳} {T : 𝒴} (κ : f.obj Z ⟶ T) (s : (f.op.ran.obj ℱ.obj).obj (op T)) :
    ℱ.obj.obj (op Z) :=
  (f.op.ranCounit.app ℱ.obj).app (op Z) ((f.op.ran.obj ℱ.obj).map κ.op s)

/-- The map of sections of equation 075M at a diagram of étale scheme charts is a value of
`AlgebraicGeometry.Space.ranSection`, namely at the morphism
`AlgebraicGeometry.Space.comparisonChartHom` of `𝒴` the diagram provides. -/
theorem restrictedDirectImageComparisonSections_eq_ranSection
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u))
    (d : ChartDiagram B S hS F G fSpace.hom)
    (s : (f.op.ran.obj ℱ.obj).obj
      (op ((restrictionFunctor B S hS G q eG).obj d.V))) :
    restrictedDirectImageComparisonSections B S hS F G p q hF hG eF eG f fSpace ha ℱ d s =
      ranSection B S hS p f ℱ (comparisonChartHom B S hS p q eF eG f fSpace ha d) s :=
  rfl

/-- **The values of a section of a direct image are compatible with precomposition.** This is
naturality of the counit of the right Kan extension. -/
theorem ranSection_comp
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u))
    {Z Z' : 𝒳} {T : 𝒴} (m : Z' ⟶ Z) (κ : f.obj Z ⟶ T)
    (s : (f.op.ran.obj ℱ.obj).obj (op T)) :
    ranSection B S hS p f ℱ (f.map m ≫ κ) s =
      ℱ.obj.map m.op (ranSection B S hS p f ℱ κ s) := by
  have key : (f.op.ran.obj ℱ.obj).map (f.map m ≫ κ).op s =
      (f.op.ran.obj ℱ.obj).map (f.map m).op ((f.op.ran.obj ℱ.obj).map κ.op s) := by
    rw [← Functor.map_comp_apply, ← op_comp]
  change (f.op.ranCounit.app ℱ.obj).app (op Z')
    ((f.op.ran.obj ℱ.obj).map (f.map m ≫ κ).op s) = _
  rw [key]
  exact NatTrans.naturality_apply (f.op.ranCounit.app ℱ.obj) m.op _

include hq hf in
/-- **A section of a direct image is determined by its values.** Two sections of `f_*ℱ` over an
object `T` of `𝒴` with the same `AlgebraicGeometry.Space.ranSection` at every pair
`(Z, κ : f(Z) ⟶ T)` are equal.

This is the pushforward formula of Stacks 06W6,
`CategoryTheory.Presheaf.pushforwardSectionsEquiv`, read as an extensionality principle: that
bijection carries a section of `f_*ℱ` to a global section over the 2-fibre product
`(Sch/q(T))_{fppf} ×_𝒴 𝒳`, a global section is a compatible family of sections over the objects
of that 2-fibre product, and by
`CategoryTheory.Presheaf.pushforwardSectionsEquiv_apply` the component at an object is one of
these values. -/
theorem ran_ext (c : q.ChoiceOfPullbacks)
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u))
    (T : 𝒴) (s t : (f.op.ran.obj ℱ.obj).obj (op T))
    (h : ∀ (Z : 𝒳) (κ : f.obj Z ⟶ T),
      ranSection B S hS p f ℱ κ s = ranSection B S hS p f ℱ κ t) :
    s = t := by
  refine (Presheaf.pushforwardSectionsEquiv p q f hq hf.comp_eq c
    (CategoryTheory.Functor.Fiber.mk (rfl : q.obj T = q.obj T)) ℱ.obj).injective ?_
  refine (Presheaf.globalSectionsEquivSections _).injective (Subtype.ext ?_)
  funext P
  obtain ⟨P⟩ := P
  have e := fun u ↦ Presheaf.pushforwardSectionsEquiv_apply p q f hq hf.comp_eq c
    (CategoryTheory.Functor.Fiber.mk (rfl : q.obj T = q.obj T)) ℱ.obj u P
  exact (e s).trans ((h _ _).trans (e t).symm)

/-! ### The comparison map determines the maps of sections over chart diagrams -/

/-! ### Injectivity of the comparison map on sections over a chart -/

include hp hq in
/-- **The comparison map of equation 075M determines all the values of a section of `f_*ℱ` at
the morphisms out of the image of an étale scheme chart of `F`.**

Every such morphism is a `AlgebraicGeometry.Space.comparisonChartHom`
(`AlgebraicGeometry.Space.comparisonChartHom_chartDiagramOfHom`), so this is the chart
correspondence of Stacks 03G8 in the form
`AlgebraicGeometry.Space.FMap.app_congr_of_pushforwardHom_app_eq`. -/
theorem ranSection_congr_of_comparisonHom_app_eq
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u))
    (V : SmallEtale B S hS G)
    (s t : ((restrictionSheafFunctor B S hS G q hq eG).obj
      ((etaleDirectImage B S hS p q hp f hf).obj ℱ)).obj.obj (op V))
    (hst : (restrictedDirectImageComparisonHom B S hS F G p q hp hq hF hG eF eG f hf fSpace
          ha ℱ).hom.app (op V) s =
        (restrictedDirectImageComparisonHom B S hS F G p q hp hq hF hG eF eG f hf fSpace
          ha ℱ).hom.app (op V) t)
    (W : SmallEtale B S hS F)
    (κ : f.obj ((restrictionFunctor B S hS F p eF).obj W) ⟶
      (restrictionFunctor B S hS G q eG).obj V) :
    ranSection B S hS p f ℱ κ s = ranSection B S hS p f ℱ κ t := by
  have hfmap := FMap.app_congr_of_pushforwardHom_app_eq B S hS fSpace
    ((restrictionSheafFunctor B S hS F p hp eF).obj ℱ)
    ((restrictionSheafFunctor B S hS G q hq eG).obj
      ((etaleDirectImage B S hS p q hp f hf).obj ℱ))
    (restrictedDirectImageComparisonFMap B S hS F G p q hp hq hF hG eF eG f hf fSpace ha ℱ)
    (chartDiagramOfHom B S hS F G p q hF hG eF eG f fSpace ha W V κ) s t hst
  rw [← comparisonChartHom_chartDiagramOfHom B S hS F G p q hF hG eF eG f fSpace ha W V κ]
  exact hfmap

include hp hF fSpace ha in
/-- **All the values of a section of `f_*ℱ` over `u_G V` are determined by its values at the
morphisms out of the images of the étale scheme charts of `F`.**

An object of `𝒳` is an arbitrary scheme chart of `F`, so it is *not* covered by objects coming
from étale charts of `F` in any sieve generated by morphisms out of them; it is covered by them
in the sense of `CategoryTheory.GrothendieckTopology.CoversTop` only, which is Stacks 073M,
`AlgebraicGeometry.Space.restrictionFunctor_coversTop`. The factorization lemma
`AlgebraicGeometry.Space.exists_chartDiagram_comparisonChartHom_factor` is exactly what bridges
the gap: over each member of that covering sieve the morphism into `u_G V` does factor through
the image of an étale chart, so each restriction of the value is one of the given ones, and the
sheaf condition on `ℱ` finishes. -/
theorem ranSection_congr_of_forall_chart
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u))
    (V : SmallEtale B S hS G)
    (s t : (f.op.ran.obj ℱ.obj).obj (op ((restrictionFunctor B S hS G q eG).obj V)))
    (h : ∀ (W : SmallEtale B S hS F)
        (κ : f.obj ((restrictionFunctor B S hS F p eF).obj W) ⟶
          (restrictionFunctor B S hS G q eG).obj V),
      ranSection B S hS p f ℱ κ s = ranSection B S hS p f ℱ κ t)
    (Z : 𝒳) (κ : f.obj Z ⟶ (restrictionFunctor B S hS G q eG).obj V) :
    ranSection B S hS p f ℱ κ s = ranSection B S hS p f ℱ κ t := by
  refine (((isSheaf_iff_isSheaf_of_type _ ℱ.obj).1 ℱ.2).isSeparated _
    (restrictionFunctor_coversTop B S hS F p hF hp eF Z)).ext ?_
  rintro Z' m ⟨W₁, ⟨n⟩⟩
  obtain ⟨W₂, g, comm, m', hm'⟩ := exists_chartDiagram_comparisonChartHom_factor B S hS F G p q
    hF hG eF eG f fSpace ha V Z' W₁ n (f.map m ≫ κ)
  have key : ∀ x : (f.op.ran.obj ℱ.obj).obj (op ((restrictionFunctor B S hS G q eG).obj V)),
      ℱ.obj.map m.op (ranSection B S hS p f ℱ κ x) =
        ℱ.obj.map m'.op (ranSection B S hS p f ℱ
          (comparisonChartHom B S hS p q eF eG f fSpace ha ⟨W₂, V, g, comm⟩) x) := by
    intro x
    rw [← ranSection_comp, ← ranSection_comp, hm']
  refine Eq.trans (key s) (Eq.trans ?_ (key t).symm)
  exact congrArg (fun z ↦ ℱ.obj.map m'.op z) (h W₂ _)

include hp hq hF hf in
/-- **The comparison map of equation 075M is injective on sections over an étale scheme chart of
`G`.**

Two sections of `(f_*ℱ)|_{G_étale}` over `V` with the same image have the same value at every
morphism `f(u_F W) ⟶ u_G V` by the chart correspondence of Stacks 03G8
(`AlgebraicGeometry.Space.ranSection_congr_of_comparisonHom_app_eq`), hence at *every* morphism
`f(Z) ⟶ u_G V` by the factorization lemma and the sheaf condition
(`AlgebraicGeometry.Space.ranSection_congr_of_forall_chart`), hence are equal by the pushforward
formula of Stacks 06W6 (`AlgebraicGeometry.Space.ran_ext`). -/
theorem injective_restrictedDirectImageComparisonHom_app (c : q.ChoiceOfPullbacks)
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u))
    (V : SmallEtale B S hS G) :
    Function.Injective
      ((restrictedDirectImageComparisonHom B S hS F G p q hp hq hF hG eF eG f hf fSpace
        ha ℱ).hom.app (op V)) := by
  intro s t hst
  refine ran_ext B S hS p q hq f hf c ℱ ((restrictionFunctor B S hS G q eG).obj V) s t ?_
  intro Z κ
  exact ranSection_congr_of_forall_chart B S hS F G p q hp hF hG eF eG f fSpace ha ℱ V s t
    (ranSection_congr_of_comparisonHom_app_eq B S hS F G p q hp hq hF hG eF eG f hf fSpace ha
      ℱ V s t hst) Z κ

end AlgebraicGeometry.Space

end
