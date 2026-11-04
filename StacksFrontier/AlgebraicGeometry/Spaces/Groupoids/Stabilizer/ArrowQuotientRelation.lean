module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ArrowQuotient

/-!
# The quotient of the arrow space by the stabilizer is an equivalence relation (Stacks 06QJ)

Let `G` be a groupoid in algebraic spaces over `B`, with object space `U` and arrow space `R`,
let `S ⟶ U` be its stabilizer group algebraic space (**Stacks 0448**) acting on `R` over `U`
through the target morphism (**Stacks 0449**), and let

    R' = R/S

be the quotient of `StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ArrowQuotient`,
with `π : R ⟶ R'` the quotient map and `s', t' : R' ⟶ U` the descended source and target. This
file proves that

    j' = (t', s') : R' ⟶ U ×_B U

is a *monomorphism* and a *pre-equivalence relation*, hence an *equivalence relation* in the sense
of **Stacks 043C** parts (2), (3) and (4).

This is the step of the proof of **Stacks 06QJ**, the implication (2) `⟹` (1), after which
`X = U/R'` is an algebraic space by **Stacks 04S6** and `[U/R] ⟶ X` is the 1-morphism that has to
be shown a gerbe.

Nothing is assumed: neither flatness nor local finite presentation of the stabilizer, nor
algebraicity of `R'`, enters anywhere below.

## The monomorphism

* Two generalized arrows of `G` with the same source and the same target lie in one orbit of
  the stabilizer action, so `π` already identifies them. That is
  `toArrowStabilizerQuotient_eq_of_source_eq_of_target_eq` of
  `StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ArrowQuotient`, and it needs no
  covering.
* Two sections of `R'` over a test object with the same image under `s'` and under `t'` agree:
  `π` is a surjection of fppf sheaves, so after an fppf covering both lift to sections of `R`;
  the lifts then have the same source and the same target, because `s = π ≫ s'` and
  `t = π ≫ t'`, so the previous point identifies them; and `R'` is an fppf sheaf, hence
  separated, so the two sections agree outright. This is the source's fppf-covering argument and
  it is `arrowStabilizerQuotient_app_injective`.

## The pre-equivalence relation

Reflexivity and symmetry are *global*: the unit of the groupoid composed with `π` is a section of
both `t'` and `s'`, and the inverse of the groupoid descends to a morphism
`arrowStabilizerQuotientInverse` of `R'` exchanging them — it descends because an arrow and its
translate by a stabilizer element have inverses with the same endpoints, which is again
`toArrowStabilizerQuotient_eq_of_source_eq_of_target_eq`.

Transitivity is the one local step. The two given points of `R'` lift to arrows of `R` after an
fppf covering, those arrows are composable because the middle endpoints agree, and their
composites glue back to a single point of `R'`: the local composites agree on overlaps *because*
`j'` is a monomorphism, and `R'` is a sheaf. That gluing is
`exists_hom_arrowStabilizerQuotient_of_locally`, which is where the monomorphism feeds back into
the pre-equivalence clause.

## Main definitions

All of these live in the namespace `AlgebraicGeometry.GroupoidInAlgebraicSpaces`.

* `arrowStabilizerQuotientPreRelation`: the pre-relation `j' = (t', s') : R' ⟶ U ×_B U` of
  **Stacks 043C** part (1), taken in the slice of presheaves over the base.
* `arrowStabilizerQuotientInverse`: the descended inverse `R' ⟶ R'`.

## Main results

* `toArrowStabilizerQuotient_app_eq_of_endpoints_eq`: two sections of `R` over a test object
  with the same source and the same target have the same image in `R/S` — the pointwise form of
  `toArrowStabilizerQuotient_eq_of_source_eq_of_target_eq`.
* `arrowStabilizerQuotient_app_injective`: a section of `R'` is determined by its source and its
  target.
* `eq_of_comp_arrowStabilizerQuotient_endpoints_eq`: the pair `(t', s')` is jointly monic.
* `arrowStabilizerQuotientSource_comp_objectsToBase`: `s'` and `t'` have the same composite to
  the base, so `j'` exists.
* `mono_arrowStabilizerQuotientPreRelation`: `j'` is a monomorphism.
* `exists_hom_arrowStabilizerQuotient_of_locally`: a point of `R'` with prescribed endpoints
  exists as soon as it exists fppf-locally.
* `exists_covering_lift_arrowStabilizerQuotient`: a point of `R'` lifts to `R` after an fppf
  covering.
* `arrowStabilizerQuotientInverse_comp_target` and
  `arrowStabilizerQuotientInverse_comp_source`: the descended inverse exchanges `t'` and `s'`.
* `isPreEquivalenceRelation_arrowStabilizerQuotientPreRelation` and
  `isEquivalenceRelation_arrowStabilizerQuotientPreRelation`: `j'` is a pre-equivalence relation
  and an equivalence relation. The second is the statement the proof of Stacks 06QJ uses.

## Implementation notes

Separatedness and the sheaf condition of `R'` are taken from its sheaf property through
`CategoryTheory.Presieve.IsSheafFor`; the covering in the injectivity statement is the
intersection of the two image sieves of `π`, which are covering because `π` is locally surjective
(`isLocallySurjective_toArrowStabilizerQuotient`). No step uses that `R'` is an algebraic space,
which is why this file is independent of **Stacks 06PH**.

The equivalence-relation statement is `CategoryTheory.IsEquivalenceRelation`, which asks for
*morphisms* witnessing reflexivity, symmetry and transitivity; it is obtained from the
monomorphism and the pointwise pre-equivalence clause by
`AlgebraicGeometry.Space.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation`, so the
transitivity morphism never has to be written down.

The monomorphism is stated for the pre-relation of **Stacks 043C** in the slice of presheaves over
the base presheaf, the same shape as
`AlgebraicGeometry.Space.groupoidPreRelation`, so that the criteria of
`StacksFrontier.AlgebraicGeometry.Spaces.RelationsOverSpace` apply to it verbatim. Monicity there is
deduced from joint monicity of `(t', s')` by composing with the two projections of the product,
exactly as in `AlgebraicGeometry.Space.PreRelation.testPoint_eq_of_mono`.

## References

* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 043X](https://stacks.math.columbia.edu/tag/043X)
* [Stacks Project, Tag 044J](https://stacks.math.columbia.edu/tag/044J)
* [Stacks Project, Tag 0448](https://stacks.math.columbia.edu/tag/0448)
* [Stacks Project, Tag 0449](https://stacks.math.columbia.edu/tag/0449)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 06PG](https://stacks.math.columbia.edu/tag/06PG)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CartesianMonoidalCategory MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

section Quotient

variable [HasSheafify (BigFppfOver.topology C S hS) (Type u)]

/-- **Two arrows over a test object with the same source and the same target have the same image
in `R/S`.** The generalized form of the statement at the presheaf represented by the test
object. -/
theorem toArrowStabilizerQuotient_app_eq_of_endpoints_eq
    (G : GroupoidInAlgebraicSpaces C S hS B) (W : BigFppfOver C S hS)
    (x y : G.arrows.obj.obj (op W))
    (hs : G.source.hom.app (op W) x = G.source.hom.app (op W) y)
    (ht : G.target.hom.app (op W) x = G.target.hom.app (op W) y) :
    (toArrowStabilizerQuotient G).app (op W) x =
      (toArrowStabilizerQuotient G).app (op W) y := by
  have h := toArrowStabilizerQuotient_eq_of_source_eq_of_target_eq G
    (yonedaEquiv.symm x) (yonedaEquiv.symm y)
    (yonedaEquiv.injective (by simpa [yonedaEquiv_comp] using hs))
    (yonedaEquiv.injective (by simpa [yonedaEquiv_comp] using ht))
  simpa [yonedaEquiv_comp] using congrArg yonedaEquiv h

/-- A map out of `R/S` is determined by its composite with `π` if that composite is constant on
orbits. -/
private theorem eq_of_toArrowStabilizerQuotient_comp_eq
    (G : GroupoidInAlgebraicSpaces C S hS B) {A : Sheaf (BigFppfOver.topology C S hS) (Type u)}
    {k : G.arrows.obj ⟶ A.obj}
    (hk : (stabilizerOrbitRelation G).target.left ≫ k = (stabilizerOrbitRelation G).source.left ≫ k)
    {f g : (arrowStabilizerQuotient G).obj ⟶ A.obj}
    (hf : toArrowStabilizerQuotient G ≫ f = k) (hg : toArrowStabilizerQuotient G ≫ g = k) :
    f = g :=
  congrArg (fun d => d.hom)
    ((Space.quotientSheafDesc_unique (stabilizerOrbitRelation G) A k hk ⟨f⟩ hf).trans
      (Space.quotientSheafDesc_unique (stabilizerOrbitRelation G) A k hk ⟨g⟩ hg).symm)

/-- If `c` is a lift of `z` along `π`, then any map `ψ = π ≫ φ` at `c` is `φ` at `z`, restricted. -/
private theorem app_eq_map_of_toArrowStabilizerQuotient_eq
    (G : GroupoidInAlgebraicSpaces C S hS B) {φ : (arrowStabilizerQuotient G).obj ⟶ G.objects.obj}
    {ψ : G.arrows.obj ⟶ G.objects.obj} (h : toArrowStabilizerQuotient G ≫ φ = ψ)
    {V W : BigFppfOver C S hS} (i : W ⟶ V) (z : (arrowStabilizerQuotient G).obj.obj (op V))
    (c : G.arrows.obj.obj (op W))
    (hc : (toArrowStabilizerQuotient G).app (op W) c = (arrowStabilizerQuotient G).obj.map i.op z) :
    ψ.app (op W) c = G.objects.obj.map i.op (φ.app (op V) z) := by
  rw [← h, ← NatTrans.naturality_apply φ i.op z, ← hc]
  rfl

/-- **A section of `R' = R/S` is determined by its source and its target.** Both sections lift
to `R` after an fppf covering, because `π : R ⟶ R'` is a surjection of fppf sheaves; the lifts
have the same source and the same target, so they already agree in `R'`; and `R'` is an fppf
sheaf, hence separated. -/
theorem arrowStabilizerQuotient_app_injective (G : GroupoidInAlgebraicSpaces C S hS B)
    {V : BigFppfOver C S hS} (x y : (arrowStabilizerQuotient G).obj.obj (op V))
    (hs : (arrowStabilizerQuotientSource G).app (op V) x =
      (arrowStabilizerQuotientSource G).app (op V) y)
    (ht : (arrowStabilizerQuotientTarget G).app (op V) x =
      (arrowStabilizerQuotientTarget G).app (op V) y) :
    x = y := by
  classical
  have hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      (toArrowStabilizerQuotient G) := isLocallySurjective_toArrowStabilizerQuotient G
  have hmem : Presheaf.imageSieve (toArrowStabilizerQuotient G) x ⊓
      Presheaf.imageSieve (toArrowStabilizerQuotient G) y ∈
        BigFppfOver.topology C S hS V :=
    (BigFppfOver.topology C S hS).intersection_covering
      (Presheaf.imageSieve_mem _ (toArrowStabilizerQuotient G) x)
      (Presheaf.imageSieve_mem _ (toArrowStabilizerQuotient G) y)
  have hsheaf := (isSheaf_iff_isSheaf_of_type _ _).1
    (arrowStabilizerQuotient G).property
  refine ((hsheaf _ hmem).isSeparatedFor).ext ?_
  intro W i hi
  obtain ⟨hix, hiy⟩ := hi
  have hax := Presheaf.app_localPreimage (toArrowStabilizerQuotient G) x i hix
  have hby := Presheaf.app_localPreimage (toArrowStabilizerQuotient G) y i hiy
  rw [← hax, ← hby]
  refine toArrowStabilizerQuotient_app_eq_of_endpoints_eq G W _ _ ?_ ?_
  · rw [app_eq_map_of_toArrowStabilizerQuotient_eq G (toArrowStabilizerQuotient_comp_source G) i
      x _ hax, app_eq_map_of_toArrowStabilizerQuotient_eq G
      (toArrowStabilizerQuotient_comp_source G) i y _ hby, hs]
  · rw [app_eq_map_of_toArrowStabilizerQuotient_eq G (toArrowStabilizerQuotient_comp_target G) i
      x _ hax, app_eq_map_of_toArrowStabilizerQuotient_eq G
      (toArrowStabilizerQuotient_comp_target G) i y _ hby, ht]

/-- **The pair `(t', s')` is jointly monic.** Two maps into `R'` which agree after both `s'` and
`t'` are equal. -/
theorem eq_of_comp_arrowStabilizerQuotient_endpoints_eq
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {W : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {f g : W ⟶ (arrowStabilizerQuotient G).obj}
    (hs : f ≫ arrowStabilizerQuotientSource G = g ≫ arrowStabilizerQuotientSource G)
    (ht : f ≫ arrowStabilizerQuotientTarget G = g ≫ arrowStabilizerQuotientTarget G) :
    f = g := by
  ext V w
  exact arrowStabilizerQuotient_app_injective G (V := V.unop) _ _
    (congrArg (fun k => k.app V w) hs) (congrArg (fun k => k.app V w) ht)

/-- The descended source and target of `R' = R/S` have the same composite to the base: both
restrict along `π` to the structure morphism of the arrow space. -/
theorem arrowStabilizerQuotientSource_comp_objectsToBase
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowStabilizerQuotientSource G ≫ G.objectsToBase.hom =
      arrowStabilizerQuotientTarget G ≫ G.objectsToBase.hom := by
  have hbase : G.source.hom ≫ G.objectsToBase.hom = G.target.hom ≫ G.objectsToBase.hom :=
    (congrArg (fun f : G.arrows ⟶ B => f.hom) G.source_over).trans
      (congrArg (fun f : G.arrows ⟶ B => f.hom) G.target_over).symm
  refine eq_of_toArrowStabilizerQuotient_comp_eq G (A := ⟨B.obj, B.property.isSheaf⟩)
    (k := G.source.hom ≫ G.objectsToBase.hom)
    (by simpa only [Category.assoc] using
      congrArg (· ≫ G.objectsToBase.hom) (stabilizerOrbitRelation_source_eq G)) ?_ ?_
  · rw [← Category.assoc, toArrowStabilizerQuotient_comp_source]
  · rw [← Category.assoc, toArrowStabilizerQuotient_comp_target, hbase]

/-! ### Reflexivity, symmetry and the fppf-local gluing of sections -/

/-- The descended source, read on the image of a section of the arrow space, is the source of
that section: the equation `s = π ≫ s'` at a section. -/
theorem arrowStabilizerQuotientSource_app_toArrowStabilizerQuotient
    (G : GroupoidInAlgebraicSpaces C S hS B) (W : BigFppfOver C S hS)
    (c : G.arrows.obj.obj (op W)) :
    (arrowStabilizerQuotientSource G).app (op W)
        ((toArrowStabilizerQuotient G).app (op W) c) = G.source.hom.app (op W) c := by
  simpa using congrArg (fun k => k.app (op W) c) (toArrowStabilizerQuotient_comp_source G)

/-- The descended target, read on the image of a section of the arrow space, is the target of
that section: the equation `t = π ≫ t'` at a section. -/
theorem arrowStabilizerQuotientTarget_app_toArrowStabilizerQuotient
    (G : GroupoidInAlgebraicSpaces C S hS B) (W : BigFppfOver C S hS)
    (c : G.arrows.obj.obj (op W)) :
    (arrowStabilizerQuotientTarget G).app (op W)
        ((toArrowStabilizerQuotient G).app (op W) c) = G.target.hom.app (op W) c := by
  simpa using congrArg (fun k => k.app (op W) c) (toArrowStabilizerQuotient_comp_target G)

/-- **A section of `R' = R/S` with prescribed target and source exists as soon as it exists
fppf-locally.** The local sections agree on overlaps because `j' = (t', s')` is a monomorphism,
so they amalgamate in the fppf sheaf `R'`; the two endpoint equations then descend because the
object space is a sheaf too. -/
theorem exists_hom_arrowStabilizerQuotient_of_locally
    (G : GroupoidInAlgebraicSpaces C S hS B) {T : BigFppfOver C S hS}
    (x y : yoneda.obj T ⟶ G.objects.obj) {W : Sieve T}
    (hW : W ∈ BigFppfOver.topology C S hS T)
    (h : ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T), W i →
      ∃ z : yoneda.obj V ⟶ (arrowStabilizerQuotient G).obj,
        z ≫ arrowStabilizerQuotientTarget G = yoneda.map i ≫ x ∧
        z ≫ arrowStabilizerQuotientSource G = yoneda.map i ≫ y) :
    ∃ z : yoneda.obj T ⟶ (arrowStabilizerQuotient G).obj,
      z ≫ arrowStabilizerQuotientTarget G = x ∧
      z ≫ arrowStabilizerQuotientSource G = y := by
  classical
  have hR' := (isSheaf_iff_isSheaf_of_type _ _).1 (arrowStabilizerQuotient G).property
  have hU := (isSheaf_iff_isSheaf_of_type _ _).1 G.objects.property.isSheaf
  have hel : ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T), W.arrows i →
      ∃ z : (arrowStabilizerQuotient G).obj.obj (op V),
        (arrowStabilizerQuotientTarget G).app (op V) z =
            G.objects.obj.map i.op (yonedaEquiv x) ∧
          (arrowStabilizerQuotientSource G).app (op V) z =
            G.objects.obj.map i.op (yonedaEquiv y) := by
    intro V i hi
    obtain ⟨z, hzt, hzs⟩ := h i hi
    refine ⟨yonedaEquiv z, ?_, ?_⟩
    · rw [yonedaEquiv_naturality]
      exact congrArg yonedaEquiv hzt
    · rw [yonedaEquiv_naturality]
      exact congrArg yonedaEquiv hzs
  let fam : Presieve.FamilyOfElements (arrowStabilizerQuotient G).obj W.arrows :=
    fun _ i hi => (hel i hi).choose
  have hft : ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T) (hi : W.arrows i),
      (arrowStabilizerQuotientTarget G).app (op V) (fam i hi) =
        G.objects.obj.map i.op (yonedaEquiv x) := fun _ i hi => (hel i hi).choose_spec.1
  have hfs : ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T) (hi : W.arrows i),
      (arrowStabilizerQuotientSource G).app (op V) (fam i hi) =
        G.objects.obj.map i.op (yonedaEquiv y) := fun _ i hi => (hel i hi).choose_spec.2
  have hmap : ∀ (φ : (arrowStabilizerQuotient G).obj ⟶ G.objects.obj)
      (u : G.objects.obj.obj (op T)),
      (∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T) (hi : W.arrows i),
        φ.app (op V) (fam i hi) = G.objects.obj.map i.op u) →
      ∀ ⦃V V' : BigFppfOver C S hS⦄ (g : V' ⟶ V) (i : V ⟶ T) (hi : W.arrows i),
        φ.app (op V') ((arrowStabilizerQuotient G).obj.map g.op (fam i hi)) =
          G.objects.obj.map (g ≫ i).op u := by
    intro φ u hf V V' g i hi
    rw [NatTrans.naturality_apply, hf i hi, ← Functor.map_comp_apply]
    rfl
  have hcompat : fam.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    refine arrowStabilizerQuotient_app_injective G _ _ ?_ ?_
    · rw [hmap _ _ hfs g₁ f₁ h₁, hmap _ _ hfs g₂ f₂ h₂, hcomm]
    · rw [hmap _ _ hft g₁ f₁ h₁, hmap _ _ hft g₂ f₂ h₂, hcomm]
  obtain ⟨z, hz, -⟩ := hR' W hW fam hcompat
  have hend : ∀ (φ : (arrowStabilizerQuotient G).obj ⟶ G.objects.obj)
      (u : G.objects.obj.obj (op T)),
      (∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T) (hi : W.arrows i),
        φ.app (op V) (fam i hi) = G.objects.obj.map i.op u) →
      φ.app (op T) z = u := fun φ u hf =>
    (hU W hW).isSeparatedFor.ext fun V i hi => by
      rw [← NatTrans.naturality_apply φ i.op z, hz i hi, hf i hi]
  refine ⟨yonedaEquiv.symm z, yonedaEquiv.injective ?_, yonedaEquiv.injective ?_⟩
  · simpa [yonedaEquiv_comp] using hend (arrowStabilizerQuotientTarget G) _ hft
  · simpa [yonedaEquiv_comp] using hend (arrowStabilizerQuotientSource G) _ hfs

/-- **The inverse of the groupoid descends to `R' = R/S`.** The inverse of an arrow and the
inverse of its translate by a stabilizer element have the same source and the same target, so
`toArrowStabilizerQuotient_eq_of_source_eq_of_target_eq` makes `i ≫ π` constant on the orbits. -/
noncomputable def arrowStabilizerQuotientInverse (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowStabilizerQuotient G ⟶ arrowStabilizerQuotient G :=
  Space.quotientSheafDesc (stabilizerOrbitRelation G) (arrowStabilizerQuotient G)
    (groupoidInverse G ≫ toArrowStabilizerQuotient G) (by
      rw [← Category.assoc, ← Category.assoc]
      refine toArrowStabilizerQuotient_eq_of_source_eq_of_target_eq G _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, groupoidInverse_source,
          Space.actionPreRelation_target, Space.actionPreRelation_source]
        exact stabilizerAction_comp_target G
      · rw [Category.assoc, Category.assoc, groupoidInverse_target,
          Space.actionPreRelation_target, Space.actionPreRelation_source]
        exact stabilizerAction_comp_source G)

/-- The descended inverse restricts to the inverse of the groupoid along the quotient map. -/
theorem toArrowStabilizerQuotient_comp_arrowStabilizerQuotientInverse
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    toArrowStabilizerQuotient G ≫ (arrowStabilizerQuotientInverse G).hom =
      groupoidInverse G ≫ toArrowStabilizerQuotient G :=
  Space.toQuotientSheaf_quotientSheafDesc _ _ _ _

/-- The descended inverse exchanges the target and the source of `R' = R/S`. -/
theorem arrowStabilizerQuotientInverse_comp_target
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (arrowStabilizerQuotientInverse G).hom ≫ arrowStabilizerQuotientTarget G =
      arrowStabilizerQuotientSource G := by
  refine eq_of_toArrowStabilizerQuotient_comp_eq G
    (A := ⟨G.objects.obj, G.objects.property.isSheaf⟩)
    (stabilizerOrbitRelation_source_eq G) ?_ (toArrowStabilizerQuotient_comp_source G)
  rw [← Category.assoc, toArrowStabilizerQuotient_comp_arrowStabilizerQuotientInverse,
    Category.assoc, toArrowStabilizerQuotient_comp_target, groupoidInverse_target]

/-- The descended inverse exchanges the source and the target of `R' = R/S`. -/
theorem arrowStabilizerQuotientInverse_comp_source
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (arrowStabilizerQuotientInverse G).hom ≫ arrowStabilizerQuotientSource G =
      arrowStabilizerQuotientTarget G := by
  refine eq_of_toArrowStabilizerQuotient_comp_eq G
    (A := ⟨G.objects.obj, G.objects.property.isSheaf⟩)
    (stabilizerOrbitRelation_target_eq G) ?_ (toArrowStabilizerQuotient_comp_target G)
  rw [← Category.assoc, toArrowStabilizerQuotient_comp_arrowStabilizerQuotientInverse,
    Category.assoc, toArrowStabilizerQuotient_comp_source, groupoidInverse_source]

/-- **The pre-relation `j' = (t', s') : R' ⟶ U ×_B U`** of **Stacks 043C** part (1), taken in the
slice of presheaves on the big fppf site over the base, where `R'` is read over the base through
`t'`. -/
noncomputable abbrev arrowStabilizerQuotientPreRelation
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Space.PreRelation
      (Over.mk (arrowStabilizerQuotientTarget G ≫ G.objectsToBase.hom))
      (Over.mk G.objectsToBase.hom) :=
  prod.lift (Over.homMk (arrowStabilizerQuotientTarget G) rfl)
    (Over.homMk (arrowStabilizerQuotientSource G)
      (arrowStabilizerQuotientSource_comp_objectsToBase G))

/-- **Stacks 043C part (2) for `R/S`: `j' = (t', s')` is a monomorphism.** This is the step of
the proof of **Stacks 06QJ**, the implication (2) `⟹` (1), which makes the quotient `R' = R/S` of
the arrow space by the stabilizer action a relation on the object space; with the
pre-equivalence-relation clause of **Stacks 043X** it is an equivalence relation.

Two sections of `R'` over a test object with the same source and the same target lift, after an
fppf covering, to arrows of `R` with the same source and the same target, and two such arrows lie
in a single orbit of the stabilizer: the loop `c(a, i(b))` at their common target carries one to
the other. So they already agree in `R'`, and `R'` is an fppf sheaf. -/
@[stacks 06QJ "the implication (2) implies (1): j' = (t', s') is a monomorphism",
  sga "3 V 10.4" "partial"]
theorem mono_arrowStabilizerQuotientPreRelation
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Mono (arrowStabilizerQuotientPreRelation G) := by
  refine ⟨fun f g hfg => ?_⟩
  refine Over.OverMorphism.ext
    (eq_of_comp_arrowStabilizerQuotient_endpoints_eq G ?_ ?_)
  · have h := congrArg (fun k => k ≫ prod.snd) hfg
    simp only [Category.assoc, prod.lift_snd] at h
    exact congrArg Over.Hom.left h
  · have h := congrArg (fun k => k ≫ prod.fst) hfg
    simp only [Category.assoc, prod.lift_fst] at h
    exact congrArg Over.Hom.left h

/-- The target of the pre-relation `j'` is the descended target `t'`. -/
theorem arrowStabilizerQuotientPreRelation_target_left
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (arrowStabilizerQuotientPreRelation G).target.left = arrowStabilizerQuotientTarget G :=
  congrArg Over.Hom.left (prod.lift_fst _ _)

/-- The source of the pre-relation `j'` is the descended source `s'`. -/
theorem arrowStabilizerQuotientPreRelation_source_left
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (arrowStabilizerQuotientPreRelation G).source.left = arrowStabilizerQuotientSource G :=
  congrArg Over.Hom.left (prod.lift_snd _ _)

/-- **`π : R ⟶ R' = R/S` is a surjection of fppf sheaves**, so a generalized point of `R'` over an
object of the site lifts to the arrow space after an fppf covering. -/
theorem exists_covering_lift_arrowStabilizerQuotient
    (G : GroupoidInAlgebraicSpaces C S hS B) {T : BigFppfOver C S hS}
    (r : yoneda.obj T ⟶ (arrowStabilizerQuotient G).obj) :
    ∃ W ∈ BigFppfOver.topology C S hS T,
      ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T), W.arrows i →
        ∃ a : yoneda.obj V ⟶ G.arrows.obj,
          a ≫ toArrowStabilizerQuotient G = yoneda.map i ≫ r := by
  classical
  have hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      (toArrowStabilizerQuotient G) := isLocallySurjective_toArrowStabilizerQuotient G
  refine ⟨Presheaf.imageSieve (toArrowStabilizerQuotient G) (yonedaEquiv r),
    Presheaf.imageSieve_mem _ (toArrowStabilizerQuotient G) (yonedaEquiv r),
    fun V i hi => ?_⟩
  refine ⟨yonedaEquiv.symm
    (Presheaf.localPreimage (toArrowStabilizerQuotient G) (yonedaEquiv r) i hi), ?_⟩
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply, Presheaf.app_localPreimage,
    ← yonedaEquiv_naturality]

/-- **Composable sections of `R' = R/S` compose.** Both sections lift to arrows of `R` after an
fppf covering; those arrows compose in the groupoid, and the composites glue back to a section of
`R'` by `exists_hom_arrowStabilizerQuotient_of_locally`. -/
private theorem exists_hom_arrowStabilizerQuotient_comp
    (G : GroupoidInAlgebraicSpaces C S hS B) {T : BigFppfOver C S hS}
    (x y z : yoneda.obj T ⟶ G.objects.obj)
    (r₁ r₂ : yoneda.obj T ⟶ (arrowStabilizerQuotient G).obj)
    (hr₁t : r₁ ≫ arrowStabilizerQuotientTarget G = x)
    (hr₁s : r₁ ≫ arrowStabilizerQuotientSource G = y)
    (hr₂t : r₂ ≫ arrowStabilizerQuotientTarget G = y)
    (hr₂s : r₂ ≫ arrowStabilizerQuotientSource G = z) :
    ∃ w : yoneda.obj T ⟶ (arrowStabilizerQuotient G).obj,
      w ≫ arrowStabilizerQuotientTarget G = x ∧ w ≫ arrowStabilizerQuotientSource G = z := by
  obtain ⟨W₁, hW₁, hl₁⟩ := exists_covering_lift_arrowStabilizerQuotient G r₁
  obtain ⟨W₂, hW₂, hl₂⟩ := exists_covering_lift_arrowStabilizerQuotient G r₂
  have hloc : ∀ ⦃V : BigFppfOver C S hS⦄ (i : V ⟶ T), (W₁ ⊓ W₂).arrows i →
      ∃ zz : yoneda.obj V ⟶ (arrowStabilizerQuotient G).obj,
        zz ≫ arrowStabilizerQuotientTarget G = yoneda.map i ≫ x ∧
        zz ≫ arrowStabilizerQuotientSource G = yoneda.map i ≫ z := by
    intro V i hi
    obtain ⟨a₁, ha₁⟩ := hl₁ i hi.1
    obtain ⟨a₂, ha₂⟩ := hl₂ i hi.2
    have e₁t : a₁ ≫ G.target.hom = yoneda.map i ≫ x := by
      rw [← toArrowStabilizerQuotient_comp_target, ← Category.assoc, ha₁, Category.assoc,
        hr₁t]
    have e₁s : a₁ ≫ G.source.hom = yoneda.map i ≫ y := by
      rw [← toArrowStabilizerQuotient_comp_source, ← Category.assoc, ha₁, Category.assoc,
        hr₁s]
    have e₂t : a₂ ≫ G.target.hom = yoneda.map i ≫ y := by
      rw [← toArrowStabilizerQuotient_comp_target, ← Category.assoc, ha₂, Category.assoc,
        hr₂t]
    have e₂s : a₂ ≫ G.source.hom = yoneda.map i ≫ z := by
      rw [← toArrowStabilizerQuotient_comp_source, ← Category.assoc, ha₂, Category.assoc,
        hr₂s]
    refine ⟨groupoidCompose G a₁ a₂ (e₁s.trans e₂t.symm) ≫ toArrowStabilizerQuotient G,
      ?_, ?_⟩
    · rw [Category.assoc, toArrowStabilizerQuotient_comp_target, groupoidCompose_target]
      exact e₁t
    · rw [Category.assoc, toArrowStabilizerQuotient_comp_source, groupoidCompose_source]
      exact e₂s
  exact exists_hom_arrowStabilizerQuotient_of_locally G x z
    ((BigFppfOver.topology C S hS).intersection_covering hW₁ hW₂) hloc

/-- **Stacks 043C part (3) for `R' = R/S`: the pre-relation `j' = (t', s')` is a pre-equivalence
relation.** On the points of every test object over the base, the relation `R'` cuts out is
reflexive, symmetric and transitive.

Reflexivity and symmetry are global: the unit of the groupoid composed with `π` is a section of
both `t'` and `s'`, and the inverse of the groupoid descends to the morphism
`arrowStabilizerQuotientInverse` of `R'`, which exchanges them. Transitivity is the one local
step: the two given points of `R'` lift to arrows of `R` after an fppf covering, those arrows
compose, and the composites glue back to a point of `R'` by
`exists_hom_arrowStabilizerQuotient_of_locally`. -/
theorem isPreEquivalenceRelation_arrowStabilizerQuotientPreRelation
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Space.IsPreEquivalenceRelation (arrowStabilizerQuotientPreRelation G) := by
  intro T b
  have htgt := arrowStabilizerQuotientPreRelation_target_left G
  have hsrc := arrowStabilizerQuotientPreRelation_source_left G
  refine ⟨fun x => ?_, fun {x y} hxy => ?_, fun {x y z} hxy hyz => ?_⟩
  · -- Reflexivity: the unit arrow of the groupoid.
    have h1 : ((identityArrow G).hom ≫ toArrowStabilizerQuotient G) ≫
        arrowStabilizerQuotientTarget G = 𝟙 G.objects.obj := by
      rw [Category.assoc, toArrowStabilizerQuotient_comp_target, identityArrow_hom_comp_target]
    have h2 : ((identityArrow G).hom ≫ toArrowStabilizerQuotient G) ≫
        arrowStabilizerQuotientSource G = 𝟙 G.objects.obj := by
      rw [Category.assoc, toArrowStabilizerQuotient_comp_source, identityArrow_hom_comp_source]
    refine ⟨⟨x.1 ≫ (identityArrow G).hom ≫ toArrowStabilizerQuotient G, ?_⟩, ?_, ?_⟩
    · show x.1 ≫ ((identityArrow G).hom ≫ toArrowStabilizerQuotient G) ≫
        arrowStabilizerQuotientTarget G ≫ G.objectsToBase.hom = b
      rw [← Category.assoc ((identityArrow G).hom ≫ toArrowStabilizerQuotient G), h1,
        Category.id_comp]
      exact x.2
    · show x.1 ≫ ((identityArrow G).hom ≫ toArrowStabilizerQuotient G) ≫
        (arrowStabilizerQuotientPreRelation G).target.left = x.1
      rw [htgt, h1]
      exact Category.comp_id _
    · show x.1 ≫ ((identityArrow G).hom ≫ toArrowStabilizerQuotient G) ≫
        (arrowStabilizerQuotientPreRelation G).source.left = x.1
      rw [hsrc, h2]
      exact Category.comp_id _
  · -- Symmetry: the descended inverse.
    obtain ⟨r, hrt, hrs⟩ := hxy
    rw [htgt] at hrt
    rw [hsrc] at hrs
    refine ⟨⟨r.1 ≫ (arrowStabilizerQuotientInverse G).hom, ?_⟩, ?_, ?_⟩
    · show (r.1 ≫ (arrowStabilizerQuotientInverse G).hom) ≫
        arrowStabilizerQuotientTarget G ≫ G.objectsToBase.hom = b
      rw [Category.assoc, ← Category.assoc ((arrowStabilizerQuotientInverse G).hom),
        arrowStabilizerQuotientInverse_comp_target, ← Category.assoc, hrs]
      exact y.2
    · show (r.1 ≫ (arrowStabilizerQuotientInverse G).hom) ≫
        (arrowStabilizerQuotientPreRelation G).target.left = y.1
      rw [htgt, Category.assoc, arrowStabilizerQuotientInverse_comp_target, hrs]
    · show (r.1 ≫ (arrowStabilizerQuotientInverse G).hom) ≫
        (arrowStabilizerQuotientPreRelation G).source.left = x.1
      rw [hsrc, Category.assoc, arrowStabilizerQuotientInverse_comp_source, hrt]
  · -- Transitivity: lift both points to the arrow space, compose, and glue.
    obtain ⟨r₁, hr₁t, hr₁s⟩ := hxy
    obtain ⟨r₂, hr₂t, hr₂s⟩ := hyz
    rw [htgt] at hr₁t hr₂t
    rw [hsrc] at hr₁s hr₂s
    obtain ⟨w, hwt, hws⟩ := exists_hom_arrowStabilizerQuotient_comp G x.1 y.1 z.1 r₁.1 r₂.1
      hr₁t hr₁s hr₂t hr₂s
    refine ⟨⟨w, ?_⟩, ?_, ?_⟩
    · show w ≫ arrowStabilizerQuotientTarget G ≫ G.objectsToBase.hom = b
      rw [← Category.assoc, hwt]
      exact x.2
    · show w ≫ (arrowStabilizerQuotientPreRelation G).target.left = x.1
      rwa [htgt]
    · show w ≫ (arrowStabilizerQuotientPreRelation G).source.left = z.1
      rwa [hsrc]

/-- **The quotient `R' = R/S` of the arrow space by the stabilizer action is an equivalence
relation on the object space** — **Stacks 043C** part (4). This is the step of the proof of
**Stacks 06QJ**, the implication (2) `⟹` (1), after which the quotient `X = U/R'` is an algebraic
space by **Stacks 04S6**.

By `AlgebraicGeometry.Space.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation` an
equivalence relation is exactly a monomorphic pre-equivalence relation, and the two halves are
`mono_arrowStabilizerQuotientPreRelation` and
`isPreEquivalenceRelation_arrowStabilizerQuotientPreRelation`. Nothing is assumed. -/
@[stacks 06QJ "the implication (2) implies (1): j' = (t', s') is an equivalence relation"]
theorem isEquivalenceRelation_arrowStabilizerQuotientPreRelation
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    CategoryTheory.IsEquivalenceRelation
      (arrowStabilizerQuotientPreRelation G).target
      (arrowStabilizerQuotientPreRelation G).source :=
  (Space.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation
    (arrowStabilizerQuotientPreRelation G)).2
    ⟨mono_arrowStabilizerQuotientPreRelation G,
      isPreEquivalenceRelation_arrowStabilizerQuotientPreRelation G⟩

end Quotient

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
