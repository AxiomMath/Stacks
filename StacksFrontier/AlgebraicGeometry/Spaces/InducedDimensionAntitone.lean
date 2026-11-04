module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.Catenary
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Catenary
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FibrePointsSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionFunction
public import StacksFrontier.Topology.Dimension.DimensionFunctionDifference

/-!
# Strict antitonicity of the induced dimension function on an algebraic space

Let `Y` be a decent, locally Noetherian, universally catenary algebraic space over `S` carrying a
dimension function `δ` on its points, and let `f : X ⟶ Y` be locally of finite type with `X` a
decent algebraic space.  Stacks 0EDN attaches to a point `x` of `X` the integer
`δ (f x) + trdeg κ(f x) κ(x)`, the value `AlgebraicGeometry.Space.inducedDimensionValue`.  This
file proves that this function drops strictly along every nontrivial specialization of points
of `X`: if `x ⤳ y` and `x ≠ y` then its value at `y` is strictly smaller than its value at `x`.

That is the antitonicity half of the assertion of Stacks 0EDN that the induced function is again
a dimension function.  Along the way the file compares the two notions of universal catenarity:
a universally catenary algebraic space in the sense of Stacks 0ED7 has every locally Noetherian
étale chart universally catenary as a scheme, in the sense of Stacks 02J8.

## Main results

* `TopologicalSpace.DimensionFunction.sub_le_sub_of_lt_of_specializes`: a function that is
  antitone along specializations and strictly antitone along nontrivial ones drops at least as
  much as any dimension function along a specialization.
* `AlgebraicGeometry.Space.isUniversallyCatenary_chart_of_isUniversallyCatenary`: a locally
  Noetherian étale chart of a universally catenary algebraic space is a universally catenary
  scheme.
* `AlgebraicGeometry.Space.lt_inducedDimensionValue_of_specializes_of_chart`: strict antitonicity
  of the induced function, given a surjective étale chart of the target that is locally
  Noetherian and universally catenary.
* `AlgebraicGeometry.Space.lt_inducedDimensionValue_of_specializes`: strict antitonicity of the
  induced function.

## Implementation notes

The route is the source's, read on a chart.  A surjective étale chart `φ : h_V ⟶ Y` of the target
is lifted to a chart `ψ : h_W ⟶ X` of the source together with a morphism `α : W ⟶ V` of the site
over it, by
`AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift`; the induced value at a point
of `X` coming from `w ∈ W` is then the value of `δ` at the image of `w` in `V` plus the
transcendence degree of the morphism of schemes `q` underlying `α` at `w`.  The specialization is
lifted to `W` because the map on points of an étale chart of a decent space is generalizing
(`AlgebraicGeometry.Space.generalizingMap_pointsMap_of_isDecentSpace`).

Downstairs on `V` the function pulled back from `δ` is not known to be a dimension function, only
to be strictly antitone: Stacks 03K5
(`AlgebraicGeometry.Space.eq_of_specializes_of_pointsMap_eq_of_isDecentSpace`) keeps the two
images of a nontrivial specialization distinct because `Y` is decent.  An honest dimension
function is obtained instead on a neighbourhood of the image point, from catenarity of the chart
by Stacks 02IY (`AlgebraicGeometry.isCatenarySpace_iff_locally_dimensionFunction`), and Stacks 02JW
(`Stacks.Chow.relativeDimension_isDimensionFunction`) turns it into a dimension function on the
preimage of that neighbourhood under the restricted morphism `q ∣_ O`.  Comparing the strict drop
of the latter with the drop of the pulled-back function, by
`TopologicalSpace.DimensionFunction.sub_le_sub_of_lt_of_specializes`, gives the result; the
transcendence-degree terms match because the residue-field maps of the two open immersions
involved are isomorphisms.

## What is not done

The **packaged** form of the dimension-function clause of Stacks 0EDN — the statement
`∃ d : DimensionFunction (points B S hS X), ∀ x, d x = inducedDimensionValue B S hS δ f x` — is
**not** proved here, and **no `@[stacks 0EDN]` attribute is attached to anything in this file**.
Only the antitonicity half is proved.  A dimension function must in addition satisfy
`TopologicalSpace.DimensionFunction.step_immediate`, that the value drop across an *immediate*
specialization is exactly one, and for the composite `δ ∘ |φ|` of `δ` with the map on points of a
chart that does not follow from the properties established here: continuity, openness,
generalizingness and non-collapse of nontrivial specializations are all consistent with a drop
larger than one across an immediate specialization, since an immediate specialization upstairs
need not be immediate downstairs.  Proving it needs Stacks 0EDM together with a finite surjection
from a scheme and the catenarity of the source, none of which this repository has.

## References

* [Stacks Project, Tag 02I2](https://stacks.math.columbia.edu/tag/02I2)
* [Stacks Project, Tag 02IY](https://stacks.math.columbia.edu/tag/02IY)
* [Stacks Project, Tag 02J8](https://stacks.math.columbia.edu/tag/02J8)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 03K5](https://stacks.math.columbia.edu/tag/03K5)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
* [Stacks Project, Tag 0ED7](https://stacks.math.columbia.edu/tag/0ED7)
* [Stacks Project, Tag 0EDM](https://stacks.math.columbia.edu/tag/0EDM)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace TopologicalSpace

/-- A function which drops along every specialization, and strictly along every nontrivial
one, drops at least as much as any dimension function. -/
theorem DimensionFunction.sub_le_sub_of_lt_of_specializes {A : Type*}
    [TopologicalSpace A] (d : DimensionFunction A) (e : A → ℤ)
    (hmono : ∀ ⦃a b : A⦄, a ⤳ b → e b ≤ e a)
    (hstrict : ∀ ⦃a b : A⦄, a ⤳ b → a ≠ b → e b < e a)
    {a b : A} (hab : a ⤳ b) : d a - d b ≤ e a - e b := by
  suffices h : ∀ n : ℕ, ∀ p q : A, p ⤳ q → (d p - d q).toNat ≤ n → d p - d q ≤ e p - e q from
    h (d a - d b).toNat a b hab le_rfl
  intro n
  induction n with
  | zero =>
    intro p q hpq hle
    have := hmono hpq
    omega
  | succ k ih =>
    intro p q hpq hle
    by_cases hne : p = q
    · subst hne
      omega
    obtain ⟨z, himm, hzq⟩ := d.exists_isImmediateSpecialization hpq hne
    have hdz : d p = d z + 1 := d.step_immediate himm
    have hdzq : d q ≤ d z := by
      by_cases h : z = q
      · subst h
        omega
      · linarith [d.strictAnti_specializes hzq h]
    have hpz : p ≠ z := by
      rintro rfl
      omega
    linarith [ih z q hzq (by omega), hstrict himm.1 hpz]

end TopologicalSpace

/-- Along a surjective generalizing map, a nontrivial specialization lifts to a nontrivial
specialization. -/
theorem GeneralizingMap.exists_specializes_lift {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {g : A → B} (hg : GeneralizingMap g) (hs : Function.Surjective g)
    {x y : B} (hxy : x ⤳ y) (hne : x ≠ y) :
    ∃ w' w, w' ⤳ w ∧ w' ≠ w ∧ g w' = x ∧ g w = y := by
  obtain ⟨w, hw⟩ := hs y
  obtain ⟨w', hw'w, hw'⟩ := hg (show x ⤳ g w by rwa [hw])
  exact ⟨w', w, hw'w, fun h => hne (by rw [← hw', h, hw]), hw', hw⟩

namespace AlgebraicGeometry

/-- The transcendence degree of the residue-field extension of a morphism of schemes at a
point of its source, as an extended natural number. -/
private def schemeTrdegE {W V : Scheme.{u}} (q : W ⟶ V) (w : W) : ℕ∞ :=
  letI := (q.residueFieldMap w).hom.toAlgebra
  Cardinal.toENat (Algebra.trdeg (V.residueField (q w)) (W.residueField w))

/-- The transcendence degree of the residue-field extension of a morphism of schemes at a
point of its source, as a natural number. -/
private def schemeTrdeg {W V : Scheme.{u}} (q : W ⟶ V) (w : W) : ℕ :=
  (schemeTrdegE q w).toNat

/-- The relative dimension of Stacks 02JW at a point is the value of the base dimension function
at the image plus the transcendence degree of the residue-field extension there. -/
private theorem relativeDimension_eq_add_schemeTrdeg {W V : Scheme.{u}}
    (δ : DimensionFunction V) (q : W ⟶ V) (w : W) :
    Stacks.Chow.relativeDimension δ q w = δ (q w) + (schemeTrdeg q w : ℤ) := by
  simp only [Stacks.Chow.relativeDimension, schemeTrdeg, schemeTrdegE, Cardinal.toNat_toENat]

/-- The transcendence degree of a morphism of schemes at a point only depends on the residue-field
extension up to compatible isomorphisms of the two fields. -/
private theorem schemeTrdeg_eq_of_ringEquiv {W V W' V' : Scheme.{u}} (q : W ⟶ V) (q' : W' ⟶ V')
    (w : W) (w' : W') (eK : V.residueField (q w) ≃+* V'.residueField (q' w'))
    (eL : W.residueField w ≃+* W'.residueField w')
    (h : ∀ a, eL ((q.residueFieldMap w).hom a) = (q'.residueFieldMap w').hom (eK a)) :
    schemeTrdeg q w = schemeTrdeg q' w' := by
  let _ := (q.residueFieldMap w).hom.toAlgebra
  let _ := (q'.residueFieldMap w').hom.toAlgebra
  simp only [schemeTrdeg, schemeTrdegE]
  exact congrArg (fun c => (Cardinal.toENat c).toNat) (Algebra.trdeg_eq_of_ringEquiv eK eL h)

/-- Postcomposing with a morphism whose residue-field map at the image point is invertible —
for instance an open immersion — does not change the transcendence degree. -/
private theorem schemeTrdeg_comp_right {W V₀ V : Scheme.{u}} (g : W ⟶ V₀) (j : V₀ ⟶ V)
    (w : W) (hj : IsIso (j.residueFieldMap (g w))) :
    schemeTrdeg (g ≫ j) w = schemeTrdeg g w :=
  schemeTrdeg_eq_of_ringEquiv _ _ w w (asIso (j.residueFieldMap (g w))).commRingCatIsoToRingEquiv
    (RingEquiv.refl _) fun a => by
    simp only [Scheme.residueFieldMap_comp]
    rfl

/-- Precomposing with a morphism whose residue-field map is invertible — for instance an open
immersion — reads the transcendence degree at the image point. -/
private theorem schemeTrdeg_comp_left {W₀ W V : Scheme.{u}} (i : W₀ ⟶ W) (q : W ⟶ V)
    (u : W₀) (hi : IsIso (i.residueFieldMap u)) :
    schemeTrdeg (i ≫ q) u = schemeTrdeg q (i u) :=
  schemeTrdeg_eq_of_ringEquiv _ _ u (i u) (RingEquiv.refl _)
    (asIso (i.residueFieldMap u)).commRingCatIsoToRingEquiv.symm fun a => by
    simp only [Scheme.residueFieldMap_comp]
    exact RingEquiv.symm_apply_apply _ _

/-- Restricting a morphism of schemes to the preimage of an open does not change the
transcendence degree. -/
private theorem schemeTrdeg_morphismRestrict {W V : Scheme.{u}} (q : W ⟶ V) (O : V.Opens)
    (z : (q ⁻¹ᵁ O).toScheme) : schemeTrdeg (q ∣_ O) z = schemeTrdeg q ((q ⁻¹ᵁ O).ι z) := by
  rw [← schemeTrdeg_comp_right (q ∣_ O) O.ι z inferInstance,
    morphismRestrict_ι q O,
    schemeTrdeg_comp_left (q ⁻¹ᵁ O).ι q z inferInstance]

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The value at a point of a scheme chart of a function on the points of an algebraic
space. -/
private def chartValue {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (δ : points B S hS Y → ℤ)
    {V : BigFppfOver B S hS} (φ : yoneda.obj V ⟶ Y)
    (v : (BigFppfOver.toScheme B S hS).obj V) : ℤ :=
  δ (pointsMap B S hS (yoneda.obj V) φ ((pointsEquivScheme B S hS V).symm v))

/-- The map from the points of a scheme chart to the points of the algebraic space it charts is
continuous: it is the map on points of the chart read through the canonical homeomorphism. -/
private theorem continuous_chartMap {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V : BigFppfOver B S hS} (φ : yoneda.obj V ⟶ Y) :
    Continuous (fun v : (BigFppfOver.toScheme B S hS).obj V =>
      pointsMap B S hS (yoneda.obj V) φ ((pointsEquivScheme B S hS V).symm v)) :=
  (continuous_pointsMap B S hS φ).comp (schemePointsHomeomorph B S hS V).symm.continuous

/-- A dimension function on the points of a decent algebraic space pulls back to a strictly
antitone function along an étale scheme chart: Stacks 03K5 keeps the two image points
distinct. -/
private theorem chartValue_lt_of_specializes {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y)
    (δ : DimensionFunction (points B S hS Y)) {V : BigFppfOver B S hS}
    (φ : yoneda.obj V ⟶ Y) (hφ : IsEtale B S hS φ)
    {v v' : (BigFppfOver.toScheme B S hS).obj V} (hvv' : v ⤳ v') (hne : v ≠ v') :
    chartValue B S hS δ φ v' < chartValue B S hS δ φ v :=
  δ.strictAnti_specializes (hvv'.map (continuous_chartMap B S hS φ)) fun heq =>
    hne (eq_of_specializes_of_pointsMap_eq_of_isDecentSpace B S hS hY hYdec V φ hφ v' v
      heq.symm hvv').symm

/-- A dimension function on the points of a decent algebraic space pulls back to an antitone
function along an étale scheme chart. -/
private theorem chartValue_le_of_specializes {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y)
    (δ : DimensionFunction (points B S hS Y)) {V : BigFppfOver B S hS}
    (φ : yoneda.obj V ⟶ Y) (hφ : IsEtale B S hS φ)
    {v v' : (BigFppfOver.toScheme B S hS).obj V} (hvv' : v ⤳ v') :
    chartValue B S hS δ φ v' ≤ chartValue B S hS δ φ v := by
  by_cases h : v = v'
  · rw [h]
  · exact (chartValue_lt_of_specializes B S hS hY hYdec δ φ hφ hvv' h).le

/-- On an open `O` of an étale chart of a decent space, the function pulled back from a
dimension function drops at least as much as any dimension function on `O`. -/
private theorem sub_le_chartValue_sub_of_specializes {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y)
    (δ : DimensionFunction (points B S hS Y)) {V : BigFppfOver B S hS}
    (φ : yoneda.obj V ⟶ Y) (hφ : IsEtale B S hS φ)
    (O : ((BigFppfOver.toScheme B S hS).obj V).Opens) (δ₀ : DimensionFunction O.toScheme)
    {o o' : O.toScheme} (h : o' ⤳ o) :
    δ₀ o' - δ₀ o ≤ chartValue B S hS δ φ (O.ι o') - chartValue B S hS δ φ (O.ι o) :=
  δ₀.sub_le_sub_of_lt_of_specializes (fun o => chartValue B S hS δ φ (O.ι o))
    (fun _ _ hoo' => chartValue_le_of_specializes B S hS hY hYdec δ φ hφ
      (hoo'.map O.ι.continuous))
    (fun _ _ hoo' hne => chartValue_lt_of_specializes B S hS hY hYdec δ φ hφ
      (hoo'.map O.ι.continuous) fun h => hne (O.ι.isOpenEmbedding.injective h)) h

/-- The induced value at a point of an étale chart of the source is the value at its image in
an étale chart of the target plus the transcendence degree of the chart morphism there. -/
private theorem inducedDimensionValue_pointsMap_eq {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (δ : DimensionFunction (points B S hS Y))
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) {W V : BigFppfOver B S hS}
    (ψ : yoneda.obj W ⟶ X) (φ : yoneda.obj V ⟶ Y) (α : W ⟶ V)
    (hψetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ)
    (hφetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (hcomm : ψ ≫ f = yoneda.map α ≫ φ) (w : (BigFppfOver.toScheme B S hS).obj W) :
    inducedDimensionValue B S hS δ f
        (pointsMap B S hS (yoneda.obj W) ψ ((pointsEquivScheme B S hS W).symm w)) =
      chartValue B S hS δ φ ((BigFppfOver.toScheme B S hS).map α w) +
        (schemeTrdeg ((BigFppfOver.toScheme B S hS).map α) w : ℤ) := by
  have hr := (hasTranscendenceDegreeAt_pointsMap_iff B S hS
    (schemeTrdegE ((BigFppfOver.toScheme B S hS).map α) w) f W V ψ φ α
    hψetale hφetale hcomm.symm w).mpr rfl
  have hpt : (pointsEquivScheme B S hS V).symm ((BigFppfOver.toScheme B S hS).map α w) =
      pointsMap B S hS (yoneda.obj W) (yoneda.map α) ((pointsEquivScheme B S hS W).symm w) := by
    refine (pointsEquivScheme B S hS V).symm_apply_eq.2 ?_
    rw [pointsEquivScheme_pointsMap_yoneda, Equiv.apply_symm_apply]
  have himg : pointsMap B S hS X f
      (pointsMap B S hS (yoneda.obj W) ψ ((pointsEquivScheme B S hS W).symm w)) =
        pointsMap B S hS (yoneda.obj V) φ
          ((pointsEquivScheme B S hS V).symm ((BigFppfOver.toScheme B S hS).map α w)) := by
    rw [hpt, ← pointsMap_comp_apply, ← pointsMap_comp_apply, hcomm]
  rw [inducedDimensionValue_eq B S hS hX hY δ f hf _ _ hr, himg]
  simp only [chartValue, schemeTrdeg]

/-! ### From the space notion of universal catenarity to the scheme notion on a chart -/

/-- An affine open of a scheme locally of finite type over the scheme of an object of the big
fppf site of `S` satisfies the site's size cutoff: it is quasi-compact, so Stacks 04T7 bounds
its size by that of the object. -/
private theorem contains_coe_affineOpens {V : BigFppfOver B S hS} {Z : Scheme.{u}}
    (z : Z ⟶ (BigFppfOver.toScheme B S hS).obj V) [LocallyOfFiniteType z]
    (W : Z.affineOpens) : B.Contains (W.1 : Scheme.{u}) :=
  have : IsAffine (W.1 : Scheme.{u}) := W.2
  (Scheme.size_le_of_locallyOfFiniteType (W.1.ι ≫ z)).trans_lt V.left.property

/-- An affine open of a scheme locally of finite type over the scheme of an object `V` of the
big fppf site of `S`, regarded again as an object of that site over `V`. -/
private noncomputable def affineOpensObj {V : BigFppfOver B S hS} {Z : Scheme.{u}}
    (z : Z ⟶ (BigFppfOver.toScheme B S hS).obj V) [LocallyOfFiniteType z]
    (W : Z.affineOpens) : BigFppfOver B S hS :=
  Over.mk (⟨(W.1.ι ≫ z) ≫ V.hom.hom⟩ :
    B.obj (contains_coe_affineOpens B S hS z W) ⟶ B.obj hS)

/-- The canonical morphism of the site from an affine open of `Z` to `V`. -/
private noncomputable def affineOpensHom {V : BigFppfOver B S hS} {Z : Scheme.{u}}
    (z : Z ⟶ (BigFppfOver.toScheme B S hS).obj V) [LocallyOfFiniteType z]
    (W : Z.affineOpens) : affineOpensObj B S hS z W ⟶ V :=
  Over.homMk ⟨W.1.ι ≫ z⟩ rfl

/-- `AlgebraicGeometry.Space.affineOpensHom` is locally of finite type: the morphism of
schemes underlying it is the inclusion of the affine open followed by the given morphism, and
being locally of finite type is étale local on the source and target. -/
private theorem isLocallyOfFiniteType_yoneda_map_affineOpensHom {V : BigFppfOver B S hS}
    {Z : Scheme.{u}} (z : Z ⟶ (BigFppfOver.toScheme B S hS).obj V) [LocallyOfFiniteType z]
    (W : Z.affineOpens) :
    IsLocallyOfFiniteType B S hS (yoneda.map (affineOpensHom B S hS z W)) :=
  (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget (affineOpensHom B S hS z W)).mpr
    (show LocallyOfFiniteType (W.1.ι ≫ z) from inferInstance)

/-- **The scheme notion of universal catenarity on an étale chart.** Let `Y` be a universally
catenary algebraic space over `S` in the sense of Stacks 0ED7 and let `φ : h_V ⟶ Y` be an
étale chart of it whose scheme is locally Noetherian. Then that scheme is universally
catenary in the scheme sense of Stacks 02J8.

The two notions differ only in the range of their quantifier: Stacks 0ED7 quantifies over
algebraic spaces over `S`, hence over schemes meeting the site's size cutoff, whereas
Stacks 02J8 quantifies over every scheme locally of finite type over the chart. The gap is
bookkeeping, because catenarity is Zariski-local (Stacks 02I2): a scheme `Z` locally of
finite type over the chart is covered by its affine opens, each of which is quasi-compact and
therefore meets the cutoff by Stacks 04T7, hence is an object of the site; it is locally of
finite type over `Y`, being so over the chart and the chart being étale over `Y`
(Stacks 06LT, Stacks 03XG), and it is decent because it is representable. So the space notion
makes each member of the covering catenary, and locality finishes. -/
theorem isUniversallyCatenary_chart_of_isUniversallyCatenary
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYcat : IsUniversallyCatenary B S hS Y) (V : BigFppfOver B S hS)
    (φ : yoneda.obj V ⟶ Y) (hφ : IsEtale B S hS φ)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] :
    Scheme.IsUniversallyCatenary ((BigFppfOver.toScheme B S hS).obj V) := by
  intro Z z hz
  refine (CatenaryTopologicalSpace.isCatenary_iff_hasOpenCoveringByCatenarySpaces Z).mpr
    ⟨Z.affineOpens, fun W => (W.1 : Set Z), fun W => W.1.isOpen, ?_, fun W => ?_⟩
  · exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr
      (TopologicalSpace.Opens.mem_iSup.mp ((iSup_affineOpens_eq_top Z).ge (Set.mem_univ x)))
  · -- The affine open, as an object of the site, is locally of finite type over `Y`.
    have hlft : IsLocallyOfFiniteType B S hS
        (yoneda.map (affineOpensHom B S hS z W) ≫ φ) :=
      isLocallyOfFiniteType_comp B S hS
        (isAlgebraicSpace_yoneda B S hS (affineOpensObj B S hS z W))
        (isAlgebraicSpace_yoneda B S hS V) hY _ φ
        (isLocallyOfFiniteType_yoneda_map_affineOpensHom B S hS z W)
        (isLocallyOfFiniteType_of_isEtale B S hS hY hφ)
    -- Universal catenarity of `Y` therefore makes it catenary.
    have hcat : IrreducibleClosedsCodim.IsCatenarySpace (W.1 : Scheme.{u}) :=
      CatenaryTopologicalSpace.isCatenary_of_homeomorph
        (schemePointsHomeomorph B S hS (affineOpensObj B S hS z W))
        (hYcat (yoneda.obj (affineOpensObj B S hS z W))
          (isAlgebraicSpace_yoneda B S hS _) (isDecentSpace_yoneda B S hS _) _ hlft)
    exact CatenaryTopologicalSpace.isCatenary_of_homeomorph
      (W.1.ι.isOpenEmbedding.isEmbedding.toHomeomorph.trans
        (Homeomorph.setCongr (Scheme.Opens.range_ι (U := W.1)))) hcat

/-- On an étale chart of a decent space that is locally Noetherian and universally catenary,
the value of the pulled-back function plus the transcendence degree of a morphism locally of
finite type into the chart drops strictly along a nontrivial specialization. -/
private theorem chartValue_add_schemeTrdeg_lt_of_specializes
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y)
    (δ : DimensionFunction (points B S hS Y)) {V : BigFppfOver B S hS}
    (φ : yoneda.obj V ⟶ Y) (hφ : IsEtale B S hS φ)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    (hVcat : Scheme.IsUniversallyCatenary ((BigFppfOver.toScheme B S hS).obj V))
    {W : Scheme.{u}} (q : W ⟶ (BigFppfOver.toScheme B S hS).obj V) [LocallyOfFiniteType q]
    {w w' : W} (hw'w : w' ⤳ w) (hwne : w' ≠ w) :
    chartValue B S hS δ φ (q w) + (schemeTrdeg q w : ℤ) <
      chartValue B S hS δ φ (q w') + (schemeTrdeg q w' : ℤ) := by
  -- An open neighbourhood of the image point carrying a dimension function.
  obtain ⟨O₀, hO₀open, hO₀mem, ⟨δ₀⟩⟩ :=
    (isCatenarySpace_iff_locally_dimensionFunction ((BigFppfOver.toScheme B S hS).obj V)).mp
      (hVcat.isCatenarySpace (𝟙 _)) (q w)
  let O : ((BigFppfOver.toScheme B S hS).obj V).Opens := ⟨O₀, hO₀open⟩
  have δ₀' : DimensionFunction O.toScheme := δ₀
  let u : (q ⁻¹ᵁ O).toScheme := ⟨w, hO₀mem⟩
  let u' : (q ⁻¹ᵁ O).toScheme := ⟨w', (hw'w.map q.continuous).mem_open hO₀open hO₀mem⟩
  have hiu : (q ⁻¹ᵁ O).ι u = w := rfl
  have hiu' : (q ⁻¹ᵁ O).ι u' = w' := rfl
  -- The dimension function of Stacks 02JW on the preimage of that neighbourhood.
  obtain ⟨d₀, hd₀⟩ := Stacks.Chow.relativeDimension_isDimensionFunction
    (fun Z z _ => hVcat Z (z ≫ O.ι)) δ₀' (q ∣_ O)
  have hrestrict : ∀ z : (q ⁻¹ᵁ O).toScheme,
      O.ι ((q ∣_ O) z) = q ((q ⁻¹ᵁ O).ι z) := fun z =>
    congrArg (fun m : (q ⁻¹ᵁ O).toScheme ⟶ (BigFppfOver.toScheme B S hS).obj V => m z)
      (morphismRestrict_ι q O)
  have hd₀value : ∀ z : (q ⁻¹ᵁ O).toScheme,
      d₀ z = δ₀' ((q ∣_ O) z) + (schemeTrdeg q ((q ⁻¹ᵁ O).ι z) : ℤ) := fun z => by
    rw [hd₀ z, relativeDimension_eq_add_schemeTrdeg δ₀' (q ∣_ O) z, schemeTrdeg_morphismRestrict]
  -- The specialization upstairs, and the strict drop of the dimension function there.
  have hspecsub : u' ⤳ u :=
    ((q ⁻¹ᵁ O).ι.isOpenEmbedding.isInducing.specializes_iff (x := u') (y := u)).mp
      (by rwa [hiu, hiu'])
  have hd₀lt : d₀ u < d₀ u' :=
    d₀.strictAnti_specializes hspecsub fun h => hwne (by rw [← hiu', ← hiu, h])
  -- The base comparison: the pulled-back dimension function drops at least as much.
  have hbase : δ₀' ((q ∣_ O) u') - δ₀' ((q ∣_ O) u) ≤
      chartValue B S hS δ φ (q w') - chartValue B S hS δ φ (q w) := by
    have hkey := sub_le_chartValue_sub_of_specializes B S hS hY hYdec δ φ hφ O δ₀'
      (hspecsub.map (q ∣_ O).continuous)
    rwa [hrestrict u, hrestrict u', hiu, hiu'] at hkey
  linarith [hiu ▸ hd₀value u, hiu' ▸ hd₀value u']

/-- **The antitonicity clause of Stacks 0EDN, read on a chart.** Let `δ` be a dimension
function on the points of a decent algebraic space `Y`, let `f : X ⟶ Y` be locally of finite
type with `X` a decent algebraic space, and let `φ : h_V ⟶ Y` be a surjective étale chart of
`Y` whose scheme is locally Noetherian and universally catenary. Then the function of
Stacks 0EDN induced by `δ` and `f` drops strictly along every nontrivial specialization. -/
theorem lt_inducedDimensionValue_of_specializes_of_chart
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y)
    (δ : DimensionFunction (points B S hS Y))
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (V : BigFppfOver B S hS) (φ : yoneda.obj V ⟶ Y)
    (hφsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (hφetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    (hVcat : Scheme.IsUniversallyCatenary ((BigFppfOver.toScheme B S hS).obj V))
    ⦃x y : points B S hS X⦄ (hxy : x ⤳ y) (hne : x ≠ y) :
    inducedDimensionValue B S hS δ f y < inducedDimensionValue B S hS δ f x := by
  obtain ⟨W, ψ, α, hcomm, hψsurj, hψetale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V φ hφsurj hφetale
  set T := BigFppfOver.toScheme B S hS
  set q := T.map α
  have hlft : LocallyOfFiniteType q := hf W V ψ φ α hψetale hφetale hcomm.symm
  set g : T.obj W → points B S hS X := fun w =>
    pointsMap B S hS (yoneda.obj W) ψ ((pointsEquivScheme B S hS W).symm w)
  have hgsurj : Function.Surjective g :=
    ((presheafSurjective_iff_isSurjective_yoneda B S hS X hX W ψ).mp hψsurj).comp
      (schemePointsHomeomorph B S hS W).symm.surjective
  have hggen : GeneralizingMap g :=
    (((schemePointsHomeomorph B S hS W).symm.isOpenEmbedding).generalizingMap).comp
      (generalizingMap_pointsMap_of_isDecentSpace B S hS X hX hXdec W ψ hψetale)
  -- The induced value at a point of the chart is the relative dimension of `q` there.
  have hvalue : ∀ w : T.obj W, inducedDimensionValue B S hS δ f (g w) =
      chartValue B S hS δ φ (q w) + (schemeTrdeg q w : ℤ) :=
    inducedDimensionValue_pointsMap_eq B S hS hX hY δ f hf ψ φ α hψetale hφetale hcomm
  obtain ⟨w', w, hw'w, hwne, hw', hw⟩ := hggen.exists_specializes_lift hgsurj hxy hne
  rw [← hw, ← hw', hvalue w, hvalue w']
  exact chartValue_add_schemeTrdeg_lt_of_specializes B S hS hY hYdec δ φ
    (isEtale_of_presheaf_etale B S hS hφetale) hVcat q hw'w hwne

/-- **The antitonicity clause of Stacks 0EDN.** Let `δ` be a dimension function on the points
of a decent, locally Noetherian, universally catenary algebraic space `Y`, and let `f : X ⟶ Y`
be locally of finite type with `X` a decent algebraic space. Then the function of Stacks 0EDN
induced by `δ` and `f` drops strictly along every nontrivial specialization of points
of `X`. -/
theorem lt_inducedDimensionValue_of_specializes
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y)
    (hYnoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hYcat : IsUniversallyCatenary B S hS Y)
    (δ : DimensionFunction (points B S hS Y))
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    ⦃x y : points B S hS X⦄ (hxy : x ⤳ y) (hne : x ≠ y) :
    inducedDimensionValue B S hS δ f y < inducedDimensionValue B S hS δ f x := by
  obtain ⟨V, φ, hφsurj, hφetale⟩ := hY.exists_atlas
  have hnoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    (exists_atlas_iff_forall_etale B S hS Y
      (fun T : Scheme.{u} => IsLocallyNoetherian T) hY).mp hYnoeth V φ hφetale
  exact lt_inducedDimensionValue_of_specializes_of_chart B S hS hX hXdec hY hYdec δ f hf
    V φ hφsurj hφetale
    (isUniversallyCatenary_chart_of_isUniversallyCatenary B S hS hY hYcat V φ
      (isEtale_of_presheaf_etale B S hS hφetale)) hxy hne

end AlgebraicGeometry.Space

end
