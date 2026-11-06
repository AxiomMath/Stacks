module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionChartQuasiFinitePair
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoidStabilizerDimension
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductFibreProductRepresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocal

/-!
# The double fibre of a charted self-intersection at a general quasi-DM stack (Stacks 06MF)

Let `𝒳` be an algebraic stack over `S` which is **quasi-DM over `S`**, let `p : U ⟶ 𝒳` be a
1-morphism out of the algebraic stack represented by a scheme `U` of the site which is locally of
finite type, let `P` be a 2-fibre product square over the cospan `(p, p)` — a model of
`U ×_𝒳 U` — let `F` be a presheaf representing its apex and let `c : h_R ⟶ F` be an étale chart
of `F` by a scheme `R` of the site. Write `a` and `b` for the two legs
`AlgebraicGeometry.Stack.chartLeg` read as morphisms of schemes `R ⟶ U`, and let `r₀` be a point
of `R` whose two images in `U` agree and are a closed point `u`.

Then the **double fibre** — the scheme-theoretic fibre over `a r₀` of
`b.fiber (b r₀) ⟶ R ⟶ U` — is **discrete**, and therefore `r₀` is an isolated point of it and is
closed in its fibre under `b`. Those are the two inputs the slicing step of the chart
construction of **Stacks 06MF** consumes: the `hiso` of
`AlgebraicGeometry.exists_isOpenImmersion_flat_zeroScheme_pullback_of_smooth` and the closedness
the quasi-finiteness conjunct of
`AlgebraicGeometry.exists_mono_flat_surjective_slice_of_smooth` asks for.

This is the transport of
`AlgebraicGeometry.Stack.SelfIntersection.dimension_relation_le_zero` — `dim(u ×_𝒳 u) = 0`, the
first paragraph of the proof of **Stacks 06MF** — to the scheme-theoretic double fibre. The
hypotheses `hq` of
`StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionChartQuasiFinitePair` are **not** assumed:
that file reaches the same two conclusions from local quasi-finiteness of the *pair*
`(a, b) : R ⟶ U ×_{Spec k} U`, over a field-valued point of the base named by a locally
quasi-finite 1-morphism `q : 𝒴₀ ⟶ Spec(k)`. At a general quasi-DM algebraic stack over the
absolute base of **Stacks 050D** part (6) there is no such `q`. The pair over the base *itself*
is locally quasi-finite — that is **Stacks 050H** part (5) at the structure morphism, which
`AlgebraicGeometry.Stack.SelfIntersection.isLocallyQuasiFinite_sourceTarget_pointGroupoid`
records — and it still does not give the conclusion, because the reduction of that file factors
`b.fiber u ⟶ U` through `U ×_T Spec κ(u)`, whose projection to `U` is locally quasi-finite only
when `Spec κ(u) ⟶ T` is: with `T = Spec(k)` that is closedness of `u`, and over the absolute base
it fails. What *is* available is the dimension of the self-intersection of the residue-field
point, and that is what is used here.

## Main results

* `AlgebraicGeometry.Stack.isIsolatedPoint_asFiber_of_discreteTopology` and
  `...isClosed_asFiber_of_discreteTopology`: the two scheme-level consequences of discreteness of
  the double fibre at a point whose two images agree.
* `AlgebraicGeometry.Stack.locallyOfFiniteType_inf_locallyQuasiFinite_sitePullbackSnd`: the
  presheaf-level step — the iterated site pullback `V ×_{b, U} R ×_{a, U} V` is an étale chart of
  the presheaf-level double fibre, so the structure morphism of the former inherits local
  quasi-finiteness from the latter.
* `AlgebraicGeometry.Stack.exists_isPullback_isLocallyQuasiFinite_doubleFibre`: the stack-level
  step — the presheaf-level double fibre `V ×_{h_U} F ×_{h_U} V` of a field-valued point
  `v : V ⟶ U` represents `V ×_𝒳 V`, and its projection to `h_V` is locally quasi-finite.
* `AlgebraicGeometry.Stack.locallyQuasiFinite_doubleFibre_sitePullback` and
  `...discreteTopology_doubleFibre_chartLeg`: the double fibre at the residue field of a closed
  point of `U` is discrete.
* `AlgebraicGeometry.Stack.isIsolatedPoint_asFiber_chartLeg_of_isQuasiDM` and
  `...isClosed_asFiber_chartLeg_of_isQuasiDM`: **the two results** — the isolated-point input and
  the closed-point input of the slicing step of **Stacks 06MF**, at a general quasi-DM algebraic
  stack, with no field-valued point of the base and nothing carried.
* `AlgebraicGeometry.Stack.exists_point_isIsolatedPoint_isClosed_asFiber_chartLeg_of_isQuasiDM`:
  the two of them at the canonical 2-fibre product square and at the identity point of
  **Stacks 04XH** over a closed point of `U`, which is the shape the chart construction of
  **Stacks 06MF** uses them in.

## Implementation notes

The stack-level step is two pastings of 2-fibre products. Writing `𝒱` for the algebraic stack
represented by the site object `V` of the residue-field point and `w` for
`AlgebraicGeometry.Stack.schemeStackMap` of `v`,

* `𝒬 = 𝒱 ×_{w, U, P.snd} P.pt` is a 2-fibre product of `(P.snd, w)`, so
  `CategoryTheory.Bicategory.TwoCommSq.paste` presents `𝒬` as a 2-fibre product over the cospan
  `(p, w ≫ p)`, i.e. as `U ×_𝒳 V`;
* `𝒲 = 𝒱 ×_{w, U, pr ≫ P.fst} 𝒬` is a 2-fibre product of `(w, 𝒬 ⟶ U)`, so
  `CategoryTheory.Bicategory.TwoCommSq.pasteFst` presents `𝒲` as a 2-fibre product over the
  cospan `(w ≫ p, w ≫ p)`, i.e. as `V ×_𝒳 V`.

Each apex is represented by the fibre product of the representing presheaves of its cospan, by
`AlgebraicGeometry.Stack.exists_representation_isPullback_twoFibreProductSquare`, which also
supplies the pullback square of representing maps and the algebraicity of the apex. Comparing
`𝒲` with the *canonical* 2-fibre product of `(w ≫ p, w ≫ p)` — both being 2-fibre products of
one cospan — transports that representation to the canonical apex, which is the form
`AlgebraicGeometry.Stack.SelfIntersection.dimension_relation_le_zero` consumes;
**Stacks 0ACA** (`AlgebraicGeometry.Space.isLocallyQuasiFinite_iff_dimension_le_zero`) then turns
`dim ≤ 0` into local quasi-finiteness of the projection `𝒲 ⟶ h_V`, which is locally of finite
type because it is a base change of `U ×_𝒳 V ⟶ U`, itself a composite of base changes of `v` and
of `p`.

The two étale charts are base changes of `c` — the first along the projection
`V ×_{h_U} F ⟶ F`, the second along `𝒲 ⟶ V ×_{h_U} F` — recognised by
`CategoryTheory.IsPullback.of_bot` against the two pullback squares of representing maps, and
`AlgebraicGeometry.Space.presheaf_of_isPullback` carries the chart property across. The chart
object is the iterated `AlgebraicGeometry.Stack.sitePullbackObj`, whose containment in the site
needs no hypothesis (**Stacks 000R**), and whose underlying scheme is the scheme-theoretic double
fibre **on the nose**: `AlgebraicGeometry.Stack.toScheme_obj_sitePullbackObj`,
`...toScheme_map_sitePullbackFst` and `AlgebraicGeometry.BigFppfOver.siteMapOver` all hold by
`rfl`, and `AlgebraicGeometry.Scheme.Hom.fiber` is by definition the pullback along
`AlgebraicGeometry.Scheme.fromSpecResidueField`. So no comparison isomorphism of schemes is ever
named, and `AlgebraicGeometry.locallyQuasiFinite_iff_discreteTopology_of_subsingleton` reads the
conclusion directly on the double fibre.

That `B.Contains (Spec κ(u))` is not a hypothesis: it is
`AlgebraicGeometry.BigFppfSite.residueField_spec_contains` at the containment witness `U` already
carries.

Several applications pass implicit arguments explicitly — `isLocallyOfFiniteType_representingMap`
and `exists_representation_isPullback_twoFibreProductSquare` take the representing equivalence
*before* the 1-morphism, so leaving the stack implicit asks the unifier to solve
`?𝒳.val.val.p =?= 𝒬.val.val.p` by `whnf` on an iterated 2-fibre product of categories fibred in
groupoids, which exhausts the heartbeat budget. Naming the stack makes the same proof elaborate
in a second.

No `@[stacks]` attribute is claimed: this is a step of the proof of **Stacks 06MF**, whose
registration sits on
`AlgebraicGeometry.Stack.isAbsolutelyQuasiDM_iff_hasQuasiDMPresentation_unconditional`.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The point of the fibre under `b` over `b r₀` determined by `r₀` maps to `b r₀` under the
composite of `fiberι` and `a`, when `a r₀ = b r₀`. -/
private theorem comp_fiberι_asFiber_eq {Rs Us : Scheme.{u}} (a b : Rs ⟶ Us) (r₀ : Rs)
    (hab : a r₀ = b r₀) : (b.fiberι (b r₀) ≫ a) (b.asFiber r₀) = b r₀ := by
  change a (b.fiberι (b r₀) (b.asFiber r₀)) = b r₀
  rw [Scheme.Hom.fiberι_asFiber]
  exact hab

/-- **A point of a relation whose double fibre is discrete is an isolated point of that double
fibre.** -/
theorem isIsolatedPoint_asFiber_of_discreteTopology {Rs Us : Scheme.{u}} (a b : Rs ⟶ Us)
    (r₀ : Rs) (hab : a r₀ = b r₀)
    (hd : DiscreteTopology ((b.fiberι (b r₀) ≫ a).fiber (b r₀))) :
    IsIsolatedPoint ((b.fiberι (b r₀) ≫ a).asFiber (b.asFiber r₀)) := by
  have hpt := comp_fiberι_asFiber_eq a b r₀ hab
  have : DiscreteTopology ((b.fiberι (b r₀) ≫ a).fiber
      ((b.fiberι (b r₀) ≫ a) (b.asFiber r₀))) := by
    rw [hpt]; exact hd
  exact isOpen_discrete _

/-- **A point of a relation whose double fibre is discrete, and whose image under the second leg
is a closed point, is closed in its fibre under that leg.** -/
theorem isClosed_asFiber_of_discreteTopology {Rs Us : Scheme.{u}} (a b : Rs ⟶ Us)
    (r₀ : Rs) (hab : a r₀ = b r₀)
    (hd : DiscreteTopology ((b.fiberι (b r₀) ≫ a).fiber (b r₀)))
    (hclosed : IsClosed ({b r₀} : Set Us)) :
    IsClosed ({b.asFiber r₀} : Set (b.fiber (b r₀))) := by
  have hpt : b.asFiber r₀ ∈ (b.fiberι (b r₀) ≫ a) ⁻¹' ({b r₀} : Set Us) :=
    comp_fiberι_asFiber_eq a b r₀ hab
  have : DiscreteTopology ((b.fiberι (b r₀) ≫ a) ⁻¹' ({b r₀} : Set Us)) :=
    have := hd
    ((b.fiberι (b r₀) ≫ a).fiberHomeo (b r₀)).symm.isEmbedding.discreteTopology
  have hcl : IsClosed ((b.fiberι (b r₀) ≫ a) ⁻¹' ({b r₀} : Set Us)) :=
    hclosed.preimage (b.fiberι (b r₀) ≫ a).continuous
  have himg := hcl.isClosedEmbedding_subtypeVal.isClosedMap
    ({(⟨b.asFiber r₀, hpt⟩ : (b.fiberι (b r₀) ≫ a) ⁻¹' ({b r₀} : Set Us))} :
      Set ((b.fiberι (b r₀) ≫ a) ⁻¹' ({b r₀} : Set Us))) (isClosed_discrete _)
  simpa using himg

/-- **The scheme-theoretic double fibre of a charted relation is an étale chart of the
presheaf-level double fibre.** -/
theorem locallyOfFiniteType_inf_locallyQuasiFinite_sitePullbackSnd
    {Fp Kp Gp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U V R : BigFppfOver B S hS}
    (f₁ f₂ : Fp ⟶ yoneda.obj U) (v : V ⟶ U) (c : yoneda.obj R ⟶ Fp)
    (aleg bleg : R ⟶ U) (hya : yoneda.map aleg = c ≫ f₁) (hyb : yoneda.map bleg = c ≫ f₂)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (pK : Kp ⟶ Fp) (qK : Kp ⟶ yoneda.obj V) (hKpb : IsPullback pK qK f₂ (yoneda.map v))
    (pG : Gp ⟶ yoneda.obj V) (qG : Gp ⟶ Kp)
    (hGpb : IsPullback pG qG (yoneda.map v) (pK ≫ f₁))
    (hGsp : IsAlgebraicSpace B S hS Gp)
    (hpGlqf : Space.IsLocallyQuasiFinite B S hS pG) :
    ((@LocallyOfFiniteType.{u} ⊓ @LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      ((BigFppfOver.toScheme B S hS).map
        (sitePullbackSnd B S hS (sitePullbackFst B S hS bleg v ≫ aleg) v)) := by
  have hWy := yoneda.map_isPullback (isPullback_sitePullback B S hS bleg v)
  rw [hyb] at hWy
  have hcomm₀ : (yoneda.map (sitePullbackFst B S hS bleg v) ≫ c) ≫ f₂ =
      yoneda.map (sitePullbackSnd B S hS bleg v) ≫ yoneda.map v := by
    rw [Category.assoc]; exact hWy.w
  have hκ₀fst := hKpb.lift_fst (yoneda.map (sitePullbackFst B S hS bleg v) ≫ c)
    (yoneda.map (sitePullbackSnd B S hS bleg v)) hcomm₀
  have hκ₀snd := hKpb.lift_snd (yoneda.map (sitePullbackFst B S hS bleg v) ≫ c)
    (yoneda.map (sitePullbackSnd B S hS bleg v)) hcomm₀
  have hκ₀pb : IsPullback (yoneda.map (sitePullbackFst B S hS bleg v))
      (hKpb.lift (yoneda.map (sitePullbackFst B S hS bleg v) ≫ c)
        (yoneda.map (sitePullbackSnd B S hS bleg v)) hcomm₀) c pK := by
    refine IsPullback.of_bot ?_ hκ₀fst.symm hKpb
    rw [hκ₀snd]
    exact hWy
  have hκ₀et : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (hKpb.lift (yoneda.map (sitePullbackFst B S hS bleg v) ≫ c)
        (yoneda.map (sitePullbackSnd B S hS bleg v)) hcomm₀) :=
    Space.presheaf_of_isPullback B S hS hκ₀pb hc
  have hDy := yoneda.map_isPullback
    (isPullback_sitePullback B S hS (sitePullbackFst B S hS bleg v ≫ aleg) v)
  rw [Functor.map_comp, hya] at hDy
  have hcomm₁ : (yoneda.map (sitePullbackFst B S hS
        (sitePullbackFst B S hS bleg v ≫ aleg) v) ≫
      hKpb.lift (yoneda.map (sitePullbackFst B S hS bleg v) ≫ c)
        (yoneda.map (sitePullbackSnd B S hS bleg v)) hcomm₀) ≫ (pK ≫ f₁) =
      yoneda.map (sitePullbackSnd B S hS (sitePullbackFst B S hS bleg v ≫ aleg) v) ≫
        yoneda.map v := by
    rw [Category.assoc, ← Category.assoc _ pK f₁, hκ₀fst, Category.assoc]
    exact hDy.w
  have hκ₁fst := hGpb.flip.lift_fst (yoneda.map (sitePullbackFst B S hS
    (sitePullbackFst B S hS bleg v ≫ aleg) v) ≫
      hKpb.lift (yoneda.map (sitePullbackFst B S hS bleg v) ≫ c)
        (yoneda.map (sitePullbackSnd B S hS bleg v)) hcomm₀)
    (yoneda.map (sitePullbackSnd B S hS (sitePullbackFst B S hS bleg v ≫ aleg) v)) hcomm₁
  have hκ₁snd := hGpb.flip.lift_snd (yoneda.map (sitePullbackFst B S hS
    (sitePullbackFst B S hS bleg v ≫ aleg) v) ≫
      hKpb.lift (yoneda.map (sitePullbackFst B S hS bleg v) ≫ c)
        (yoneda.map (sitePullbackSnd B S hS bleg v)) hcomm₀)
    (yoneda.map (sitePullbackSnd B S hS (sitePullbackFst B S hS bleg v ≫ aleg) v)) hcomm₁
  have hκ₁pb : IsPullback (yoneda.map (sitePullbackFst B S hS
      (sitePullbackFst B S hS bleg v ≫ aleg) v))
      (hGpb.flip.lift (yoneda.map (sitePullbackFst B S hS
        (sitePullbackFst B S hS bleg v ≫ aleg) v) ≫
        hKpb.lift (yoneda.map (sitePullbackFst B S hS bleg v) ≫ c)
          (yoneda.map (sitePullbackSnd B S hS bleg v)) hcomm₀)
        (yoneda.map (sitePullbackSnd B S hS (sitePullbackFst B S hS bleg v ≫ aleg) v)) hcomm₁)
      (hKpb.lift (yoneda.map (sitePullbackFst B S hS bleg v) ≫ c)
        (yoneda.map (sitePullbackSnd B S hS bleg v)) hcomm₀) qG := by
    refine IsPullback.of_bot ?_ hκ₁fst.symm hGpb.flip
    rw [hκ₁snd, ← Category.assoc _ pK f₁, hκ₀fst, Category.assoc]
    exact hDy
  have hκ₁et := Space.presheaf_of_isPullback B S hS hκ₁pb hκ₀et
  have hcomp : Space.IsLocallyQuasiFinite B S hS
      (hGpb.flip.lift (yoneda.map (sitePullbackFst B S hS
        (sitePullbackFst B S hS bleg v ≫ aleg) v) ≫
        hKpb.lift (yoneda.map (sitePullbackFst B S hS bleg v) ≫ c)
          (yoneda.map (sitePullbackSnd B S hS bleg v)) hcomm₀)
        (yoneda.map (sitePullbackSnd B S hS (sitePullbackFst B S hS bleg v ≫ aleg) v)) hcomm₁ ≫
        pG) :=
    Space.isLocallyQuasiFinite_comp B S hS
      (isAlgebraicSpace_yoneda B S hS _) hGsp (isAlgebraicSpace_yoneda B S hS V) _ pG
      (Space.isLocallyQuasiFinite_of_isEtale B S hS hGsp
        (Space.isEtale_of_presheaf_etale B S hS hκ₁et)) hpGlqf
  refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    (P := (@LocallyOfFiniteType.{u} ⊓ @LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
    AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_locallyOfFiniteType_inf_locallyQuasiFinite
    (sitePullbackSnd B S hS (sitePullbackFst B S hS bleg v ≫ aleg) v)).1 ?_
  rw [← hκ₁snd]
  exact hcomp


section Chart

variable {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (U : BigFppfOver B S hS) (p : schemeStack.{u, w} B S hS U ⟶ 𝒳)
  (P : Bicategory.TwoCommSq p p)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eF : StacksRepresentableCFG.EquivalenceOver P.pt.val.val.p
    (presheafOfCategories (F ⋙ typeToCat)).p)

include eF in
/-- **The presheaf-level double fibre of a field-valued point of a quasi-DM stack is locally
quasi-finite over that point.** -/
theorem exists_isPullback_isLocallyQuasiFinite_doubleFibre
    (h𝒳 : IsQuasiDMOver B S hS 𝒳)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hplft : AlgebraicStacks.IsLocallyOfFiniteType B S hS p)
    (hF : IsAlgebraicSpace B S hS F)
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (toBase : Spec (.of k) ⟶ S)
    (v : (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ⟶ U)
    (hvimm : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map v)) :
    ∃ (Kp Gp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pK : Kp ⟶ F)
      (qK : Kp ⟶ yoneda.obj (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
      (pG : Gp ⟶ yoneda.obj (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))) (qG : Gp ⟶ Kp),
      IsPullback pK qK (representingMap B S hS P.pt.val (schemeStack.{u, w} B S hS U).val F
          (yoneda.obj U) eF (representedChart B S hS U) P.snd.hom) (yoneda.map v) ∧
        IsPullback pG qG (yoneda.map v) (pK ≫ representingMap B S hS P.pt.val
          (schemeStack.{u, w} B S hS U).val F (yoneda.obj U) eF
          (representedChart B S hS U) P.fst.hom) ∧
        IsAlgebraicSpace B S hS Gp ∧ Space.IsLocallyQuasiFinite B S hS pG := by
  classical
  have hwlft : AlgebraicStacks.IsLocallyOfFiniteType B S hS (schemeStackMap.{u, w} B S hS v) :=
    AlgebraicStacks.isLocallyOfFiniteType_of_isImmersion B S hS _
      (AlgebraicStacks.isImmersion_schemeStackMap.{u, w} B S hS v hvimm)
  have hvY : representingMap B S hS (schemeStack.{u, w} B S hS
      (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))).val
      (schemeStack.{u, w} B S hS U).val (yoneda.obj (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
        (yoneda.obj U)
      (representedChart B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
        (representedChart B S hS U)
      (schemeStackMap.{u, w} B S hS v).hom = yoneda.map v := by
    rw [representingMap_representedChart_eq_yoneda_map_siteMap B S hS
        (schemeStackMap.{u, w} B S hS v),
      siteMap_schemeStackMap]
  -- the first base change: `V ×_U (U ×_𝒳 U)` along the second leg
  obtain ⟨Kp, eK, hKsp, hKpb⟩ := exists_representation_isPullback_twoFibreProductSquare
    B S hS (𝒜 := P.pt) (ℬ := schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
    (𝒞 := schemeStack.{u, w} B S hS U) F (yoneda.obj (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
      (yoneda.obj U) eF
    (representedChart B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))) (representedChart B S hS U)
      hF
    (isAlgebraicSpace_yoneda B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
      (isAlgebraicSpace_yoneda B S hS U) P.snd
    (schemeStackMap.{u, w} B S hS v)
  have hTzero : Bicategory.IsTwoFibreProduct (AlgebraicStacks.twoFibreProductSquare B S hS P.snd
      (schemeStackMap.{u, w} B S hS v)) :=
    AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS P.snd _
  -- the second base change: `(V ×_𝒳 U) ×_U V` along the first leg
  have hZ₁ : Bicategory.IsTwoFibreProduct (P.paste (AlgebraicStacks.twoFibreProductSquare B S hS
      P.snd (schemeStackMap.{u, w} B S hS v))) :=
    Bicategory.isTwoFibreProduct_paste hP hTzero
  obtain ⟨Gp, eG, hGsp, hGpb⟩ := exists_representation_isPullback_twoFibreProductSquare
    B S hS (𝒜 := schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)))
      (ℬ := (AlgebraicStacks.twoFibreProductSquare B S hS P.snd
      (schemeStackMap.{u, w} B S hS v)).pt)
    (𝒞 := schemeStack.{u, w} B S hS U) (yoneda.obj (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))) Kp
      (yoneda.obj U)
    (representedChart B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))) eK
      (representedChart B S hS U)
    (isAlgebraicSpace_yoneda B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))) hKsp
      (isAlgebraicSpace_yoneda B S hS U)
    (schemeStackMap.{u, w} B S hS v) ((AlgebraicStacks.twoFibreProductSquare B S hS P.snd
      (schemeStackMap.{u, w} B S hS v)).fst ≫ P.fst)
  have hTone : Bicategory.IsTwoFibreProduct (AlgebraicStacks.twoFibreProductSquare B S hS
      (schemeStackMap.{u, w} B S hS v)
      ((AlgebraicStacks.twoFibreProductSquare B S hS P.snd (schemeStackMap.{u, w} B S hS v)).fst ≫
        P.fst)) :=
    AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS _
      ((AlgebraicStacks.twoFibreProductSquare B S hS P.snd (schemeStackMap.{u, w} B S hS v)).fst ≫
      P.fst)
  -- the pasted square is a 2-fibre product of the cospan of the field-valued point
  have hZ₂ : Bicategory.IsTwoFibreProduct ((P.paste (AlgebraicStacks.twoFibreProductSquare B S hS
      P.snd (schemeStackMap.{u, w} B S hS v))).pasteFst
      (AlgebraicStacks.twoFibreProductSquare B S hS (schemeStackMap.{u, w} B S hS v)
      ((AlgebraicStacks.twoFibreProductSquare B S hS P.snd (schemeStackMap.{u, w} B S hS v)).fst ≫
        P.fst))) :=
    Bicategory.isTwoFibreProduct_pasteFst (P.paste (AlgebraicStacks.twoFibreProductSquare B S hS
      P.snd (schemeStackMap.{u, w} B S hS v))) hZ₁ (AlgebraicStacks.twoFibreProductSquare B S hS
      (schemeStackMap.{u, w} B S hS v)
      ((AlgebraicStacks.twoFibreProductSquare B S hS P.snd (schemeStackMap.{u, w} B S hS v)).fst ≫
        P.fst)) hTone
  have hKsqp := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS
    (schemeStackMap.{u, w} B S hS v ≫ p) (schemeStackMap.{u, w} B S hS v ≫ p)
  obtain ⟨eRel⟩ := (StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (AlgebraicStacks.twoFibreProductSquare B S hS (schemeStackMap.{u, w} B S hS v ≫ p)
      (schemeStackMap.{u, w} B S hS v ≫ p)).pt.val.property
        ((P.paste (AlgebraicStacks.twoFibreProductSquare B S hS P.snd
        (schemeStackMap.{u, w} B S hS v))).pasteFst (AlgebraicStacks.twoFibreProductSquare B S hS
        (schemeStackMap.{u, w} B S hS v)
      ((AlgebraicStacks.twoFibreProductSquare B S hS P.snd (schemeStackMap.{u, w} B S hS v)).fst ≫
        P.fst))).pt.val.property
    (CatFiberedInGroupoids.homFunctor (Quotient.out (hZ₂.from
      (AlgebraicStacks.twoFibreProductSquare B S hS (schemeStackMap.{u, w} B S hS v ≫ p)
      (schemeStackMap.{u, w} B S hS v ≫ p)))).hom.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p (Quotient.out
      (hZ₂.from (AlgebraicStacks.twoFibreProductSquare B S hS (schemeStackMap.{u, w} B S hS v ≫ p)
      (schemeStackMap.{u, w} B S hS v ≫ p)))).hom.hom)
    (isEquivalence_of_isTwoFibreProductAlgebraicStacks B S hS hKsqp hZ₂
      (Quotient.out (hZ₂.from (AlgebraicStacks.twoFibreProductSquare B S hS
        (schemeStackMap.{u, w} B S hS v ≫ p)
      (schemeStackMap.{u, w} B S hS v ≫ p)))))).map fun E => E.trans eG
  -- the dimension of the self-intersection of the field-valued point is at most zero
  have hdim : Space.dimension B S hS Gp hGsp ≤ 0 :=
    SelfIntersection.dimension_relation_le_zero B S hS k hk toBase
      (schemeStackMap.{u, w} B S hS v ≫ p) ⟨Gp, hGsp⟩ eRel h𝒳
      (AlgebraicStacks.isLocallyOfFiniteType_comp B S hS _ p hwlft hplft)
  -- the projection of the double fibre to the field-valued point
  have hZ₁lft : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      ((AlgebraicStacks.twoFibreProductSquare B S hS P.snd (schemeStackMap.{u, w} B S hS v)).fst ≫
      P.fst) :=
    AlgebraicStacks.isLocallyOfFiniteType_comp B S hS (AlgebraicStacks.twoFibreProductSquare B S hS
      P.snd (schemeStackMap.{u, w} B S hS v)).fst P.fst
      (AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS
        (schemeStackMap.{u, w} B S hS v) P.snd (AlgebraicStacks.twoFibreProductSquare B S hS P.snd
          (schemeStackMap.{u, w} B S hS v)) hTzero hwlft)
      (AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS p p P hP hplft)
  have hrmZlft := isLocallyOfFiniteType_representingMap B S hS
    (𝒳 := (AlgebraicStacks.twoFibreProductSquare B S hS P.snd (schemeStackMap.{u, w} B S hS v)).pt)
      (𝒴 := schemeStack.{u, w} B S hS U) Kp (yoneda.obj U)
    hKsp (isAlgebraicSpace_yoneda B S hS U) eK (representedChart B S hS U)
    ((AlgebraicStacks.twoFibreProductSquare B S hS P.snd (schemeStackMap.{u, w} B S hS v)).fst ≫
      P.fst) hZ₁lft
  have hpGlft := Space.IsLocallyOfFiniteType.of_isPullback B S hS hGpb hKsp
    (isAlgebraicSpace_yoneda B S hS U) hrmZlft
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj
      (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of k) : Type u))
  have hpGlqf := (Space.isLocallyQuasiFinite_iff_dimension_le_zero B S hS hGsp hsub _
    hpGlft).mpr hdim
  have hrmZeq : representingMap B S hS (AlgebraicStacks.twoFibreProductSquare B S hS P.snd
      (schemeStackMap.{u, w} B S hS v)).pt.val (schemeStack.{u, w} B S hS U).val Kp
      (yoneda.obj U) eK (representedChart B S hS U) ((AlgebraicStacks.twoFibreProductSquare B S hS
        P.snd (schemeStackMap.{u, w} B S hS v)).fst ≫ P.fst).hom =
      representingMap B S hS (AlgebraicStacks.twoFibreProductSquare B S hS P.snd
        (schemeStackMap.{u, w} B S hS v)).pt.val P.pt.val Kp F eK eF
        (AlgebraicStacks.twoFibreProductSquare B S hS P.snd
        (schemeStackMap.{u, w} B S hS v)).fst.hom ≫
        representingMap B S hS P.pt.val (schemeStack.{u, w} B S hS U).val F (yoneda.obj U) eF
          (representedChart B S hS U) P.fst.hom :=
    representingMap_comp B S hS (𝒜 := (AlgebraicStacks.twoFibreProductSquare B S hS P.snd
      (schemeStackMap.{u, w} B S hS v)).pt.val) (ℬ := P.pt.val)
      (𝒞 := (schemeStack.{u, w} B S hS U).val) Kp F (yoneda.obj U) eK eF
      (representedChart B S hS U) (AlgebraicStacks.twoFibreProductSquare B S hS P.snd
        (schemeStackMap.{u, w} B S hS v)).fst.hom P.fst.hom
  rw [hvY] at hKpb
  rw [hvY, hrmZeq] at hGpb
  exact ⟨Kp, Gp, _, _, _, _, hKpb, hGpb, hGsp, hpGlqf⟩

variable (R : BigFppfOver B S hS) (c : yoneda.obj R ⟶ F)

include eF in
/-- **The scheme-theoretic double fibre of a charted self-intersection of a quasi-DM stack is
locally quasi-finite over the field-valued point.** -/
theorem locallyQuasiFinite_doubleFibre_sitePullback
    (h𝒳 : IsQuasiDMOver B S hS 𝒳)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hplft : AlgebraicStacks.IsLocallyOfFiniteType B S hS p)
    (hF : IsAlgebraicSpace B S hS F)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (toBase : Spec (.of k) ⟶ S)
    (v : (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)) ⟶ U)
    (hvimm : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map v)) :
    LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map
        (sitePullbackSnd B S hS
          (sitePullbackFst B S hS (chartLeg B S hS U p P F eF R c P.snd) v ≫
            chartLeg B S hS U p P F eF R c P.fst) v)) ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
        (sitePullbackSnd B S hS
          (sitePullbackFst B S hS (chartLeg B S hS U p P F eF R c P.snd) v ≫
            chartLeg B S hS U p P F eF R c P.fst) v)) := by
  obtain ⟨Kp, Gp, pK, qK, pG, qG, hKpb, hGpb, hGsp, hpGlqf⟩ :=
    exists_isPullback_isLocallyQuasiFinite_doubleFibre B S hS U p P F eF h𝒳 hP hplft hF
      k hk toBase v hvimm
  have hfin := locallyOfFiniteType_inf_locallyQuasiFinite_sitePullbackSnd B S hS
    (representingMap B S hS P.pt.val (schemeStack.{u, w} B S hS U).val F
      (yoneda.obj U) eF (representedChart B S hS U) P.fst.hom)
    (representingMap B S hS P.pt.val (schemeStack.{u, w} B S hS U).val F
      (yoneda.obj U) eF (representedChart B S hS U) P.snd.hom)
    v c (chartLeg B S hS U p P F eF R c P.fst) (chartLeg B S hS U p P F eF R c P.snd)
    (yoneda.map_preimage _) (yoneda.map_preimage _) hc pK qK hKpb pG qG hGpb hGsp hpGlqf
  exact ⟨hfin.2, hfin.1⟩

include eF in
/-- **The double fibre of a charted self-intersection of a quasi-DM stack is discrete at a
point whose two images agree and are closed.** -/
theorem discreteTopology_doubleFibre_chartLeg
    (h𝒳 : IsQuasiDMOver B S hS 𝒳)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hplft : AlgebraicStacks.IsLocallyOfFiniteType B S hS p)
    (hF : IsAlgebraicSpace B S hS F)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (r₀ : (BigFppfOver.toScheme B S hS).obj R)
    (hclosed : IsClosed ({(BigFppfOver.toScheme B S hS).map
                            (chartLeg B S hS U p P F eF R c P.snd) r₀} :
      Set ((BigFppfOver.toScheme B S hS).obj U))) :
    DiscreteTopology ((((BigFppfOver.toScheme B S hS).map
          (chartLeg B S hS U p P F eF R c P.snd)).fiberι
        ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.snd) r₀) ≫
      (BigFppfOver.toScheme B S hS).map
        (chartLeg B S hS U p P F eF R c P.fst)).fiber
      ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.snd) r₀)) := by
  have hk : B.Contains (Spec (((BigFppfOver.toScheme B S hS).obj U).residueField
      ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.snd) r₀))) :=
    B.residueField_spec_contains U.left.property
      ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.snd) r₀)
  have _ : AlgebraicGeometry.IsClosedImmersion
      (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField
      ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.snd) r₀)) :=
    isClosed_singleton_iff_isClosedImmersion.mp hclosed
  obtain ⟨hlqf, hlft⟩ := locallyQuasiFinite_doubleFibre_sitePullback B S hS U p P F eF R c
    h𝒳 hP hplft hF hc
    (IsLocalRing.ResidueField ↑(((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk
      ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.snd) r₀)))
    hk (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField
      ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.snd) r₀) ≫ U.hom.hom)
    (BigFppfOver.siteMapOver B S hS U hk
      (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField
        ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.snd) r₀)))
    (inferInstanceAs (AlgebraicGeometry.IsImmersion
      (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField
        ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.snd) r₀))))
  let := hlft
  let : Subsingleton ((BigFppfOver.toScheme B S hS).obj
      (BigFppfOver.siteObjectOver B S hS U hk
        (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField
          ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.snd) r₀)))) :=
    inferInstanceAs (Subsingleton (Spec (((BigFppfOver.toScheme B S hS).obj U).residueField
      ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.snd) r₀)) : Type u))
  exact (@locallyQuasiFinite_iff_discreteTopology_of_subsingleton _ _
    ((BigFppfOver.toScheme B S hS).map
      (sitePullbackSnd B S hS
        (sitePullbackFst B S hS (chartLeg B S hS U p P F eF R c P.snd)
            (BigFppfOver.siteMapOver B S hS U hk
              (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField
                ((BigFppfOver.toScheme B S hS).map
                  (chartLeg B S hS U p P F eF R c P.snd) r₀))) ≫
          chartLeg B S hS U p P F eF R c P.fst)
        (BigFppfOver.siteMapOver B S hS U hk
          (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField
            ((BigFppfOver.toScheme B S hS).map
              (chartLeg B S hS U p P F eF R c P.snd) r₀))))) _ hlft).mp hlqf

include eF in
/-- **The isolated-point input of the slicing step of Stacks 06MF, at a general quasi-DM
stack.** -/
theorem isIsolatedPoint_asFiber_chartLeg_of_isQuasiDM
    (h𝒳 : IsQuasiDMOver B S hS 𝒳)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hplft : AlgebraicStacks.IsLocallyOfFiniteType B S hS p)
    (hF : IsAlgebraicSpace B S hS F)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (r₀ : (BigFppfOver.toScheme B S hS).obj R)
    (hab : (BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.fst) r₀ =
      (BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.snd) r₀)
    (hclosed : IsClosed ({(BigFppfOver.toScheme B S hS).map
                            (chartLeg B S hS U p P F eF R c P.snd) r₀} :
      Set ((BigFppfOver.toScheme B S hS).obj U))) :
    IsIsolatedPoint
      ((((BigFppfOver.toScheme B S hS).map
            (chartLeg B S hS U p P F eF R c P.snd)).fiberι
          ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.snd) r₀) ≫
        (BigFppfOver.toScheme B S hS).map
          (chartLeg B S hS U p P F eF R c P.fst)).asFiber
        (((BigFppfOver.toScheme B S hS).map
          (chartLeg B S hS U p P F eF R c P.snd)).asFiber r₀)) :=
  isIsolatedPoint_asFiber_of_discreteTopology _ _ r₀ hab
    (discreteTopology_doubleFibre_chartLeg B S hS U p P F eF R c h𝒳 hP hplft hF hc r₀
      hclosed)

include eF in
/-- **The closed-point input of the quasi-finiteness datum of the slicing step of Stacks 06MF,
at a general quasi-DM stack.** -/
theorem isClosed_asFiber_chartLeg_of_isQuasiDM
    (h𝒳 : IsQuasiDMOver B S hS 𝒳)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hplft : AlgebraicStacks.IsLocallyOfFiniteType B S hS p)
    (hF : IsAlgebraicSpace B S hS F)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (r₀ : (BigFppfOver.toScheme B S hS).obj R)
    (hab : (BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.fst) r₀ =
      (BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.snd) r₀)
    (hclosed : IsClosed ({(BigFppfOver.toScheme B S hS).map
                            (chartLeg B S hS U p P F eF R c P.snd) r₀} :
      Set ((BigFppfOver.toScheme B S hS).obj U))) :
    IsClosed ({((BigFppfOver.toScheme B S hS).map
        (chartLeg B S hS U p P F eF R c P.snd)).asFiber r₀} :
      Set (((BigFppfOver.toScheme B S hS).map
        (chartLeg B S hS U p P F eF R c P.snd)).fiber
        ((BigFppfOver.toScheme B S hS).map
          (chartLeg B S hS U p P F eF R c P.snd) r₀))) :=
  isClosed_asFiber_of_discreteTopology _ _ r₀ hab
    (discreteTopology_doubleFibre_chartLeg B S hS U p P F eF R c h𝒳 hP hplft hF hc r₀
      hclosed) hclosed

end Chart

section CanonicalSquare

variable {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (U : BigFppfOver B S hS) (p : schemeStack.{u, w} B S hS U ⟶ 𝒳)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eF : StacksRepresentableCFG.EquivalenceOver
    (twoFibreProductSquareAlgebraicStacks B S hS p p).pt.val.val.p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (R : BigFppfOver B S hS) (c : yoneda.obj R ⟶ F)

include eF in
/-- **Both inputs of the slicing step of Stacks 06MF, at a general quasi-DM algebraic stack.**
Let `𝒳` be quasi-DM over `S`, let `p : U ⟶ 𝒳` be a smooth 1-morphism out of the algebraic stack
represented by a scheme `U` of the site, let `F` represent the apex of the canonical 2-fibre
product square `U ×_𝒳 U` and let `c : h_R ⟶ F` be an étale chart of `F`, surjective on points, by
a scheme `R` of the site. Then over every point `u` of `U` which is closed in `U` there is a
point `r₀` of `R` — the identity point of **Stacks 04XH** — which is an isolated point of the
double fibre and is closed in its fibre under the second leg.

These are the two data the chart construction of **Stacks 06MF** consumes at the point it slices,
and they are delivered here with no field-valued point of the base and nothing carried: the
hypotheses are quasi-DM-ness of `𝒳` over `S`, smoothness of `p`, and the chart being étale and
surjective. -/
theorem exists_point_isIsolatedPoint_isClosed_asFiber_chartLeg_of_isQuasiDM
    (h𝒳 : IsQuasiDMOver B S hS 𝒳)
    (hp : AlgebraicStacks.IsSmooth B S hS p)
    (hF : IsAlgebraicSpace B S hS F)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (hcsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (u : (BigFppfOver.toScheme B S hS).obj U)
    (hu : IsClosed ({u} : Set ((BigFppfOver.toScheme B S hS).obj U))) :
    ∃ r₀ : (BigFppfOver.toScheme B S hS).obj R,
      IsIsolatedPoint
        ((((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
          (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
              (twoFibreProductSquareAlgebraicStacks B S hS p p).snd)).fiberι
            ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
              (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
              (twoFibreProductSquareAlgebraicStacks B S hS p p).snd) r₀) ≫
          (BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
            (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
            (twoFibreProductSquareAlgebraicStacks B S hS p p).fst)).asFiber
          (((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
            (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
            (twoFibreProductSquareAlgebraicStacks B S hS p p).snd)).asFiber r₀)) ∧
      IsClosed ({((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
        (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
          (twoFibreProductSquareAlgebraicStacks B S hS p p).snd)).asFiber r₀} :
        Set (((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
          (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
          (twoFibreProductSquareAlgebraicStacks B S hS p p).snd)).fiber
          ((BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
            (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
            (twoFibreProductSquareAlgebraicStacks B S hS p p).snd) r₀))) := by
  obtain ⟨r₀, hfst, hsnd⟩ := exists_point_chartLeg_eq B S hS U p
    (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS p p) hcsurj u
  have hab := hfst.trans hsnd.symm
  have hcl : IsClosed ({(BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p
      (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c
      (twoFibreProductSquareAlgebraicStacks B S hS p p).snd) r₀} :
      Set ((BigFppfOver.toScheme B S hS).obj U)) := by rw [hsnd]; exact hu
  have hlft := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS p hp
  exact ⟨r₀, isIsolatedPoint_asFiber_chartLeg_of_isQuasiDM B S hS U p
      (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c h𝒳
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS p p) hlft hF hc r₀ hab hcl,
    isClosed_asFiber_chartLeg_of_isQuasiDM B S hS U p
      (twoFibreProductSquareAlgebraicStacks B S hS p p) F eF R c h𝒳
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS p p) hlft hF hc r₀ hab hcl⟩

end CanonicalSquare


end AlgebraicGeometry.Stack

end
