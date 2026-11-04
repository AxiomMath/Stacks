module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealizationSelfProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.FieldSpectrumCoverSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeIsomorphism

/-!
# The self-product hypothesis of Stacks 0DTI for the quotient stack of an open subgroupoid

Let `φ : (U, P, …) ⟶ (U, R, …)` be an open subgroupoid of a groupoid scheme containing every arrow
of `R` with source and target a point `u ∈ U`, and let `f : 𝒰 ⟶ 𝒳` be a 1-morphism of algebraic
stacks which, up to a 2-isomorphism, is a fully faithful `𝒰 ⥤ [U/P]` followed by
`[φ] : [U/P] ⟶ [U/R]` and by a fully faithful `[U/R] ⥤ 𝒳`. Let `p` be a field-valued point of
`𝒰` whose image in `[U/P]` is presented by a generalized point of `U` lying over `u`. Then `f`
satisfies the hypothesis of **Stacks 0DTI** at the point of `p`: the comparison
`Spec k ×_𝒰 Spec k ⟶ Spec k ×_𝒳 Spec k` is an equivalence.

This is the step of the proof of **Stacks 0DU5** "since `P ⊂ R` is open and contains
`{r ∈ R : s(r) = u, t(r) = u}` we see that `u ×_𝒰 u ⟶ u ×_𝒳 u` is an isomorphism", with the
étale 1-morphism `[U/R] ⟶ 𝒳` of the source's proof factored as an equivalence onto an open
substack followed by its inclusion, which is how the étale local chart constructs it.

## Main results

* `AlgebraicGeometry.Stack.pointsMap_fieldValuedPointStackMorphism_fieldSpectrumPoint`: the
  1-morphism of a field-valued point sends the tautological point of the spectrum of its field to
  the point of the field-valued point.
* `AlgebraicGeometry.Stack.exists_iso_pointwiseToQuotientStack_of_fieldValuedPoint`: the objects of
  the image of `Spec k ⟶ 𝒰` in `[U/P]` are presented by the pullbacks of the point presenting
  the image of `p`.
* `AlgebraicGeometry.Stack.hasSelfProductEquivalenceAt_of_quotientStackMap_realization`: the
  hypothesis of Stacks 0DTI.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 0DTI](https://stacks.math.columbia.edu/tag/0DTI)
* [Stacks Project, Tag 0DU5](https://stacks.math.columbia.edu/tag/0DU5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids.GroupoidScheme

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The 1-morphism of a field-valued point sends the tautological point of the spectrum of its
field to the point of the field-valued point.** The image of the tautological point is the chosen
lift of the object of `p` along the identity, which maps to the object of `p`, so the two
field-valued points have a common refinement. -/
theorem pointsMap_fieldValuedPointStackMorphism_fieldSpectrumPoint
    (𝒰 : AlgebraicStacks.{u, w} B S hS) (p : FieldValuedPoint B S hS 𝒰.val.val) :
    AlgebraicStacks.pointsMap B S hS (fieldValuedPointStackMorphism.{u, w} B S hS 𝒰 p)
        (pointClass B S hS _ _
          (fieldSpectrumPoint.{u, w} B S hS (FieldValuedPoint.fieldSpectrum B S hS p))) =
      pointClass B S hS 𝒰.val.val 𝒰.val.isFiberedInGroupoids p := by
  refine (class_eq_class_iff_hasCommonExtension B S hS 𝒰.val.val _ _ _).2 ?_
  exact ⟨_, ⟨𝟙 _⟩, ⟨(Functor.TwoYoneda.chosenLift 𝒰.val.val.p 𝒰.val.isFiberedInGroupoids p.base
    (Functor.Fiber.mk (a := p.obj) p.over) (Over.mk (𝟙 p.base))).φ⟩⟩

/-- **The objects of a field-valued point's 1-morphism are presented by points over `u`.** Let
`E : 𝒰 ⥤ [U/G]` be a 1-morphism over the site and `p` a field-valued point of `𝒰` whose image
under `E` is identified, over the identity of its base, with the object presented by a
generalized point `x` of `U`. Then the image under `E` of every object of the 1-morphism
`Spec k ⟶ 𝒰` of `p`, lying over `a : T ⟶ Spec k`, is isomorphic to the object presented by the
pullback of `x` along `a`: both map to the object presented by `x` over `a`, and in a category
fibred in groupoids such arrows are strongly cartesian, so their sources are isomorphic. -/
theorem exists_iso_pointwiseToQuotientStack_of_fieldValuedPoint {A : AlgebraicSpaces B S hS}
    {G : AlgebraicGeometry.GroupoidInAlgebraicSpaces B S hS A}
    {𝒰 : AlgebraicStacks.{u, w} B S hS} (E : 𝒰.val.val ⥤ᵇ quotientStack G)
    (p : FieldValuedPoint B S hS 𝒰.val.val) (x : G.objects.obj.obj (op p.base))
    (j : E.obj p.obj ≅ ((pointwiseToQuotientStackFiber G p.base).obj x).1)
    (hj : (quotientStack G).p.IsHomLift (𝟙 p.base) j.hom)
    (a : (schemeStack.{u, w} B S hS p.base).val.val.obj) :
    Nonempty (E.obj ((CatFiberedInGroupoids.homFunctor
        (fieldValuedPointStackMorphism.{u, w} B S hS 𝒰 p).hom).obj a) ≅
      (pointwiseToQuotientStack G).obj
        ⟨a.left, G.objects.obj.map a.hom.op x⟩) := by
  let cl := Functor.TwoYoneda.chosenLift 𝒰.val.val.p 𝒰.val.isFiberedInGroupoids p.base
    (Functor.Fiber.mk (a := p.obj) p.over) a
  have : 𝒰.val.val.p.IsHomLift a.hom cl.φ := cl.isStronglyCartesian.toIsHomLift
  let jh : E.obj p.obj ⟶ (pointwiseToQuotientStack G).obj ⟨p.base, x⟩ := j.hom
  have hj' : (quotientStack G).p.IsHomLift (𝟙 p.base) jh := hj
  let eφ : E.obj cl.y ⟶ E.obj p.obj := E.map cl.φ
  have : (quotientStack G).p.IsHomLift a.hom eφ :=
    Functor.isHomLift_map_of_comp_eq E.w a.hom cl.φ
  obtain ⟨φ₁, h₁⟩ : ∃ φ₁ : E.obj cl.y ⟶ (pointwiseToQuotientStack G).obj ⟨p.base, x⟩,
      (quotientStack G).p.IsHomLift a.hom φ₁ :=
    ⟨eφ ≫ jh, IsHomLift.comp_lift_id_right' (quotientStack G).p a.hom eφ p.base jh⟩
  let c : (⟨a.left, G.objects.obj.map a.hom.op x⟩ : (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) ⟶ ⟨p.base, x⟩ :=
    ⟨a.hom, 𝟙 _⟩
  have : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p.IsHomLift
      a.hom c :=
    IsHomLift.map (p := (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p) c
  have h₂ : (quotientStack G).p.IsHomLift a.hom ((pointwiseToQuotientStack G).map c) :=
    Functor.isHomLift_map_of_comp_eq (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq
      a.hom c
  have hcart : ∀ {X Y} (g : X ⟶ Y), (quotientStack G).p.IsHomLift a.hom g →
      (quotientStack G).p.IsCartesian a.hom g := fun g hg =>
    have := (isFiberedInGroupoids_quotientStack G).isStronglyCartesian_homLift a.hom g
    inferInstance
  exact ⟨@Functor.IsCartesian.domainUniqueUpToIso _ _ _ _ (quotientStack G).p _ _ _ _ a.hom
    _ (hcart _ h₂) _ φ₁ (hcart _ h₁)⟩

/-- **The hypothesis of Stacks 0DTI for the quotient stack of an open subgroupoid scheme.** Let
`φ : H ⟶ K` be a morphism of groupoid schemes which is an open immersion on arrows and an
equality on objects, and let `u` be a point of the object scheme of `K` such that every arrow of
`K` with source and target `u` lies in the image of `φ`. Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism of
algebraic stacks whose underlying functor is isomorphic to `E ⋙ [φ] ⋙ F` for fully faithful
1-morphisms `E : 𝒰 ⥤ [U/H]` and `F : [U/K] ⥤ 𝒳` over the site, and let `p` be a field-valued
point of `𝒰` whose image under `E` is identified, over the identity of its base, with the object
presented by a generalized point of `U` lying over `u`. Then the comparison
`Spec k ×_𝒰 Spec k ⟶ Spec k ×_𝒳 Spec k` for the 1-morphism of `p` is an equivalence: `f`
satisfies the hypothesis of Stacks 0DTI at the point of `p`.

The functor of `f` is faithful, `E`, `[φ]` (whose arrow map is a monomorphism) and `F` being so.
It is surjective on the morphisms between objects of the image of `Spec k ⟶ 𝒰`: their images
under `E` are presented by generalized points over `u`
(`AlgebraicGeometry.Stack.exists_iso_pointwiseToQuotientStack_of_fieldValuedPoint`), between
which `[φ]` is surjective because every arrow of `K` over `u` comes from `H`
(`Stacks.Groupoids.GroupoidScheme.Hom.realization_arrow_lift`), and `E` and `F` are full. Then
`CategoryTheory.TwoFibreProductOver.isEquivalence_mapBase_of_surjective` applies. -/
theorem hasSelfProductEquivalenceAt_of_quotientStackMap_realization
    {H K : Stacks.Groupoids.GroupoidScheme S} (φ : Hom H K)
    [AlgebraicGeometry.IsOpenImmersion φ.mapArrows.left]
    (hHU : B.Contains H.objects.left) (hHR : B.Contains H.arrows.left)
    (hHP : B.Contains (pullback H.source H.target).left)
    (hKU : B.Contains K.objects.left) (hKR : B.Contains K.arrows.left)
    (hKP : B.Contains (pullback K.source K.target).left)
    (e : H.objects = K.objects) (hφ : φ.mapObjects = eqToHom e) (u : K.objects.left)
    (hstab : ∀ r : K.arrows.left, K.source.left.base r = u → K.target.left.base r = u →
      ∃ p : H.arrows.left, φ.mapArrows.left.base p = r)
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳)
    (E : 𝒰.val.val ⥤ᵇ quotientStack (H.realization B hS hHU hHR hHP))
    (hE : E.toFunctor.FullyFaithful)
    (F : quotientStack (K.realization B hS hKU hKR hKP) ⥤ᵇ 𝒳.val.val)
    (hF : F.toFunctor.FullyFaithful)
    (ι : CatFiberedInGroupoids.homFunctor f.hom ≅ E.toFunctor ⋙
      (quotientStackMap (φ.realization B hS hHU hHR hHP hKU hKR hKP)).toFunctor ⋙ F.toFunctor)
    (p : FieldValuedPoint B S hS 𝒰.val.val)
    (x : (H.realization B hS hHU hHR hHP).objects.obj.obj (op p.base))
    (hx : Hom.IsOverPoint B hS hHU hHR hHP ((eqToHom e.symm).left.base u) p.base x)
    (j : E.obj p.obj ≅
      ((pointwiseToQuotientStackFiber (H.realization B hS hHU hHR hHP) p.base).obj x).1)
    (hj : (quotientStack (H.realization B hS hHU hHR hHP)).p.IsHomLift (𝟙 p.base) j.hom) :
    HasSelfProductEquivalenceAt B S hS f
      (pointClass B S hS 𝒰.val.val 𝒰.val.isFiberedInGroupoids p) := by
  let M := (quotientStackMap (φ.realization B hS hHU hHR hHP hKU hKR hKP)).toFunctor
  let q := fieldValuedPointStackMorphism.{u, w} B S hS 𝒰 p
  let Q := CatFiberedInGroupoids.homFunctor q.hom
  refine ⟨FieldValuedPoint.fieldSpectrum B S hS p, q, _,
    pointsMap_fieldValuedPointStackMorphism_fieldSpectrumPoint B S hS 𝒰 p, ?_⟩
  -- the objects of the image of `Spec k ⟶ 𝒰` are presented by points over `u`
  have hgood : ∀ a, ∃ X : (presheafOfGroupoids (evaluationGroupoidFunctor
      (H.realization B hS hHU hHR hHP).toGroupoidInFunctors)).obj,
      Hom.IsOverPoint B hS hHU hHR hHP ((eqToHom e.symm).left.base u) X.base X.fiber ∧
        Nonempty (E.obj (Q.obj a) ≅ (pointwiseToQuotientStack _).obj X) := fun a =>
    ⟨⟨a.left, _⟩, Hom.isOverPoint_map B hS hHU hHR hHP _ a.hom x hx,
      exists_iso_pointwiseToQuotientStack_of_fieldValuedPoint B S hS E p x j hj a⟩
  -- `[φ]` is surjective on the morphisms between their images under `E`
  have hM : ∀ a b, Function.Surjective (M.map : (E.obj (Q.obj a) ⟶ E.obj (Q.obj b)) → _) :=
    fun a b => quotientStackMap_map_surjective_of_good _
      (Hom.IsOverPoint B hS hHU hHR hHP ((eqToHom e.symm).left.base u))
      (fun g y hy => Hom.isOverPoint_map B hS hHU hHR hHP _ g y hy)
      (fun T x y hx hy b hbs hbt => Hom.realization_arrow_lift B hS φ hHU hHR hHP hKU hKR hKP
        e hφ u hstab T x y hx hy b hbs hbt) (hgood a) (hgood b)
  -- hence `E ⋙ [φ]` is surjective on the morphisms between objects of the image of `Q`
  have hEM : ∀ a b, Function.Surjective ((E.toFunctor ⋙ M).map : (Q.obj a ⟶ Q.obj b) → _) := by
    intro a b g
    obtain ⟨h, rfl⟩ := hM a b g
    exact ⟨hE.preimage h, by simp [M]⟩
  have : F.toFunctor.Full := hF.full
  have hsurj : ∀ a b, Function.Surjective
      ((CatFiberedInGroupoids.homFunctor f.hom).map : (Q.obj a ⟶ Q.obj b) → _) := fun a b =>
    Functor.map_surjective_of_iso_comp (𝟭 _) F.toFunctor (E.toFunctor ⋙ M)
      (CatFiberedInGroupoids.homFunctor f.hom) ι.symm (hEM a b)
  have : Mono φ.mapArrows := (Over.forget S).mono_of_mono_map
    (inferInstance : Mono φ.mapArrows.left)
  have : M.Faithful := faithful_quotientStackMap_of_mono _
    (Hom.mono_realization_mapArrows B hS φ hHU hHR hHP hKU hKR hKP)
  have : E.toFunctor.Faithful := hE.faithful
  have : F.toFunctor.Faithful := hF.faithful
  have : (CatFiberedInGroupoids.homFunctor f.hom).Faithful :=
    Functor.Faithful.of_iso ι.symm
  exact TwoFibreProductOver.isEquivalence_mapBase_of_surjective _ hsurj fun a b => hsurj b a

end AlgebraicGeometry.Stack

end
