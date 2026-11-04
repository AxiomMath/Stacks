module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesRSStarGluing
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.Deformation.Artin.RimSchlessinger.ComparisonCocone
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FromThickeningPushouts

/-!
# Condition (RS*) for the stack of curves

Condition (RS*) of Stacks 07Y8 asks that for every square of affine objects of the big fppf site
whose square of rings is a fibre product along a surjection with square-zero kernel, the
comparison functor from the fibre of a category fibred in groupoids over the fourth corner to the
two-fibre product of the fibres over the other three corners be an equivalence. For the stack of
curves this is the case of Stacks 0D56 at such a square: the square is a pushout of affine schemes
along a first-order thickening
(`Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine_of_pair`),
families of curves glue across it, and a family of curves over the pushout is the pushout of its
restrictions.

The comparison functor is read through spans and cocones (`CategoryTheory.Functor.SquareSpan`): it
is essentially surjective as soon as every span has a cocone
(`Deformation.Artin.essSurj_fiberSquareComparison_of_nonempty_cocone`), and it is fully faithful as
soon as cocones are unique up to unique isomorphism
(`AlgebraicGeometry.C1590Private.full_fiberSquareComparison_of_hasUniqueSquareCocones` and
`AlgebraicGeometry.C1590Private.faithful_fiberSquareComparison_of_hasUniqueSquareCocones`, the
converse of `Deformation.Artin.hasUniqueSquareCocones_of_fullyFaithful`).

## Main results

* `AlgebraicGeometry.C1590Private.satisfiesRSStar_curves`: the stack of curves satisfies
  condition (RS*).

## References

* [Stacks Project, Tag 0D56](https://stacks.math.columbia.edu/tag/0D56)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Deformation.Artin

universe v₁ v₂ u₁ u₂ u

namespace AlgebraicGeometry.C1590Private

/-! ### Full faithfulness of the comparison from unique cocones -/

section Comparison

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  CategoryTheory.Limits.CategoricalPullback.π₁
  CategoryTheory.Limits.CategoricalPullback.π₂

variable {C : Type u₁} [Category.{v₁} C] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {q : 𝒳 ⥤ C} (hq : q.IsFiberedInGroupoids) (c : q.ChoiceOfPullbacks)
variable {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
variable (h : f ≫ i = g ≫ j)

/-- The span over `(f, g)` of the two chosen restrictions of an object `x` of the fibre over `Z`,
identified over `U` by the structure isomorphism of the comparison. -/
def restrictionSpan (x : q.Fiber Z) : SquareSpan q f g where
  u := (c.obj f (c.obj i x)).1
  x := (c.obj i x).1
  y := (c.obj j x).1
  α := c.map f (c.obj i x)
  β := Fiber.fiberInclusion.map ((fiberSquareComparison q c f g i j h).obj x).iso.hom ≫
    c.map g (c.obj j x)
  isHomLift_α := (c.isStronglyCartesian f (c.obj i x)).toIsHomLift
  isHomLift_β := by
    have := (c.isStronglyCartesian g (c.obj j x)).toIsHomLift
    infer_instance

/-- An object `x` of the fibre over `Z` is a cocone over the span of its restrictions. -/
def restrictionCocone (x : q.Fiber Z) : (restrictionSpan c f g i j h x).Cocone i j where
  z := x.1
  ξ := c.map i x
  η := c.map j x
  isHomLift_ξ := (c.isStronglyCartesian i x).toIsHomLift
  isHomLift_η := (c.isStronglyCartesian j x).toIsHomLift
  w := by
    change c.map f (c.obj i x) ≫ c.map i x =
      (Fiber.fiberInclusion.map ((fiberSquareComparison q c f g i j h).obj x).iso.hom ≫
        c.map g (c.obj j x)) ≫ c.map j x
    rw [Category.assoc]
    exact (fiberSquareComparison_obj_iso_hom_fac q c f g i j h x).symm

/-- A morphism `m` of the two-fibre product from the image of `x` to the image of `y` makes `y`
a cocone over the span of the restrictions of `x`. -/
def transportedCocone {x y : q.Fiber Z}
    (m : (fiberSquareComparison q c f g i j h).obj x ⟶
      (fiberSquareComparison q c f g i j h).obj y) :
    (restrictionSpan c f g i j h x).Cocone i j where
  z := y.1
  ξ := Fiber.fiberInclusion.map m.fst ≫ c.map i y
  η := Fiber.fiberInclusion.map m.snd ≫ c.map j y
  isHomLift_ξ := by
    have := (c.isStronglyCartesian i y).toIsHomLift
    have : q.IsHomLift (𝟙 V) (Fiber.fiberInclusion.map m.fst) := m.fst.2
    exact IsHomLift.comp_lift_id_left (p := q) i (c.map i y) (Fiber.fiberInclusion.map m.fst)
  isHomLift_η := by
    have := (c.isStronglyCartesian j y).toIsHomLift
    have : q.IsHomLift (𝟙 W) (Fiber.fiberInclusion.map m.snd) := m.snd.2
    exact IsHomLift.comp_lift_id_left (p := q) j (c.map j y) (Fiber.fiberInclusion.map m.snd)
  w := by
    have hw : Fiber.fiberInclusion.map (c.homMap f m.fst) ≫
        Fiber.fiberInclusion.map ((fiberSquareComparison q c f g i j h).obj y).iso.hom =
        Fiber.fiberInclusion.map ((fiberSquareComparison q c f g i j h).obj x).iso.hom ≫
          Fiber.fiberInclusion.map (c.homMap g m.snd) := by
      simpa only [Functor.map_comp, ChoiceOfPullbacks.pullbackFunctor_map] using
        congrArg (fun φ => Fiber.fiberInclusion.map φ) m.w
    have e₁ : Fiber.fiberInclusion.map (c.homMap f m.fst) ≫ c.map f (c.obj i y) =
        c.map f (c.obj i x) ≫ Fiber.fiberInclusion.map m.fst := c.homMap_fac f m.fst
    have e₂ : Fiber.fiberInclusion.map (c.homMap g m.snd) ≫ c.map g (c.obj j y) =
        c.map g (c.obj j x) ≫ Fiber.fiberInclusion.map m.snd := c.homMap_fac g m.snd
    change c.map f (c.obj i x) ≫ Fiber.fiberInclusion.map m.fst ≫ c.map i y =
      (Fiber.fiberInclusion.map ((fiberSquareComparison q c f g i j h).obj x).iso.hom ≫
        c.map g (c.obj j x)) ≫ Fiber.fiberInclusion.map m.snd ≫ c.map j y
    calc c.map f (c.obj i x) ≫ Fiber.fiberInclusion.map m.fst ≫ c.map i y
        = Fiber.fiberInclusion.map (c.homMap f m.fst) ≫ c.map f (c.obj i y) ≫ c.map i y := by
          rw [reassoc_of% e₁]
      _ = Fiber.fiberInclusion.map (c.homMap f m.fst) ≫
            Fiber.fiberInclusion.map ((fiberSquareComparison q c f g i j h).obj y).iso.hom ≫
              c.map g (c.obj j y) ≫ c.map j y := by
          rw [fiberSquareComparison_obj_iso_hom_fac q c f g i j h y]
      _ = Fiber.fiberInclusion.map ((fiberSquareComparison q c f g i j h).obj x).iso.hom ≫
            Fiber.fiberInclusion.map (c.homMap g m.snd) ≫ c.map g (c.obj j y) ≫ c.map j y := by
          rw [reassoc_of% hw]
      _ = _ := by rw [reassoc_of% e₂, Category.assoc]

/-- **The comparison is full when cocones are unique.** -/
theorem full_fiberSquareComparison_of_hasUniqueSquareCocones
    (hu : HasUniqueSquareCocones q f g i j) :
    (fiberSquareComparison q c f g i j h).Full where
  map_surjective {x y} m := by
    obtain ⟨⟨θ⟩, -⟩ := hu _ (restrictionCocone c f g i j h x) (transportedCocone c f g i j h m)
    let γ : x ⟶ y := ⟨θ.θ, θ.isHomLift_θ⟩
    exact ⟨γ, CategoricalPullback.hom_ext (c.homMap_uniq i γ m.fst θ.comm_ξ.symm).symm
      (c.homMap_uniq j γ m.snd θ.comm_η.symm).symm⟩

/-- **The comparison is faithful when cocones are unique.** -/
theorem faithful_fiberSquareComparison_of_hasUniqueSquareCocones
    (hu : HasUniqueSquareCocones q f g i j) :
    (fiberSquareComparison q c f g i j h).Faithful where
  map_injective {x y γ₁ γ₂} e := by
    have h₁ : c.homMap i γ₁ = c.homMap i γ₂ := congrArg CategoricalPullback.Hom.fst e
    have h₂ : c.homMap j γ₁ = c.homMap j γ₂ := congrArg CategoricalPullback.Hom.snd e
    let K := transportedCocone c f g i j h ((fiberSquareComparison q c f g i j h).map γ₁)
    let key : ∀ γ : x ⟶ y, c.homMap i γ = c.homMap i γ₁ → c.homMap j γ = c.homMap j γ₁ →
        (restrictionCocone c f g i j h x).Hom K := fun γ e₁ e₂ =>
      { θ := Fiber.fiberInclusion.map γ
        isHomLift_θ := γ.2
        comm_ξ := by
          show c.map i x ≫ _ = Fiber.fiberInclusion.map (c.homMap i γ₁) ≫ c.map i y
          rw [← e₁]
          exact (c.homMap_fac i γ).symm
        comm_η := by
          show c.map j x ≫ _ = Fiber.fiberInclusion.map (c.homMap j γ₁) ≫ c.map j y
          rw [← e₂]
          exact (c.homMap_fac j γ).symm }
    exact Fiber.hom_ext ((hu _ _ K).2 (key γ₁ rfl rfl) (key γ₂ h₁.symm h₂.symm))

end Comparison

/-! ### Spans and cocones of families of curves -/

section Curves

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

variable (B hZ) in
/-- The projection of the stack of curves to the big fppf site of `Spec ℤ`. -/
abbrev curvesP : CurveFamily B hZ ⥤ BigFppfOver B integerBase hZ :=
  (curvesFiberedCategory B hZ).val.p

/-- The projection of the stack of curves takes a family to its base. -/
theorem curvesP_obj (X : CurveFamily B hZ) : (curvesP B hZ).obj X = X.base := rfl

/-- The projection of the stack of curves takes a morphism of families to its base map. -/
theorem curvesP_map {X Y : CurveFamily B hZ} (φ : X ⟶ Y) : (curvesP B hZ).map φ = φ.baseMap := rfl

/-- The base map of a morphism of families lying over `f` is `f`, up to the identifications of
the bases. -/
theorem baseMap_eq_of_isHomLift {R T : BigFppfOver B integerBase hZ} (f : R ⟶ T)
    {X Y : CurveFamily B hZ} (φ : X ⟶ Y) [(curvesP B hZ).IsHomLift f φ] :
    φ.baseMap = eqToHom (show X.base = R from IsHomLift.domain_eq (curvesP B hZ) f φ) ≫ f ≫
      eqToHom (show Y.base = T from IsHomLift.codomain_eq (curvesP B hZ) f φ).symm :=
  IsHomLift.fac' (curvesP B hZ) f φ

variable {U V W Z : BigFppfOver B integerBase hZ} {f : U ⟶ V} {g : U ⟶ W} {i : V ⟶ Z}
  {j : W ⟶ Z}

/-- A square of the shape of condition (RS*), read on the bases of a span of families of curves
and of a family over `Z` with morphisms lying over `i` and `j`. -/
theorem rsSquare_of_span (hsq : RSSquare g f j i) (s : SquareSpan (curvesP B hZ) f g)
    (K : s.Cocone i j) : RSSquare s.β.baseMap s.α.baseMap K.η.baseMap K.ξ.baseMap :=
  hsq.of_eqToHom (show s.u.base = U from IsHomLift.domain_eq (curvesP B hZ) f s.α)
    (show s.y.base = W from IsHomLift.codomain_eq (curvesP B hZ) g s.β)
    (show s.x.base = V from IsHomLift.codomain_eq (curvesP B hZ) f s.α)
    (show K.z.base = Z from IsHomLift.codomain_eq (curvesP B hZ) i K.ξ)
    (baseMap_eq_of_isHomLift g s.β) (baseMap_eq_of_isHomLift f s.α)
    (by rw [baseMap_eq_of_isHomLift j K.η])
    (baseMap_eq_of_isHomLift i K.ξ)

/-- **Every span of families of curves over an (RS*) square has a cocone** (the essential
surjectivity half of Stacks 0D56): the glued family of
`AlgebraicGeometry.C1590Private.exists_glue`. -/
theorem nonempty_cocone (w : f ≫ i = g ≫ j) (hsq : RSSquare g f j i)
    (s : SquareSpan (curvesP B hZ) f g) :
    Nonempty (s.Cocone i j) := by
  have hu : s.u.base = U := IsHomLift.domain_eq (curvesP B hZ) f s.α
  have hx : s.x.base = V := IsHomLift.codomain_eq (curvesP B hZ) f s.α
  have hy : s.y.base = W := IsHomLift.codomain_eq (curvesP B hZ) g s.β
  let a' : s.y.base ⟶ Z := eqToHom hy ≫ j
  let b' : s.x.base ⟶ Z := eqToHom hx ≫ i
  have hRS : RSSquare s.β.baseMap s.α.baseMap a' b' :=
    hsq.of_eqToHom hu hy hx rfl (baseMap_eq_of_isHomLift g s.β)
      (baseMap_eq_of_isHomLift f s.α) (by simp only [eqToHom_refl, Category.comp_id]; rfl)
      (by simp only [eqToHom_refl, Category.comp_id]; rfl)
  obtain ⟨E, g₀, c₁, c₂, hc₁, hc₂, hcomm, hfl, hpr, hfp, hdim⟩ := exists_glue s.α s.β hRS
  let K : CurveFamily B hZ :=
    { base := Z
      total := E
      toBase := g₀
      flat := hfl
      proper := hpr
      finitePresentation := hfp
      relativeDimensionLE := hdim }
  let ξ : s.x ⟶ K := ⟨b', c₁, hc₁⟩
  let η : s.y ⟶ K := ⟨a', c₂, hc₂⟩
  refine ⟨{ z := K, ξ := ξ, η := η, isHomLift_ξ := ?_, isHomLift_η := ?_, w := ?_ }⟩
  · exact (IsHomLift.lift_eqToHom_comp_iff (p := curvesP B hZ) i ξ hx).1 (IsHomLift.map _ ξ)
  · exact (IsHomLift.lift_eqToHom_comp_iff (p := curvesP B hZ) j η hy).1 (IsHomLift.map _ η)
  · refine CurveFamily.Hom.ext ?_ hcomm
    show s.α.baseMap ≫ b' = s.β.baseMap ≫ a'
    rw [baseMap_eq_of_isHomLift f s.α, baseMap_eq_of_isHomLift g s.β]
    simpa only [a', b', Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      using congrArg (fun φ => eqToHom hu ≫ φ) w

/-- The base maps of the first legs of two cocones differ by the identification of their bases. -/
theorem cocone_ξ_baseMap_eq {s : SquareSpan (curvesP B hZ) f g} (K K' : s.Cocone i j)
    (e : K.z.base = K'.z.base) : K'.ξ.baseMap = K.ξ.baseMap ≫ eqToHom e := by
  rw [baseMap_eq_of_isHomLift i K.ξ, baseMap_eq_of_isHomLift i K'.ξ]
  simp only [Category.assoc, eqToHom_trans]

/-- The base maps of the second legs of two cocones differ by the identification of their
bases. -/
theorem cocone_η_baseMap_eq {s : SquareSpan (curvesP B hZ) f g} (K K' : s.Cocone i j)
    (e : K.z.base = K'.z.base) : K'.η.baseMap = K.η.baseMap ≫ eqToHom e := by
  rw [baseMap_eq_of_isHomLift j K.η, baseMap_eq_of_isHomLift j K'.η]
  simp only [Category.assoc, eqToHom_trans]

/-- **Cocones of families of curves over an (RS*) square are unique up to unique isomorphism**
(the full faithfulness half of Stacks 0D56): the total space of a cocone is the pushout of the
total spaces of the span (`AlgebraicGeometry.C1590Private.isPushout_totalMap`), so a cocone maps
to another one by the morphism the pushout induces, and by no other. -/
theorem hasUniqueSquareCocones (hsq : RSSquare g f j i) :
    HasUniqueSquareCocones (curvesP B hZ) f g i j := by
  intro s K₁ K₂
  have hpo : ∀ K : s.Cocone i j, IsPushout s.β.totalMap s.α.totalMap K.η.totalMap K.ξ.totalMap :=
    fun K => isPushout_totalMap s.α s.β K.ξ K.η K.w (rsSquare_of_span hsq s K)
  have hz₁ : K₁.z.base = Z := IsHomLift.codomain_eq (curvesP B hZ) i K₁.ξ
  have hz₂ : K₂.z.base = Z := IsHomLift.codomain_eq (curvesP B hZ) i K₂.ξ
  -- the morphism of cocones from `K` to `K'` induced by the pushout property of `K`
  have desc : ∀ K K' : s.Cocone i j, ∃ t, K.η.totalMap ≫ t = K'.η.totalMap ∧
      K.ξ.totalMap ≫ t = K'.ξ.totalMap := fun K K' =>
    ⟨_, (hpo K).inl_desc K'.η.totalMap K'.ξ.totalMap (congrArg CurveFamily.Hom.totalMap K'.w).symm,
      (hpo K).inr_desc _ _ _⟩
  obtain ⟨t, ht₁, ht₂⟩ := desc K₁ K₂
  obtain ⟨t', ht'₁, ht'₂⟩ := desc K₂ K₁
  have : IsIso t := ⟨t', (hpo K₁).hom_ext (by rw [reassoc_of% ht₁, ht'₁, Category.comp_id])
      (by rw [reassoc_of% ht₂, ht'₂, Category.comp_id]),
    (hpo K₂).hom_ext (by rw [reassoc_of% ht'₁, ht₁, Category.comp_id])
      (by rw [reassoc_of% ht'₂, ht₂, Category.comp_id])⟩
  let e : K₁.z.base = K₂.z.base := hz₁.trans hz₂.symm
  have : IsIso (schemeSpaceMap (eqToHom e)) :=
    (inferInstance : IsIso ((schemeSpaceFunctor B integerBase hZ).map (eqToHom e)))
  have hcomm : t ≫ K₂.z.toBase = K₁.z.toBase ≫ schemeSpaceMap (eqToHom e) := by
    refine (hpo K₁).hom_ext ?_ ?_
    · rw [reassoc_of% ht₁, K₂.η.cartesian.w, reassoc_of% K₁.η.cartesian.w,
        ← schemeSpaceMap_comp, ← cocone_η_baseMap_eq K₁ K₂ e]
    · rw [reassoc_of% ht₂, K₂.ξ.cartesian.w, reassoc_of% K₁.ξ.cartesian.w,
        ← schemeSpaceMap_comp, ← cocone_ξ_baseMap_eq K₁ K₂ e]
  let θ : K₁.z ⟶ K₂.z := ⟨eqToHom e, t, IsPullback.of_horiz_isIso ⟨hcomm⟩⟩
  have hθ : (curvesP B hZ).IsHomLift (𝟙 Z) θ := by
    refine IsHomLift.of_fac' (curvesP B hZ) (𝟙 Z) θ hz₁ hz₂ ?_
    show (eqToHom e : K₁.z.base ⟶ K₂.z.base) = eqToHom hz₁ ≫ 𝟙 Z ≫ eqToHom hz₂.symm
    simp only [Category.id_comp, eqToHom_trans]
  refine ⟨⟨{ θ := θ, isHomLift_θ := hθ, comm_ξ := ?_, comm_η := ?_ }⟩, ?_⟩
  · exact CurveFamily.Hom.ext (cocone_ξ_baseMap_eq K₁ K₂ e).symm ht₂
  · exact CurveFamily.Hom.ext (cocone_η_baseMap_eq K₁ K₂ e).symm ht₁
  · intro m m'
    refine CurveFamily.Hom.ext ?_ ?_
    · rw [baseMap_eq_of_isHomLift (𝟙 Z) m.θ, baseMap_eq_of_isHomLift (𝟙 Z) m'.θ]
    · exact (hpo K₁).hom_ext
        ((congrArg CurveFamily.Hom.totalMap m.comm_η).trans
          (congrArg CurveFamily.Hom.totalMap m'.comm_η).symm)
        ((congrArg CurveFamily.Hom.totalMap m.comm_ξ).trans
          (congrArg CurveFamily.Hom.totalMap m'.comm_ξ).symm)

end Curves

/-! ### Condition (RS*) -/

/-- **The stack of curves satisfies condition (RS*)** (Stacks 07Y8), by Stacks 0D56: across a
square of affine objects of the big fppf site whose ring square is a fibre product along a
surjection with square-zero kernel, families of curves over the fourth corner are the compatible
pairs of families over the two middle corners. -/
theorem satisfiesRSStar_curves (B : BigFppfSite.{u}) (hZ : B.Contains integerBase) :
    SatisfiesRSStar B integerBase hZ (curvesFiberedCategory B hZ).val.p
      (curvesFiberedCategory B hZ).property := by
  refine satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine_of_pair B
    integerBase hZ _ _ ?_
  intro X X' Y Y' i f a b w hX hX' hY hY' hfi hfb hpush
  have hsq : RSSquare i f a b := ⟨hX, hX', hY, hY', hfi, hfb, hpush⟩
  have hp := (curvesFiberedCategory B hZ).property
  have hu := hasUniqueSquareCocones (B := B) (hZ := hZ) hsq
  exact
    { faithful := faithful_fiberSquareComparison_of_hasUniqueSquareCocones _ f i b a w.symm hu
      full := full_fiberSquareComparison_of_hasUniqueSquareCocones _ f i b a w.symm hu
      essSurj := essSurj_fiberSquareComparison_of_nonempty_cocone hp _ f i b a w.symm
        (nonempty_cocone w.symm hsq) }

end AlgebraicGeometry.C1590Private

end
