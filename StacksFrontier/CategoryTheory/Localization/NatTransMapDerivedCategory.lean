module

public import StacksFrontier.AlgebraicGeometry.Perfect.Approximation.OpenSubscheme

/-!
# The derived form of a natural transformation away from the image of the localization

`CategoryTheory.NatTrans.mapDerivedCategory` is defined as a lift through the localization
`DerivedCategory.Q`, so it is constrained only on the objects `Q.obj K` for `K` a cochain
complex.  A consumer which feeds it objects produced by another functor out of the derived
category — such as a derived pullback `Lf^*` — meets it at objects that are not of that form.

The transformation at an arbitrary object `Z` is nevertheless pinned by its composite with any
morphism `Z ⟶ Q.obj K`: naturality moves the transformation onto `Q.obj K`, where the defining
formula computes it.  So the whiskering is upgraded from `Q` to `Q ⋙ H`, for any `H`, by
naturality together with the existence of such a morphism, and neither essential surjectivity of
`Q` nor a choice of preimage enters.  For a derived functor the morphism is the canonical
comparison, which is available at every object by construction.

## Main results

* `CategoryTheory.NatTrans.mapDerivedCategory_app_Q`: the defining formula for the derived
  transformation at an object in the image of `DerivedCategory.Q`.
* `CategoryTheory.NatTrans.mapDerivedCategory_app_comp` and
  `CategoryTheory.NatTrans.mapDerivedCategory_app_comp_Qh`: the derived transformation at an
  arbitrary object, composed with a morphism into the image of `DerivedCategory.Q` and of
  `DerivedCategory.Qh` respectively.
* `CategoryTheory.NatTrans.mapDerivedCategory_app_Qh_comp`: the derived transformation on the
  image of `DerivedCategory.Qh`.
* `CategoryTheory.NatTrans.mapDerivedCategory_eq`: a transformation of derived functors
  satisfying the defining formula is the derived transformation.
* `CategoryTheory.NatTrans.mapDerivedCategory_id` and
  `CategoryTheory.NatTrans.mapDerivedCategory_comp`: the construction is functorial.
* `CategoryTheory.NatTrans.isIso_mapDerivedCategory`: an isomorphism of exact functors induces
  an isomorphism of the functors they induce on unbounded derived categories.
* `CategoryTheory.NatTrans.mapDerivedCategoryCompToId_app`,
  `CategoryTheory.NatTrans.mapDerivedCategoryCompToId_app_Q` and
  `CategoryTheory.NatTrans.mapDerivedCategoryCompToId_app_comp`: the same for the counit-shaped
  form `G.mapDerivedCategory ⋙ F.mapDerivedCategory ⟶ 𝟭`.

## Implementation notes

The lift `CategoryTheory.NatTrans.mapDerivedCategory` through `DerivedCategory.Q` can be taken
through either spelling of the intermediate functor —
`DerivedCategory.Q ⋙ F.mapDerivedCategory` conjugated by
`CategoryTheory.Functor.mapDerivedCategoryFactors`, or
`F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q` directly. Both give one
construction with one type and one set of hypotheses;
`CategoryTheory.NatTrans.mapDerivedCategory_eq` is what makes any such spelling recognisable as
this one.

`DerivedCategory.Qh.obj M` is `DerivedCategory.Q.obj M.as`, but `Qh` carries `no_expose`, so
that identification is unavailable to `rw` and to unification at reducible transparency.  The
statements on the image of `Qh` are therefore phrased through the isomorphism
`CategoryTheory.DerivedCategory.quotientCompQhIso` rather than by unfolding, and their proofs
are terms rather than rewrites.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category

namespace CategoryTheory

universe v₁ v₂ u₁ u₂ w₁ w₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]

section

variable {F G : C ⥤ D} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The derived form of a natural transformation of exact functors on an object in the image of
the localization.** It is the degreewise transformation on the cochain complex, conjugated by the
two factorizations of `CategoryTheory.Functor.mapDerivedCategoryFactors`. -/
theorem NatTrans.mapDerivedCategory_app_Q (η : F ⟶ G) (K : CochainComplex C ℤ) :
    (NatTrans.mapDerivedCategory η).app (DerivedCategory.Q.obj K) =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app K) ≫
        G.mapDerivedCategoryFactors.inv.app K := by
  rw [NatTrans.mapDerivedCategory, Localization.liftNatTrans_app]
  simp [Localization.Lifting.compLeft_iso]

/-- Two natural transformations of derived functors agreeing on the image of the localization
are equal. -/
private theorem mapDerivedCategory_natTrans_ext {τ τ' : F.mapDerivedCategory ⟶ G.mapDerivedCategory}
    (h : ∀ K : CochainComplex C ℤ, τ.app (DerivedCategory.Q.obj K) =
      τ'.app (DerivedCategory.Q.obj K)) : τ = τ' :=
  Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) h

/-- **A transformation of derived functors agreeing with the degreewise transformation on the
image of the localization is the derived transformation.** -/
theorem NatTrans.mapDerivedCategory_eq (η : F ⟶ G)
    (τ : F.mapDerivedCategory ⟶ G.mapDerivedCategory)
    (hτ : ∀ K : CochainComplex C ℤ, τ.app (DerivedCategory.Q.obj K) =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app K) ≫
        G.mapDerivedCategoryFactors.inv.app K) :
    τ = NatTrans.mapDerivedCategory η :=
  mapDerivedCategory_natTrans_ext fun K => by
    rw [hτ, NatTrans.mapDerivedCategory_app_Q]

/-- **The derived form of a natural transformation at an arbitrary object, composed with a
morphism into the image of the localization.** Naturality carries the transformation onto the
image of `DerivedCategory.Q`, where `CategoryTheory.NatTrans.mapDerivedCategory_app_Q` computes
it. -/
@[reassoc]
theorem NatTrans.mapDerivedCategory_app_comp (η : F ⟶ G) {Z : DerivedCategory C}
    {K : CochainComplex C ℤ} (h : Z ⟶ DerivedCategory.Q.obj K) :
    (NatTrans.mapDerivedCategory η).app Z ≫ G.mapDerivedCategory.map h =
      F.mapDerivedCategory.map h ≫ F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app K) ≫
        G.mapDerivedCategoryFactors.inv.app K := by
  rw [← NatTrans.mapDerivedCategory_app_Q η K, (NatTrans.mapDerivedCategory η).naturality h]

/-- **The derived form of a natural transformation on an object in the image of the localization
of the homotopy category.** The comparison
`CategoryTheory.DerivedCategory.quotientCompQhIso` is invertible, so this determines the
transformation at `DerivedCategory.Qh.obj M` for every `M`. -/
theorem NatTrans.mapDerivedCategory_app_Qh_comp (η : F ⟶ G)
    (M : HomotopyCategory C (ComplexShape.up ℤ)) :
    (NatTrans.mapDerivedCategory η).app (DerivedCategory.Qh.obj M) ≫
        G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app M.as) =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app M.as) ≫
        F.mapDerivedCategoryFactors.hom.app M.as ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app M.as) ≫
        G.mapDerivedCategoryFactors.inv.app M.as :=
  NatTrans.mapDerivedCategory_app_comp η
    ((DerivedCategory.quotientCompQhIso C).hom.app M.as)

/-- **The derived form of a natural transformation at an arbitrary object, composed with a
morphism into the image of the localization of the homotopy category.** Naturality reduces the
transformation at an object outside the image of `DerivedCategory.Q` to the transformation at
`DerivedCategory.Qh.obj M`, which
`CategoryTheory.NatTrans.mapDerivedCategory_app_Qh_comp` computes. -/
@[reassoc]
theorem NatTrans.mapDerivedCategory_app_comp_Qh (η : F ⟶ G) {Z : DerivedCategory C}
    {M : HomotopyCategory C (ComplexShape.up ℤ)} (h : Z ⟶ DerivedCategory.Qh.obj M) :
    (NatTrans.mapDerivedCategory η).app Z ≫ G.mapDerivedCategory.map h =
      F.mapDerivedCategory.map h ≫
        (NatTrans.mapDerivedCategory η).app (DerivedCategory.Qh.obj M) :=
  ((NatTrans.mapDerivedCategory η).naturality h).symm

/-- **The identity transformation induces the identity on derived functors.** -/
@[simp]
theorem NatTrans.mapDerivedCategory_id :
    NatTrans.mapDerivedCategory (𝟙 F) = 𝟙 F.mapDerivedCategory :=
  mapDerivedCategory_natTrans_ext fun K => by
    rw [NatTrans.mapDerivedCategory_app_Q]; simp

/-- **The derived form of a vertical composite of natural transformations is the composite of
their derived forms.** -/
@[simp]
theorem NatTrans.mapDerivedCategory_comp {H : C ⥤ D} [H.Additive] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H] (η : F ⟶ G) (θ : G ⟶ H) :
    NatTrans.mapDerivedCategory (η ≫ θ) =
      NatTrans.mapDerivedCategory η ≫ NatTrans.mapDerivedCategory θ :=
  mapDerivedCategory_natTrans_ext fun K => by
    rw [NatTrans.mapDerivedCategory_app_Q, NatTrans.comp_app,
      NatTrans.mapDerivedCategory_app_Q, NatTrans.mapDerivedCategory_app_Q]
    simp

/-- **An isomorphism of exact functors induces an isomorphism of the functors they induce on
unbounded derived categories.** The derived form of the inverse is a two-sided inverse, by
functoriality of the construction. -/
instance NatTrans.isIso_mapDerivedCategory (η : F ⟶ G) [IsIso η] :
    IsIso (NatTrans.mapDerivedCategory η) :=
  ⟨NatTrans.mapDerivedCategory (inv η), by
      rw [← NatTrans.mapDerivedCategory_comp, IsIso.hom_inv_id,
        NatTrans.mapDerivedCategory_id], by
      rw [← NatTrans.mapDerivedCategory_comp, IsIso.inv_hom_id,
        NatTrans.mapDerivedCategory_id]⟩

end

section CompToId

variable (G : C ⥤ D) (F : D ⥤ C) [G.Additive] [PreservesFiniteLimits G]
  [PreservesFiniteColimits G] [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The counit-shaped derived transformation in its three factors:** the identification of the
derived functor of a composite with the composite of the derived functors, the derived
transformation, and the identification of the derived functor of `𝟭` with `𝟭`. -/
theorem NatTrans.mapDerivedCategoryCompToId_app (η : G ⋙ F ⟶ 𝟭 C) (Z : DerivedCategory C) :
    (NatTrans.mapDerivedCategoryCompToId G F η).app Z =
      (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso G F).inv.app Z ≫
        (NatTrans.mapDerivedCategory η).app Z ≫ Functor.mapDerivedCategoryIdIso.hom.app Z :=
  rfl

/-- **The counit-shaped derived transformation at an object in the image of the localization.**
Its middle factor is computed by `CategoryTheory.NatTrans.mapDerivedCategory_app_Q`. -/
theorem NatTrans.mapDerivedCategoryCompToId_app_Q (η : G ⋙ F ⟶ 𝟭 C) (K : CochainComplex C ℤ) :
    (NatTrans.mapDerivedCategoryCompToId G F η).app (DerivedCategory.Q.obj K) =
      (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso G F).inv.app
            (DerivedCategory.Q.obj K) ≫
        ((G ⋙ F).mapDerivedCategoryFactors.hom.app K ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app K) ≫
            (𝟭 C).mapDerivedCategoryFactors.inv.app K) ≫
          Functor.mapDerivedCategoryIdIso.hom.app (DerivedCategory.Q.obj K) := by
  rw [NatTrans.mapDerivedCategoryCompToId_app, NatTrans.mapDerivedCategory_app_Q]

/-- **The counit-shaped derived transformation at an arbitrary object, composed with a morphism
into the image of the localization.** Naturality against the identity functor, which is the
whiskering upgrade in counit form: the derived counit at an object outside the image of
`DerivedCategory.Q` is determined by its composite with any morphism into that image. -/
@[reassoc]
theorem NatTrans.mapDerivedCategoryCompToId_app_comp (η : G ⋙ F ⟶ 𝟭 C)
    {Z : DerivedCategory C} {K : CochainComplex C ℤ} (h : Z ⟶ DerivedCategory.Q.obj K) :
    (NatTrans.mapDerivedCategoryCompToId G F η).app Z ≫ h =
      F.mapDerivedCategory.map (G.mapDerivedCategory.map h) ≫
        (NatTrans.mapDerivedCategoryCompToId G F η).app (DerivedCategory.Q.obj K) :=
  ((NatTrans.mapDerivedCategoryCompToId G F η).naturality h).symm

/-- **The counit-shaped derived transformation at an arbitrary object, composed with a morphism
into the image of the localization of the homotopy category.** The form of
`CategoryTheory.NatTrans.mapDerivedCategoryCompToId_app_comp` matching the comparison morphisms
of a derived functor on the unbounded homotopy category. -/
@[reassoc]
theorem NatTrans.mapDerivedCategoryCompToId_app_comp_Qh (η : G ⋙ F ⟶ 𝟭 C)
    {Z : DerivedCategory C} {M : HomotopyCategory C (ComplexShape.up ℤ)}
    (h : Z ⟶ DerivedCategory.Qh.obj M) :
    (NatTrans.mapDerivedCategoryCompToId G F η).app Z ≫ h =
      F.mapDerivedCategory.map (G.mapDerivedCategory.map h) ≫
        (NatTrans.mapDerivedCategoryCompToId G F η).app (DerivedCategory.Qh.obj M) :=
  ((NatTrans.mapDerivedCategoryCompToId G F η).naturality h).symm

end CompToId

end CategoryTheory

end
