module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekSumResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatIsFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekFiniteGeneration
public import StacksFrontier.AlgebraicGeometry.Etale.GeometricSkyscraper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.ShriekConstantFree
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories

/-!
# Sheaves of `Λ`-modules whose étale stalks are flat

Let `B` be a big étale site, `X` an object of it and `Λ` a commutative ring. A sheaf of
`Λ`-modules on the small étale site of `X` has **flat étale stalks** when
`Module.Flat Λ ((AlgebraicGeometry.etaleModuleStalkFunctor B X Λ s).obj F)` holds at every
geometric point `s` of `X`. This file develops that condition and shows that the generators of
Stacks 093B (2) satisfy it.

Three things make the condition useful, and none of them asks anything of `X`.

* It implies flatness over the constant coefficient ring sheaf,
  `AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_flat_etaleModuleStalk`: that
  is Stacks 05VC against the conservative family of lifted geometric points, and it generalizes
  `AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_isConstructibleFlatModuleSheaf`,
  which is now a corollary of it.
* It is stable under arbitrary coproducts, because the stalk functor is the fibre functor of a
  point of the site and hence a left adjoint.
* The generators `j_{U!}\underline{Λ}` of Stacks 093B (2) have it, for an arbitrary étale object
  `U`, because their stalks are projective.

Consequently every object of `D⁻` of the small étale site of an **arbitrary** scheme is
represented by a bounded above complex of sheaves with flat étale stalks, which is
`AlgebraicGeometry.exists_isStrictlyLE_flat_etaleModuleStalk_of_isLE`.

## Main results

* `AlgebraicGeometry.preservesColimitsOfShape_etaleModuleStalkFunctor` — the étale module stalk
  functor preserves colimits of every shape.
* `AlgebraicGeometry.flat_etaleModuleStalk_sigma` — an arbitrary coproduct of sheaves with flat
  étale stalks has flat étale stalks.
* `AlgebraicGeometry.projective_etaleModuleStalk_moduleShriekConstant` and
  `AlgebraicGeometry.flat_etaleModuleStalk_moduleShriekConstant` — the étale stalk of
  `j_{U!}\underline{Λ}` is projective, hence flat, for an arbitrary étale object `U`.
* `AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_flat_etaleModuleStalk` — flat
  étale stalks give flatness over the constant coefficient ring sheaf.
* `AlgebraicGeometry.flat_etaleModuleStalk_smallEtaleSheafPullback` — flat étale stalks are
  stable under small étale inverse image, the stalk of an inverse image being a stalk of the
  original sheaf.
* `AlgebraicGeometry.exists_epi_flat_etaleModuleStalk` — every sheaf of `Λ`-modules is a quotient
  of one with flat étale stalks.
* `AlgebraicGeometry.exists_isStrictlyLE_flat_etaleModuleStalk_of_isLE` — hence every bounded
  above object of the derived category is represented by a bounded above complex of sheaves with
  flat étale stalks.

## Implementation notes

The identification `AlgebraicGeometry.etaleModuleStalkFunctor B X Λ s =
(AlgebraicGeometry.geometricSitePoint B X s).sheafFiber` holds by `rfl`, both sides being the
colimit of the sections over the category of pointed étale neighbourhoods; it is what makes
Mathlib's `CategoryTheory.GrothendieckTopology.Point.skyscraperSheafAdjunction` available, and
with it the left adjointness of the stalk. The two spellings of the point,
`AlgebraicGeometry.geometricSitePoint` and
`AlgebraicGeometry.geometricPointSitePoint`, are equal only at default transparency, so the
proofs below keep to the first and reach the skyscraper through a single `change`.

Projectivity of the stalk of `j_{U!}\underline{Λ}` is a two-step adjunction computation and not
a corollary of flat constructibility: `j_{U!}\underline{Λ}` is *not* constructible for a general
`U`, so `AlgebraicGeometry.etaleModuleStalk_projective_of_isConstructibleFlatModuleSheaf` does
not apply. Instead, maps out of `j_{U!}\underline{Λ}` are sections over `U`
(`AlgebraicGeometry.moduleShriekConstantCoyonedaIso`) and maps out of its stalk are sections of
the skyscraper over `U`, that is, a product of copies of the target indexed by the lifts of the
geometric point; a product of surjections is surjective.

## References

* [Stacks Project, Tag 093B](https://stacks.math.columbia.edu/tag/093B)
* [Stacks Project, Tag 05VC](https://stacks.math.columbia.edu/tag/05VC)
* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w r v₁ v₂

namespace AlgebraicGeometry

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

/-! ### A product of epimorphisms of modules is an epimorphism -/

/-- **A product of epimorphisms of modules is an epimorphism.** The categorical product is the
module-theoretic one, where a family of surjections is surjective componentwise. -/
public theorem ModuleCat.epi_piMap_const.{iu, mu, ru} {Λ : Type ru} [CommRing Λ] {ι : Type iu}
    {N N' : ModuleCat.{max iu mu} Λ} (e : N ⟶ N') [Epi e]
    [HasProduct fun _ : ι => N] [HasProduct fun _ : ι => N'] :
    Epi (Limits.Pi.map fun _ : ι => e) := by
  classical
  have he : Function.Surjective e.hom := (ModuleCat.epi_iff_surjective e).1 ‹_›
  set d : ModuleCat.of Λ (∀ _ : ι, (N : Type (max iu mu))) ⟶
      ModuleCat.of Λ (∀ _ : ι, (N' : Type (max iu mu))) :=
    ModuleCat.ofHom (LinearMap.pi fun i : ι => e.hom.comp (LinearMap.proj i)) with hd
  have hde : Epi d := (ModuleCat.epi_iff_surjective d).2 fun y =>
    ⟨fun i => (he (y i)).choose, funext fun i => (he (y i)).choose_spec⟩
  have hsq : (ModuleCat.piIsoPi fun _ : ι => N).inv ≫ (Limits.Pi.map fun _ : ι => e) =
      d ≫ (ModuleCat.piIsoPi fun _ : ι => N').inv := by
    apply Limits.Pi.hom_ext
    intro i
    simp only [Category.assoc, Limits.Pi.map_π, hd]
    rw [ModuleCat.piIsoPi_inv_kernel_ι, ← Category.assoc,
      ModuleCat.piIsoPi_inv_kernel_ι]
    ext x
    rfl
  have hfac : (Limits.Pi.map fun _ : ι => e) =
      (ModuleCat.piIsoPi fun _ : ι => N).hom ≫ d ≫
        (ModuleCat.piIsoPi fun _ : ι => N').inv := by
    rw [← hsq, Iso.hom_inv_id_assoc]
  rw [hfac]
  infer_instance

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]

/-! ### (α1) The stalk functor preserves arbitrary coproducts -/

section Alpha1

variable [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)] [HasLimitsOfSize.{u, u} (ModuleCat.{w} Λ)]

/-- The étale module stalk functor preserves colimits of every shape: it is the fibre functor of
the point `AlgebraicGeometry.geometricSitePoint`, which is left adjoint to the skyscraper. -/
public theorem preservesColimitsOfShape_etaleModuleStalkFunctor
    (s : GeometricPoint X.obj) (A : Type v₁) [Category.{v₂} A] :
    PreservesColimitsOfShape A (etaleModuleStalkFunctor B X Λ s) :=
  inferInstanceAs (PreservesColimitsOfShape A
    ((geometricSitePoint B X s).sheafFiber (A := ModuleCat.{w} Λ)))

/-- **The étale module stalk of an arbitrary coproduct of sheaves with flat stalks is flat.**
The stalk functor is a left adjoint, so it carries the coproduct to the coproduct of the
stalks, which in `ModuleCat` is the direct sum; a direct sum of flat modules is flat. -/
public theorem flat_etaleModuleStalk_sigma {A : Type w}
    (M : A → Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    (s : GeometricPoint X.obj) [HasCoproduct M]
    [HasCoproduct fun a => (etaleModuleStalkFunctor B X Λ s).obj (M a)]
    (h : ∀ a, Module.Flat Λ ((etaleModuleStalkFunctor B X Λ s).obj (M a))) :
    Module.Flat Λ ((etaleModuleStalkFunctor B X Λ s).obj (∐ M)) := by
  classical
  have : PreservesColimit (Discrete.functor M) (etaleModuleStalkFunctor B X Λ s) :=
    (preservesColimitsOfShape_etaleModuleStalkFunctor B X Λ s
      (Discrete A)).preservesColimit
  have hd : Module.Flat Λ
      (DirectSum A fun a => ((etaleModuleStalkFunctor B X Λ s).obj (M a) : Type w)) :=
    Module.Flat.directSum
  exact Module.Flat.of_linearEquiv
    ((Limits.PreservesCoproduct.iso (etaleModuleStalkFunctor B X Λ s) M ≪≫
      ModuleCat.coprodIsoDirectSum
        fun a => (etaleModuleStalkFunctor B X Λ s).obj (M a)).toLinearEquiv)

end Alpha1

/-! ### (α2) The stalk of `j_{U!}Λ` -/

section Alpha2

/-- Products indexed by a type of size `u` exist in `Λ`-modules at the universe level of
`AlgebraicGeometry.moduleShriekConstant`. -/
private theorem hasProducts_moduleCat : HasProducts.{u} (ModuleCat.{max (u + 1) r w} Λ) :=
  fun _ => ModuleCat.hasLimitsOfShape

/-- **The skyscraper sheaf functor at a geometric point is surjective on sections.** Its
sections over an object of the small étale site are a product of copies of the value, indexed
by the lifts of the geometric point. -/
public theorem epi_skyscraperSheafFunctor_map_app
    [HasLimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r w} Λ)] (s : GeometricPoint X.obj)
    (U : (SmallEtale B X.obj X.property)ᵒᵖ)
    {N N' : ModuleCat.{max (u + 1) r w} Λ} (e : N ⟶ N') [Epi e] :
    Epi ((((geometricSitePoint B X s).skyscraperSheafFunctor
      (A := ModuleCat.{max (u + 1) r w} Λ)).map e).hom.app U) := by
  have := hasProducts_moduleCat.{u, w, r} Λ
  exact ModuleCat.epi_piMap_const.{u, max (u + 1) r w, r} e

/-- `AlgebraicGeometry.moduleShriekConstantSectionEquiv` is natural in the target sheaf: it is
the component of the natural isomorphism
`AlgebraicGeometry.moduleShriekConstantCoyonedaIso`. -/
public theorem moduleShriekConstantSectionEquiv_naturality (U : SmallEtale B X.1 X.property)
    {F G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r w} Λ)}
    (α : F ⟶ G) (φ : moduleShriekConstant.{u, r, w} B X Λ U ⟶ F) :
    moduleShriekConstantSectionEquiv.{u, r, w} B X Λ U G (φ ≫ α) =
      α.hom.app (Opposite.op U)
        (moduleShriekConstantSectionEquiv.{u, r, w} B X Λ U F φ) := by
  simpa [moduleShriekConstantSectionEquiv] using
    congr($((moduleShriekConstantCoyonedaIso.{u, r, w} B X Λ U).hom.naturality α) φ)

/-- **The étale module stalk of `j_{U!}\underline{Λ}` is a projective object of `Λ`-modules**,
for an arbitrary étale object `U` and with no hypothesis on `X`.

Maps out of `j_{U!}\underline{Λ}` are sections over `U`
(`AlgebraicGeometry.moduleShriekConstantCoyonedaIso`), and the stalk at `s` is left adjoint to
the skyscraper at `s` (`AlgebraicGeometry.etaleStalkSkyscraperAdjunction`), so maps out of the
stalk into `N` are the sections of the skyscraper over `U`, i.e. the product of copies of `N`
indexed by the lifts of `s` to `U`.  A product of surjections is surjective, so the lifting
property holds. -/
public theorem projective_etaleModuleStalk_moduleShriekConstant
    [HasColimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r w} Λ)]
    [HasLimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r w} Λ)]
    (s : GeometricPoint X.obj) (U : SmallEtale B X.1 X.property) :
    Projective ((etaleModuleStalkFunctor B X Λ s).obj
      (moduleShriekConstant.{u, r, w} B X Λ U)) := by
  have := hasProducts_moduleCat.{u, w, r} Λ
  show Projective (((geometricSitePoint B X s).sheafFiber
    (A := ModuleCat.{max (u + 1) r w} Λ)).obj (moduleShriekConstant.{u, r, w} B X Λ U))
  have adj := (geometricSitePoint B X s).skyscraperSheafAdjunction
    (A := ModuleCat.{max (u + 1) r w} Λ)
  constructor
  intro E Y f e he
  obtain ⟨τ, hτ⟩ := (ModuleCat.epi_iff_surjective _).1
    (epi_skyscraperSheafFunctor_map_app B X Λ s (Opposite.op U) e)
    (moduleShriekConstantSectionEquiv.{u, r, w} B X Λ U _
      (adj.homEquiv (moduleShriekConstant.{u, r, w} B X Λ U) Y f))
  refine ⟨(adj.homEquiv (moduleShriekConstant.{u, r, w} B X Λ U) E).symm
    ((moduleShriekConstantSectionEquiv.{u, r, w} B X Λ U _).symm τ), ?_⟩
  apply (adj.homEquiv (moduleShriekConstant.{u, r, w} B X Λ U) Y).injective
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply (moduleShriekConstantSectionEquiv.{u, r, w} B X Λ U _).injective
  rwa [moduleShriekConstantSectionEquiv_naturality, Equiv.apply_symm_apply]

/-- **The étale module stalk of `j_{U!}\underline{Λ}` is a flat `Λ`-module**, for an arbitrary
étale object `U` and with no hypothesis on `X`: it is projective by
`AlgebraicGeometry.projective_etaleModuleStalk_moduleShriekConstant`. -/
public theorem flat_etaleModuleStalk_moduleShriekConstant
    [HasColimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r w} Λ)]
    [HasLimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r w} Λ)]
    (s : GeometricPoint X.obj) (U : SmallEtale B X.1 X.property) :
    Module.Flat Λ ((etaleModuleStalkFunctor B X Λ s).obj
      (moduleShriekConstant.{u, r, w} B X Λ U)) :=
  have := projective_etaleModuleStalk_moduleShriekConstant B X Λ s U
  have : Module.Projective Λ ((etaleModuleStalkFunctor B X Λ s).obj
    (moduleShriekConstant.{u, r, w} B X Λ U)) := inferInstance
  Module.Flat.of_projective

end Alpha2

/-! ### The goal -/

section Goal

/-- Limits indexed by a category of size `u` exist in `Λ`-modules at the module universe of
`AlgebraicGeometry.moduleShriekConstant`; this is what the skyscraper sheaf asks for, and it
needs no hypothesis. -/
private theorem hasLimitsOfSizeModuleShriek :
    HasLimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r w} Λ) :=
  ModuleCat.hasLimitsOfSize.{u, u, max (u + 1) r w, r}

attribute [local instance] hasLimitsOfSizeModuleShriek
  SmallEtale.hasSheafify_moduleCat
  SheafOfModules.hasSheafify_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

variable [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r w} Λ)]
  [HasColimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r w} Λ)]

omit [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r w} Λ)] in
/-- **An arbitrary, possibly infinite, coproduct of the generators `j_{U!}\underline{Λ}` is flat
over the constant coefficient ring sheaf**, with no hypothesis on `X`. -/
public theorem isFlat_sigma_moduleShriekConstant
    {A : Type max (u + 1) r w} (U : A → SmallEtale B X.obj X.property) :
    Stacks.SheafOfModules.IsFlat.{u, u + 1, max (u + 1) r w, max (u + 1) r w}
      (moduleSheafOverConstantCoefficients.{u, max (u + 1) r w, r} B X Λ
        (∐ fun a => moduleShriekConstant.{u, r, w} B X Λ (U a))) :=
  Stacks.isFlat_of_forall_isFlatModuleStalk
    (constantCoefficientSheaf.{u, max (u + 1) r w, r} B X Λ) _
    (fun x : ↥X.obj => (geometricSitePoint B X (.ofPoint X.obj x)).ulift.{max (u + 1) r w})
    (isConservativeFamilyOfPoints_uliftGeometricSitePoint.{u, max (u + 1) r w, r} B X)
    (fun _x => isFlatModuleStalk_of_flat_etaleModuleStalk.{u, max (u + 1) r w, r} B X Λ _ _
      (flat_etaleModuleStalk_sigma B X Λ _ _
        fun a => flat_etaleModuleStalk_moduleShriekConstant B X Λ _ (U a)))

end Goal

/-! ### Stability under inverse image -/

section Pullback

variable [HasColimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r w} Λ)]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- **Flat étale stalks are stable under small étale inverse image.** The stalk of `f^{-1}F` at a
geometric point is the stalk of `F` at its image, by
`AlgebraicGeometry.smallEtalePullbackSheafFiberIso`, which is Stacks 03Q1 at these coefficients.
No hypothesis on either scheme. -/
public theorem flat_etaleModuleStalk_smallEtaleSheafPullback
    {S T : B.Scheme} (f : T ⟶ S)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) r w} Λ))
    (hF : ∀ s : GeometricPoint S.obj,
      Module.Flat Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r w, r} B S Λ s).obj F))
    (x : GeometricPoint T.obj) :
    Module.Flat Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r w, r} B T Λ x).obj
      (((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) r w} Λ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).obj F)) := by
  have := hasProducts_moduleCat.{u, w, r} Λ
  have : Module.Flat Λ (((geometricPointSitePoint B S.obj S.property
      (x.map (B.inclusion.map f))).sheafFiber
        (A := ModuleCat.{max (u + 1) r w} Λ)).obj F) :=
    hF (x.map (B.inclusion.map f))
  exact Module.Flat.of_linearEquiv
    ((smallEtalePullbackSheafFiberIso B f x (ModuleCat.{max (u + 1) r w} Λ)).app F).toLinearEquiv

end Pullback

/-! ### Bounded above complexes with flat étale stalks -/

section Resolution

attribute [local instance] HasDerivedCategory.standard SmallEtale.hasSheafify_moduleCat

variable [HasColimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r} Λ)]

/-- **Every sheaf of `Λ`-modules on the small étale site is a quotient of one with flat étale
stalks**, with no hypothesis on `X`: it is a quotient of a direct sum of the generators
`j_{U!}\underline{Λ}` at affine étale objects, by Stacks 093B (2)
(`AlgebraicGeometry.exists_epi_sigma_moduleShriekConstant_affine`), each of which has flat étale
stalks, and flat étale stalks pass to an arbitrary coproduct. -/
public theorem exists_epi_flat_etaleModuleStalk
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ)) :
    ∃ (Y : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max (u + 1) r} Λ))
      (_ : ∀ s : GeometricPoint X.obj,
        Module.Flat Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).obj Y))
      (p : Y ⟶ F), Epi p := by
  have : HasLimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r} Λ) :=
    ModuleCat.hasLimitsOfSize.{u, u, max (u + 1) r, r}
  obtain ⟨A, U, _, p, hp⟩ := exists_epi_sigma_moduleShriekConstant_affine B X Λ F
  exact ⟨_, fun s => flat_etaleModuleStalk_sigma.{u, max (u + 1) r, r} B X Λ _ s
    (fun a => flat_etaleModuleStalk_moduleShriekConstant.{u, r, r} B X Λ s (U a)), p, hp⟩

/-- **Every bounded above object of the derived category of small étale sheaves of `Λ`-modules is
represented by a bounded above complex of sheaves with flat étale stalks**, with no hypothesis on
`X`.

This is Stacks 05T7, `CochainComplex.exists_quasiIso_prop`, for the class of sheaves with flat
étale stalks: that class contains the zero object, because the stalk functor is additive and a
subsingleton module is flat, and every sheaf is a quotient of a member of it by
`AlgebraicGeometry.exists_epi_flat_etaleModuleStalk`. The bound is preserved: the resolution the
tag produces vanishes in the same degrees.

It is what makes `Stacks.EtaleCohomology.IsDerivedTensorOnFlatComplexes` applicable over an
arbitrary scheme, through
`AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_flat_etaleModuleStalk`. -/
public theorem exists_isStrictlyLE_flat_etaleModuleStalk_of_isLE
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ))) (a : ℤ) (hK : K.IsLE a) :
    ∃ (G : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) r} Λ)) ℤ) (_ : CochainComplex.IsStrictlyLE G a),
      (∀ (i : ℤ) (s : GeometricPoint X.obj),
          Module.Flat Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).obj (G.X i))) ∧
        Nonempty (DerivedCategory.Q.obj G ≅ K) := by
  classical
  set P : ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ)) :=
    fun F => ∀ s : GeometricPoint X.obj,
      Module.Flat Λ ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).obj F)
  have hzero : P.ContainsZero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ))
    refine ⟨⟨Z, hZ, fun s => ?_⟩⟩
    have : Subsingleton ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).obj Z) :=
      ModuleCat.isZero_iff_subsingleton.mp
        ((etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s).map_isZero hZ)
    infer_instance
  obtain ⟨A, hA, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE a
  obtain ⟨L, f, -, hf, hPL, hLE⟩ :=
    (CochainComplex.exists_quasiIso_prop P (exists_epi_flat_etaleModuleStalk B X Λ) a).1 A
  exact ⟨L, hLE, hPL, ⟨asIso (DerivedCategory.Q.map f) ≪≫ e.symm⟩⟩

end Resolution

end AlgebraicGeometry

end
