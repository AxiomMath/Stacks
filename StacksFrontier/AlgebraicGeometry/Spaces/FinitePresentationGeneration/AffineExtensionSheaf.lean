module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.AffineExtensionAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAffineComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardAffineGeometry
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenSchemeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits

/-!
# Sheaf-theoretic inputs for the affine extension of modules of finite presentation

Auxiliary constructions for
`AlgebraicGeometry.Space.exists_isFinitePresentation_extension_of_isAffineSpace`:

* the chart `AlgebraicGeometry.Space.AffineExtension.affineChart` of an affine algebraic space
  given by an isomorphism with a representable presheaf, which is terminal in the small étale
  site, and the global section `AlgebraicGeometry.Space.AffineExtension.sectionsOfTerminal`
  determined by a section over a terminal chart;
* the evaluation of a morphism out of a free module on the sections given by finitely supported
  families (`AlgebraicGeometry.Space.AffineExtension.freeHomEquiv_symm_app_freeSectionsMap`), and
  the naturality of that description
  (`AlgebraicGeometry.Space.AffineExtension.map_freeSectionsMap`);
* a criterion for a morphism of modules to be invertible: bijectivity on the sections over the
  affine charts with a map to a chart covering the space
  (`AlgebraicGeometry.Space.AffineExtension.isIso_of_bijective_app_of_coversTop`);
* quasi-compactness of a morphism from a quasi-compact algebraic space to an affine one
  (`AlgebraicGeometry.Space.AffineExtension.isQuasiCompact_of_isAffineSpace`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.AffineExtension

/-! ### Free modules on a general site -/

section Unit

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- The morphism from the unit module attached to a global section multiplies that section by
a scalar. -/
theorem unitHomEquiv_symm_val_app (M : SheafOfModules.{u} R) (s : M.sections) (W : Cᵒᵖ)
    (b : R.obj.obj W) : (M.unitHomEquiv.symm s).val.app W b = b • s.eval W := by
  have h3 : (M.unitHomEquiv.symm s).val.app W (1 : R.obj.obj W) = s.eval W := by
    rw [← SheafOfModules.unitHomEquiv_apply_coe, Equiv.apply_symm_apply]
  calc _ = ((M.unitHomEquiv.symm s).val.app W).hom (b • (1 : R.obj.obj W)) := by
        rw [smul_eq_mul, mul_one]
    _ = _ := (((M.unitHomEquiv.symm s).val.app W).hom.map_smul b (1 : R.obj.obj W)).trans
        (congrArg (b • ·) h3)

end Unit

section Free

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A morphism out of a free module, given by a family of global sections, evaluated on the
section of the free module attached to a finitely supported family of scalars. -/
theorem freeHomEquiv_symm_app_freeSectionsMap (M : SheafOfModules.{u} R) {I : Type u}
    (s : I → M.sections) (W : Cᵒᵖ) (c : I →₀ R.obj.obj W) :
    (M.freeHomEquiv.symm s).val.app W (Stacks.Sites.freeSectionsMap (R := R) I W c) =
      Finsupp.linearCombination (R.obj.obj W) (fun i => (s i).eval W) c := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add]
  | single i b =>
    rw [Stacks.Sites.freeSectionsMap_single, Finsupp.linearCombination_single]
    have h : SheafOfModules.ιFree i ≫ M.freeHomEquiv.symm s = M.unitHomEquiv.symm (s i) := by
      rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, Equiv.apply_symm_apply]
    have h' := congrArg (fun f => f.val.app W b) h
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app] at h'
    rwa [unitHomEquiv_symm_val_app] at h'

/-- The description of the sections of a free module by finitely supported families of scalars
is compatible with restriction. -/
theorem map_freeSectionsMap {I : Type u} {W W' : Cᵒᵖ} (f : W ⟶ W') (c : I →₀ R.obj.obj W) :
    (SheafOfModules.free (R := R) I).val.map f (Stacks.Sites.freeSectionsMap (R := R) I W c) =
      Stacks.Sites.freeSectionsMap (R := R) I W'
        (Finsupp.mapRange (R.obj.map f) (map_zero _) c) := by
  induction c using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, map_zero, Finsupp.mapRange_zero, map_zero]
    rfl
  | add f₁ g₁ hf hg =>
    rw [map_add, map_add, hf, hg, Finsupp.mapRange_add (map_add _), map_add]
    rfl
  | single i b =>
    rw [Stacks.Sites.freeSectionsMap_single, Finsupp.mapRange_single,
      Stacks.Sites.freeSectionsMap_single]
    exact (PresheafOfModules.naturality_apply (SheafOfModules.ιFree (R := R) i).val f b).symm

end Free

/-! ### Global sections from a terminal chart -/

section Terminal

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}} {T₀ : C} (hT₀ : IsTerminal T₀)
  (M : PresheafOfModules.{u} R)

/-- The global section of a presheaf of modules determined by its value at a terminal object. -/
def sectionsOfTerminal (y : M.obj (op T₀)) : M.sections :=
  PresheafOfModules.sectionsMk (fun W => M.map (hT₀.from W.unop).op y) (fun W W' f => by
    rw [← PresheafOfModules.map_comp_apply,
      show (hT₀.from W.unop).op ≫ f = (hT₀.from W'.unop).op from
        Quiver.Hom.unop_inj (hT₀.hom_ext _ _)])

/-- The value of `sectionsOfTerminal` at a chart is the restriction along the morphism to the
terminal object. -/
theorem sectionsOfTerminal_val (y : M.obj (op T₀)) (W : C) :
    (sectionsOfTerminal hT₀ M y).val (op W) = M.map (hT₀.from W).op y := rfl

/-- The value of `sectionsOfTerminal` at the terminal object is the given section. -/
theorem sectionsOfTerminal_val_self (y : M.obj (op T₀)) :
    (sectionsOfTerminal hT₀ M y).val (op T₀) = y := by
  rw [sectionsOfTerminal_val, hT₀.hom_ext (hT₀.from T₀) (𝟙 T₀)]
  exact PresheafOfModules.map_id_apply M _ y

/-- A global section is determined by its value at a terminal object. -/
theorem sectionsOfTerminal_eval (s : M.sections) :
    sectionsOfTerminal hT₀ M (s.val (op T₀)) = s :=
  PresheafOfModules.sections_ext _ _ fun W => s.property (hT₀.from W.unop).op

end Terminal

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The terminal chart of an affine algebraic space -/

section AffineChart

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : BigFppfOver B S hS} (e : X ≅ yoneda.obj T)

/-- The étale chart of a presheaf given by the inverse of an isomorphism with a representable
presheaf. -/
def affineChart : SmallEtale B S hS X :=
  ⟨CostructuredArrow.mk e.inv, presheaf_etale_of_isEtale B S hS (isEtale_of_isIso B S hS e.inv)⟩

/-- The chart `affineChart` is terminal in the small étale site. -/
def isTerminal_affineChart : IsTerminal (affineChart B S hS e) := by
  have hy (V : BigFppfOver B S hS) (ψ : yoneda.obj V ⟶ yoneda.obj T) :
      yoneda.map (yonedaEquiv ψ) = ψ :=
    yonedaEquiv.injective (yonedaEquiv_yoneda_map _)
  have hmap (V : SmallEtale B S hS X) (g : V.obj.left ⟶ T) :
      yoneda.map g ≫ e.inv = V.obj.hom ↔ g = yonedaEquiv (V.obj.hom ≫ e.hom) := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← h, Category.assoc, Iso.inv_hom_id, Category.comp_id, yonedaEquiv_yoneda_map]
    · rw [h, hy, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact IsTerminal.ofUniqueHom
    (fun V => ObjectProperty.homMk (show V.obj ⟶ (affineChart B S hS e).obj from
      CostructuredArrow.homMk (yonedaEquiv (V.obj.hom ≫ e.hom)) ((hmap V _).2 rfl))) fun V m =>
    ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
      ((hmap V m.hom.left).1 (CostructuredArrow.w m.hom)))

end AffineChart

/-! ### Isomorphisms detected on affine charts over a covering chart -/

section IsoCriterion

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- The sieve of the morphisms to `U` factoring through an affine chart with a morphism to
`T₁`. -/
def affineOverSieve (T₁ : SmallEtale B S hS X) (U : SmallEtale B S hS X) : Sieve U where
  arrows W g := ∃ (A : SmallEtale B S hS X) (a : W ⟶ A) (b : A ⟶ U),
    IsAffine ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).obj A) ∧
      Nonempty (A ⟶ T₁) ∧ a ≫ b = g
  downward_closed := by
    rintro W W' g ⟨A, a, b, hA, hT, rfl⟩ h
    exact ⟨A, h ≫ a, b, hA, hT, by simp⟩

include hX in
/-- If a chart `T₁` covers `X`, the sieve `affineOverSieve` is covering. -/
theorem affineOverSieve_mem {T₁ : SmallEtale B S hS X}
    (hT₁ : (SmallEtale.topology B S hS X).CoversTop (fun _ : PUnit.{u + 2} => T₁))
    (U : SmallEtale B S hS X) :
    affineOverSieve B S hS T₁ U ∈ SmallEtale.topology B S hS X U := by
  refine (SmallEtale.topology B S hS X).transitive (hT₁ U) _ fun W g hg => ?_
  obtain ⟨-, ⟨t⟩⟩ := (Sieve.mem_ofObjects_iff _ g).1 hg
  refine (SmallEtale.topology B S hS X).superset_covering ?_
    ((SmallEtale.isCoverDense_affineEtaleInclusion B S hS X hX).is_cover W)
  rintro W' h ⟨⟨A, lift, map, fac⟩⟩
  exact ⟨(AffineEtale.inclusion B S hS X).obj A, lift, map ≫ g, A.property, ⟨map ≫ t⟩,
    by rw [← Category.assoc, fac]⟩

include hX in
/-- **A morphism of modules bijective on the sections over the affine charts over a covering
chart is an isomorphism.** -/
theorem isIso_of_bijective_app_of_coversTop {T₁ : SmallEtale B S hS X}
    (hT₁ : (SmallEtale.topology B S hS X).CoversTop (fun _ : PUnit.{u + 2} => T₁))
    {M N : Modules.{u, u} B S hS X hX} (φ : M ⟶ N)
    (h : ∀ A : SmallEtale B S hS X,
      IsAffine ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).obj A) →
        Nonempty (A ⟶ T₁) → Function.Bijective (φ.val.app (op A))) :
    IsIso φ := by
  have hinj : PresheafOfModules.IsLocallyInjective (smallEtaleRingedSite B S hS X hX).J
      φ.val := by
    refine ⟨fun {U} x y hxy => ?_⟩
    refine (SmallEtale.topology B S hS X).superset_covering ?_
      (affineOverSieve_mem B S hS hX hT₁ U.unop)
    rintro W g ⟨A, a, b, hA, hT, rfl⟩
    refine (Presheaf.equalizerSieve x y).downward_closed ?_ a
    refine (h A hA hT).1 ?_
    exact (NatTrans.naturality_apply ((PresheafOfModules.toPresheaf _).map φ.val) b.op x).trans
      ((congrArg (((PresheafOfModules.toPresheaf _).obj N.val).map b.op) hxy).trans
        (NatTrans.naturality_apply ((PresheafOfModules.toPresheaf _).map φ.val) b.op y).symm)
  have hsurj : PresheafOfModules.IsLocallySurjective (smallEtaleRingedSite B S hS X hX).J
      φ.val := by
    refine ⟨fun {U} s => ?_⟩
    refine (SmallEtale.topology B S hS X).superset_covering ?_
      (affineOverSieve_mem B S hS hX hT₁ U)
    rintro W g ⟨A, a, b, hA, hT, rfl⟩
    refine (Presheaf.imageSieve _ s).downward_closed ?_ a
    exact (h A hA hT).2 (((PresheafOfModules.toPresheaf _).obj N.val).map b.op s)
  exact Stacks.SheafOfModules.isIso_of_isLocallyBijective φ

end IsoCriterion

/-! ### The two renderings of finite presentation -/

/-- A module of finite presentation in the sense of Mathlib on an algebraic space is of finite
presentation on the site: restrict the finite presentations of a `QuasicoherentData` to the
charts mapping to its members. -/
theorem isFinitePresentationOnSite_of_isFinitePresentation {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (M : Modules.{u, u} B S hS X hX)
    (hM : M.IsFinitePresentation) : SheafOfModules.IsFinitePresentationOnSite M := by
  classical
  obtain ⟨D, hD⟩ := hM.exists_quasicoherentData
  refine ⟨fun U => ⟨{p : Σ W : (smallEtaleRingedSite B S hS X hX).C, (W ⟶ U) //
    ∃ i, Nonempty (p.1 ⟶ D.X i)},
    fun p => p.1.1, fun p => p.1.2, ?_, fun p => ?_⟩⟩
  · refine (SmallEtale.topology B S hS X).superset_covering ?_ (D.coversTop U)
    intro W g hg
    obtain ⟨i, ⟨t⟩⟩ := (Sieve.mem_ofObjects_iff _ _).1 hg
    exact Sieve.ofArrows_mk (fun p : {p : Σ W : (smallEtaleRingedSite B S hS X hX).C, (W ⟶ U) //
      ∃ i, Nonempty (p.1 ⟶ D.X i)} => p.1.1) (fun p => p.1.2) ⟨⟨W, g⟩, i, ⟨t⟩⟩
  · obtain ⟨i, ⟨t⟩⟩ := p.2
    have := hD.isFinite_presentation i
    have : ∀ Z : (smallEtaleRingedSite B S hS X hX).C,
        HasSheafify ((smallEtaleRingedSite B S hS X hX).J.over Z) AddCommGrpCat.{u} :=
      fun _ => AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
    have : ∀ (V W : (smallEtaleRingedSite B S hS X hX).C) (f : W ⟶ V),
        PreservesColimitsOfSize.{u, u} (SheafOfModules.overMap.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O) f) :=
      fun _ _ f => Stacks.SheafOfModules.overMap_preservesColimits _ f
    exact SheafOfModules.HasFiniteGlobalPresentation.of_presentation'
      (Stacks.SheafOfModules.LocalKernel.presentationOver (M := M) t (D.presentation i))
      inferInstance

/-! ### Quasi-compactness of morphisms to affine spaces -/

set_option synthInstance.maxHeartbeats 400000 in
/-- A morphism from a quasi-compact algebraic space to a representable presheaf with affine
underlying scheme is quasi-compact. -/
theorem isQuasiCompact_to_yoneda {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXqc : IsQuasiCompactSpace B S hS X)
    {T : BigFppfOver B S hS} (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (s : X ⟶ yoneda.obj T) : IsQuasiCompact B S hS s := by
  obtain ⟨W, a, hWaff, hasurj, -⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X hX).mp hXqc
  refine isQuasiCompact_of_forall_isQuasiCompactSpace_pullback B S hS s fun U hU p => ?_
  have h' : IsQuasiCompactSpace B S hS (pullback (a ≫ s) p) :=
    isQuasiCompactSpace_of_iso B S hS (pullbackSymmetry p (a ≫ s))
      (isQuasiCompact_yoneda_of_isAffine B S hS (a ≫ s) hWaff hT (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U) (isQuasiCompact_yoneda_of_compact B S hS U hU) p)
  exact isQuasiCompactSpace_of_iso B S hS (pullbackSymmetry s p)
    (isQuasiCompactSpace_pullback_of_isSurjective B S hS p s a
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS T) hX
      (isAlgebraicSpace_yoneda B S hS W) (isSurjective_of_presheafSurjective B S hS a hasurj)
      rfl h')

set_option synthInstance.maxHeartbeats 400000 in
/-- A morphism from a quasi-compact algebraic space to an affine algebraic space is
quasi-compact. -/
theorem isQuasiCompact_of_isAffineSpace {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXqc : IsQuasiCompactSpace B S hS X)
    (hY : IsAffineSpace B S hS Y) (f : X ⟶ Y) : IsQuasiCompact B S hS f := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hY
  exact isQuasiCompact_of_comp_mono B S hS f e.hom
    (isQuasiCompact_to_yoneda B S hS hX hXqc hT (f ≫ e.hom))

end AlgebraicGeometry.Space.AffineExtension

end
