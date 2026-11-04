module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedCoherator.Induction
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.InverseLimitOfAcyclicTower
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationLevelHomology

/-!
# The coherator of an algebraic space has bounded cohomological dimension

Let `X` be a quasi-compact and quasi-separated algebraic space with coherator
`DQ_X : D(𝒪_X) ⥤ D_QCoh(𝒪_X)`. [Stacks, Tag 0CSS] says that there is an integer `N` such that,
whenever `K` in `D(𝒪_X)` has `H^i(U, K) = 0` for all affine `U` étale over `X` and all `i > b`,
the cohomology sheaves of `DQ_X(K)` vanish in degrees `> b + N`. This module proves this bound,
granted the affine case; the hypercohomology `H^i(U, K)` is read on a K-injective representative
`I` of `K`, as the cohomology of the complex of sections `Γ(U, I)`.

## Main definitions

* `AlgebraicGeometry.Space.SectionsAmplitudeLE Y b I`: the complexes of sections of `I` over the
  affine étale charts of `Y` have no cohomology above degree `b`.
* `AlgebraicGeometry.Space.SpaceCohomologyVanishesAbove X c K`: `H^i(K) = 0` for `i > c`.

## Main results

* `AlgebraicGeometry.Space.coherator_obj_iso_of_decomposition`: a coreflection is unique, the
  first object of any decomposition triangle of `K` being `ι(DQ_X K)`.
* `AlgebraicGeometry.Space.sectionsAmplitudeLE_complexEtalePullback`: the amplitude passes to
  étale restrictions.
* `AlgebraicGeometry.Space.exists_coheratorBound_of_affineCase`: the one-sided bound of
  [Stacks, Tag 0CSS], granted the affine case.
* `AlgebraicGeometry.Space.exists_coheratorBound_twoSided_of_affineCase`: the two-sided bound,
  granted the affine case.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.PushforwardMayerVietoris

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] isGrothendieckAbelian_modules enoughInjectives_modules
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The cohomology sheaves `H^i(K)` vanish for `i > c`. -/
abbrev SpaceCohomologyVanishesAbove (X : AlgebraicSpaces B S hS) (c : ℤ)
    (K : spaceDerivedCategory B S hS X) : Prop :=
  ∀ i : ℤ, c < i → IsZero ((spaceDerivedHomology B S hS X i).obj K)

/-- The complex of sections `Γ(V, I)` of a complex of `𝒪_Y`-modules over an étale chart `V`. -/
abbrev sectionsComplex (Y : AlgebraicSpaces B S hS) (V : SmallEtale B S hS Y.1) :
    CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  (Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
    (smallEtaleRingedSite B S hS Y.1 Y.2) V).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **Affine amplitude at most `b`.** The complexes of sections of `I` over the affine étale
charts of `Y` have no cohomology in degrees `> b`. For a K-injective `I` these are the
hypercohomology groups `H^i(V, I)` over the affine charts `V`. -/
def SectionsAmplitudeLE (Y : AlgebraicSpaces B S hS) (b : ℤ)
    (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) : Prop :=
  ∀ V : SmallEtale B S hS Y.1, IsAffineChart B S hS Y.1 V → ∀ i : ℤ, b < i →
    IsZero (((sectionsComplex B S hS Y V).obj I).homology i)

variable {B S hS}

/-- **The amplitude passes to étale restrictions**: if `I` has affine amplitude at most `b` on
`W` and `j : T ⟶ W` is étale, then `j^*I` has affine amplitude at most `b` on `T`. -/
theorem sectionsAmplitudeLE_complexEtalePullback {T W : AlgebraicSpaces B S hS} (j : T ⟶ W)
    (hj : IsEtale B S hS j.hom) {b : ℤ} {I : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ}
    (hI : SectionsAmplitudeLE B S hS W b I) :
    SectionsAmplitudeLE B S hS T b ((complexEtalePullback B S hS j hj).obj I) := by
  intro V hV i hi
  have e : (sectionsComplex B S hS T V).obj ((complexEtalePullback B S hS j hj).obj I) ≅
      (sectionsComplex B S hS W ((smallEtalePostcomp B S hS j hj).obj V)).obj I :=
    HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun _ _ _ => rfl)
  exact (hI ((smallEtalePostcomp B S hS j hj).obj V) hV i hi).of_iso
    (HomologicalComplex.homologyMapIso e i)

/-! ### Uniqueness of coreflections -/

/-- Two morphisms from `ι F` to `ι (DQ K)` agreeing after composition with the counit are equal. -/
private theorem eq_of_comp_counit_eq {C : Type*} [Category C] (P : ObjectProperty C)
    {DQ : C ⥤ P.FullSubcategory} (adj : P.ι ⊣ DQ) {K : C} {F : P.FullSubcategory}
    {f g : P.ι.obj F ⟶ P.ι.obj (DQ.obj K)}
    (h : f ≫ adj.counit.app K = g ≫ adj.counit.app K) : f = g := by
  obtain ⟨f', rfl⟩ := P.fullyFaithfulι.map_surjective f
  obtain ⟨g', rfl⟩ := P.fullyFaithfulι.map_surjective g
  have : (adj.homEquiv _ _).symm f' = (adj.homEquiv _ _).symm g' := by
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    exact h
  rw [(adj.homEquiv _ _).symm.injective this]

section Uniqueness

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- If the third object of a distinguished triangle is right orthogonal to a shift-stable `P`,
then composition with the first morphism is bijective on morphisms out of objects of `P`. -/
theorem bijective_comp_mor₁_of_rightOrthogonal (P : ObjectProperty C) [P.IsStableUnderShift ℤ]
    {T : Triangle C} (hT : T ∈ distTriang C) (hT₃ : P.rightOrthogonal T.obj₃) {W : C}
    (hW : P W) : Function.Bijective fun g : W ⟶ T.obj₁ ↦ g ≫ T.mor₁ := by
  have hker : ∀ g : W ⟶ T.obj₁, g ≫ T.mor₁ = 0 → g = 0 := by
    intro g hg
    obtain ⟨g', hg'⟩ := Triangle.coyoneda_exact₂ T.invRotate (inv_rot_of_distTriang T hT) g hg
    have h₃ : P.rightOrthogonal (T.obj₃⟦(-1 : ℤ)⟧) := P.rightOrthogonal.le_shift (-1) _ hT₃
    have hg'' : g' = 0 := h₃ g' hW
    rw [hg', hg'']
    exact zero_comp
  refine ⟨fun g₁ g₂ hg ↦ ?_, fun k ↦ ?_⟩
  · have hg' : g₁ ≫ T.mor₁ = g₂ ≫ T.mor₁ := hg
    rw [← sub_eq_zero]
    exact hker _ (by rw [Preadditive.sub_comp, hg', sub_self])
  · obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T hT k (hT₃ (k ≫ T.mor₂) hW)
    exact ⟨g, hg.symm⟩

/-- **A coreflection is unique.** If `E ⟶ K ⟶ Q ⟶ E[1]` is a distinguished triangle with `E` in
`P` and `Q` right orthogonal to `P`, and `DQ` is right adjoint to the inclusion of `P`, then
`ι(DQ K) ≅ E`. -/
theorem coherator_obj_iso_of_decomposition (P : ObjectProperty C) [P.IsStableUnderShift ℤ]
    {DQ : C ⥤ P.FullSubcategory} (adj : P.ι ⊣ DQ) {E K Q : C} {a : E ⟶ K} {b : K ⟶ Q}
    {c : Q ⟶ E⟦(1 : ℤ)⟧} (hT : Triangle.mk a b c ∈ distTriang C) (hE : P E)
    (hQ : P.rightOrthogonal Q) : Nonempty (P.ι.obj (DQ.obj K) ≅ E) := by
  have hbij := fun {W : C} (hW : P W) =>
    bijective_comp_mor₁_of_rightOrthogonal P hT hQ (W := W) hW
  let ε := adj.counit.app K
  obtain ⟨ψ, hψ₀⟩ := (hbij (DQ.obj K).property).2 ε
  have hψ : ψ ≫ a = ε := hψ₀
  let E' : P.FullSubcategory := ⟨E, hE⟩
  let φ : E ⟶ P.ι.obj (DQ.obj K) := P.ι.map (adj.homEquiv E' K a)
  have hφ : φ ≫ ε = a := by
    simpa only [Equiv.symm_apply_apply] using
      (adj.homEquiv_counit (X := E') (Y := K) (g := adj.homEquiv E' K a)).symm
  refine ⟨⟨ψ, φ, ?_, ?_⟩⟩
  · apply eq_of_comp_counit_eq P adj
    rw [Category.assoc, Category.id_comp]
    exact (congrArg (ψ ≫ ·) hφ).trans hψ
  · apply (hbij hE).1
    simp only [Category.assoc, Category.id_comp]
    show φ ≫ ψ ≫ a = a
    rw [hψ, hφ]

end Uniqueness

/-! ### Vanishing of cohomology sheaves along triangles -/

section Vanishing

variable {X : AlgebraicSpaces B S hS}

/-- Cohomology sheaves of `K` vanish above degree `c` if and only if `K` is `≤ c` for the
canonical t-structure. -/
theorem spaceCohomologyVanishesAbove_iff_isLE (c : ℤ) (K : spaceDerivedCategory B S hS X) :
    SpaceCohomologyVanishesAbove B S hS X c K ↔
      @DerivedCategory.IsLE _ _ _ (spaceHasDerivedCategory B S hS X) K c := by
  let := spaceHasDerivedCategory B S hS X
  exact (DerivedCategory.isLE_iff K c).symm

/-- Vanishing of cohomology sheaves above `c` is invariant under isomorphism. -/
theorem SpaceCohomologyVanishesAbove.of_iso {c : ℤ} {K K' : spaceDerivedCategory B S hS X}
    (h : SpaceCohomologyVanishesAbove B S hS X c K) (e : K ≅ K') :
    SpaceCohomologyVanishesAbove B S hS X c K' :=
  fun i hi => (h i hi).of_iso ((spaceDerivedHomology B S hS X i).mapIso e).symm

/-- If cohomology sheaves vanish above `c` and `c ≤ d`, they vanish above `d`. -/
theorem SpaceCohomologyVanishesAbove.mono {c d : ℤ} {K : spaceDerivedCategory B S hS X}
    (h : SpaceCohomologyVanishesAbove B S hS X c K) (hcd : c ≤ d) :
    SpaceCohomologyVanishesAbove B S hS X d K :=
  fun i hi => h i (by omega)

/-- In a distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]`, if `H^i(B) = 0` for `i > c` and
`H^i(C) = 0` for `i > c - 1`, then `H^i(A) = 0` for `i > c`. -/
theorem SpaceCohomologyVanishesAbove.obj₁ {T : Triangle (spaceDerivedCategory B S hS X)}
    (hT : T ∈ distTriang _) {c : ℤ} (h₂ : SpaceCohomologyVanishesAbove B S hS X c T.obj₂)
    (h₃ : SpaceCohomologyVanishesAbove B S hS X (c - 1) T.obj₃) :
    SpaceCohomologyVanishesAbove B S hS X c T.obj₁ := by
  let := spaceHasDerivedCategory B S hS X
  rw [spaceCohomologyVanishesAbove_iff_isLE] at h₂ h₃ ⊢
  have hdist := inv_rot_of_distTriang _ hT
  have := h₃
  have h₃' := DerivedCategory.TStructure.t.isLE_shift T.obj₃ (c - 1) (-1) c (by omega)
  exact DerivedCategory.TStructure.t.isLE₂ _ hdist c h₃' h₂

/-- Vanishing above `c` passes to binary biproducts. -/
theorem SpaceCohomologyVanishesAbove.biprod {A C : spaceDerivedCategory B S hS X} {c : ℤ}
    (hA : SpaceCohomologyVanishesAbove B S hS X c A)
    (hC : SpaceCohomologyVanishesAbove B S hS X c C) :
    SpaceCohomologyVanishesAbove B S hS X c (A ⊞ C) := by
  let := spaceHasDerivedCategory B S hS X
  rw [spaceCohomologyVanishesAbove_iff_isLE] at hA hC ⊢
  exact DerivedCategory.TStructure.t.isLE₂ _ (binaryBiproductTriangle_distinguished A C) c hA hC

end Vanishing

/-! ### The bound -/

section Bound

variable {X : AlgebraicSpaces B S hS}
  (DQ : spaceDerivedCategory B S hS X ⥤ (spaceQuasicoherentProp B S hS X).FullSubcategory)

/-- For a morphism `j : Y ⟶ X` from a presheaf `Y`: there is an integer `N` such that, if `Y` is
an algebraic space and `j` is étale, then for every K-injective complex `I` of `𝒪_Y`-modules whose
complexes of sections over the affine étale charts of `Y` have no cohomology above degree `b`,
`ι(DQ_X(j_*I))` has no cohomology sheaves above degree `b + N`. -/
def CoheratorBoundPushforward (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (j : Y ⟶ X.1) : Prop :=
  ∃ N : ℤ, ∀ (hY : IsAlgebraicSpace B S hS Y), IsEtale B S hS j →
    ∀ (b : ℤ) (I : CochainComplex (Modules.{u, u} B S hS Y hY) ℤ), I.IsKInjective →
      SectionsAmplitudeLE B S hS ⟨Y, hY⟩ b I →
        SpaceCohomologyVanishesAbove B S hS X (b + N)
          ((spaceQuasicoherentProp B S hS X).ι.obj (DQ.obj ((spaceDerivedQ B S hS X).obj
            ((complexPushforward B S hS
              (ObjectProperty.homMk j : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj I))))

variable {DQ} (adj : (spaceQuasicoherentProp B S hS X).ι ⊣ DQ) [DQ.CommShift ℤ]
  [adj.IsTriangulated]

include adj in
/-- The composite of the coherator `DQ` with the inclusion of quasi-coherent objects is a
triangulated functor. -/
theorem isTriangulated_coherator_comp_ι :
    (DQ ⋙ (spaceQuasicoherentProp B S hS X).ι).IsTriangulated :=
  have : DQ.IsTriangulated := inferInstance
  inferInstance

/-- The direct image along `jW` of `jT,* jT^* I` is the direct image along `jT ≫ jW` of the
K-injective complex `jT^* I`. -/
def spaceDerivedPushforwardRestrictPushIso {W T : AlgebraicSpaces B S hS}
    (jW : W ⟶ X) (jT : T ⟶ W) (hjT : IsEtale B S hS jT.hom)
    (I : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ) [I.IsKInjective] :
    (spaceDerivedPushforward B S hS jW).obj
      ((spaceDerivedQ B S hS W).obj ((complexPushforward B S hS jT).obj
        ((complexEtalePullback B S hS jT hjT).obj I))) ≅
      (spaceDerivedQ B S hS X).obj ((complexPushforward B S hS
        (ObjectProperty.homMk (jT.hom ≫ jW.hom) : (⟨T.1, T.2⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj
          ((complexEtalePullback B S hS jT hjT).obj I)) :=
  haveI := isKInjective_complexEtalePullback jT hjT I
  haveI := isKInjective_complexPushforward_of_isEtale jT hjT
    ((complexEtalePullback B S hS jT hjT).obj I)
  spaceDerivedPushforwardQIso B S hS jW _ inferInstance ≪≫ (spaceDerivedQ B S hS X).mapIso
    ((NatIso.mapHomologicalComplex (modulePushforwardCompIso B S hS jT jW)
      (ComplexShape.up ℤ)).app ((complexEtalePullback B S hS jT hjT).obj I))

omit [DQ.CommShift ℤ] in
/-- The bound for `jT ≫ jW` gives the same bound for the coherator of `RjW_*(jT,* jT^* I)`. -/
theorem coheratorBound_restrictPush {W T : AlgebraicSpaces B S hS}
    (jW : W ⟶ X) (hjW : IsEtale B S hS jW.hom) (jT : T ⟶ W) (hjT : IsEtale B S hS jT.hom)
    {N : ℤ} (hT : ∀ (hY : IsAlgebraicSpace B S hS T.1), IsEtale B S hS (jT.hom ≫ jW.hom) →
      ∀ (b : ℤ) (I : CochainComplex (Modules.{u, u} B S hS T.1 hY) ℤ), I.IsKInjective →
        SectionsAmplitudeLE B S hS ⟨T.1, hY⟩ b I →
          SpaceCohomologyVanishesAbove B S hS X (b + N)
            ((spaceQuasicoherentProp B S hS X).ι.obj (DQ.obj ((spaceDerivedQ B S hS X).obj
              ((complexPushforward B S hS (ObjectProperty.homMk (jT.hom ≫ jW.hom) :
                (⟨T.1, hY⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj I)))))
    (b : ℤ) (I : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ) [I.IsKInjective]
    (hI : SectionsAmplitudeLE B S hS W b I) :
    SpaceCohomologyVanishesAbove B S hS X (b + N)
      ((spaceQuasicoherentProp B S hS X).ι.obj (DQ.obj ((spaceDerivedPushforward B S hS jW).obj
        ((spaceDerivedQ B S hS W).obj ((complexPushforward B S hS jT).obj
          ((complexEtalePullback B S hS jT hjT).obj I)))))) := by
  have := isKInjective_complexEtalePullback jT hjT I
  refine SpaceCohomologyVanishesAbove.of_iso (hT T.2 (isEtale_comp B S hS hjT hjW) b _
    inferInstance (sectionsAmplitudeLE_complexEtalePullback jT hjT hI))
    ((DQ ⋙ (spaceQuasicoherentProp B S hS X).ι).mapIso
      (spaceDerivedPushforwardRestrictPushIso jW jT hjT I).symm)

include adj in
/-- Let `(U ⊆ W, f : V ⟶ W)` be an elementary distinguished square and let `jW : W ⟶ X` be étale.
If `AlgebraicGeometry.Space.CoheratorBoundPushforward` holds for `U`, `V` and `U ×_W V` with their
composite morphisms to `X`, then there is an integer `N` such that `ι(DQ_X(jW,* I))` has no
cohomology sheaves above degree `b + N` for every K-injective `I` on `W` of affine amplitude at
most `b`. -/
theorem coheratorBound_of_isElementaryDistinguishedSquare {W : AlgebraicSpaces B S hS}
    (jW : W ⟶ X) (hjW : IsEtale B S hS jW.hom)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : Subfunctor W.1} {f : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 U f)
    (hU : CoheratorBoundPushforward DQ U.toFunctor (U.ι ≫ jW.hom))
    (hV : CoheratorBoundPushforward DQ V (f ≫ jW.hom))
    (hP : CoheratorBoundPushforward DQ (pullback U.ι f) ((pullback.fst U.ι f ≫ U.ι) ≫ jW.hom)) :
    ∃ N : ℤ, ∀ (b : ℤ) (I : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ), I.IsKInjective →
      SectionsAmplitudeLE B S hS W b I →
        SpaceCohomologyVanishesAbove B S hS X (b + N)
          ((spaceQuasicoherentProp B S hS X).ι.obj (DQ.obj ((spaceDerivedQ B S hS X).obj
            ((complexPushforward B S hS jW).obj I)))) := by
  obtain ⟨NU, hNU⟩ := hU
  obtain ⟨NV, hNV⟩ := hV
  obtain ⟨NP, hNP⟩ := hP
  refine ⟨max (max NU NV) NP + 1, fun b I hI hamp => ?_⟩
  have := hI
  let := spaceHasDerivedCategory B S hS W
  let := spaceHasDerivedCategory B S hS X
  have := smallEtaleRingedSite_hasSheafify_addCommGrpCat B S hS W
  have := smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat B S hS W
  have hF := isTriangulated_coherator_comp_ι adj
  obtain ⟨δ, hT⟩ := mem_distTriang_unitBiprod_of_natural_shortExact
    (edsAdjOpen B S hS hsq).unit (edsAdjEtale B S hS hsq).unit _ _
    (zero_edsRestrictPushMayerVietorisLowerShriek B S hS hsq)
    (shortExact_edsRestrictPushMayerVietorisLowerShriek B S hS hsq) I
  have hUc := coheratorBound_restrictPush jW hjW (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq) hNU b I hamp
  have hVc := coheratorBound_restrictPush jW hjW (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq) hNV b I hamp
  have hPc := coheratorBound_restrictPush jW hjW (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq) hNP b I hamp
  let G := spaceDerivedPushforward B S hS jW ⋙ DQ ⋙ (spaceQuasicoherentProp B S hS X).ι
  have : G.IsTriangulated := inferInstance
  have : G.Additive := inferInstance
  have hT' := G.map_distinguished _ hT
  let A := DerivedCategory.Q.obj ((edsRestrictPushOpen B S hS hsq).mapHomologicalComplex
    (ComplexShape.up ℤ) |>.obj I)
  let C := DerivedCategory.Q.obj ((edsRestrictPushEtale B S hS hsq).mapHomologicalComplex
    (ComplexShape.up ℤ) |>.obj I)
  have hmid : SpaceCohomologyVanishesAbove B S hS X (b + (max (max NU NV) NP + 1))
      (G.obj (A ⊞ C)) :=
    SpaceCohomologyVanishesAbove.of_iso
      (SpaceCohomologyVanishesAbove.biprod
        ((hUc.mono (by omega)) : SpaceCohomologyVanishesAbove B S hS X _ (G.obj A))
        ((hVc.mono (by omega)) : SpaceCohomologyVanishesAbove B S hS X _ (G.obj C)))
      (G.biprodIsoOfAdditive A C).symm
  have hthd : SpaceCohomologyVanishesAbove B S hS X (b + (max (max NU NV) NP + 1) - 1)
      (G.obj (DerivedCategory.Q.obj ((edsRestrictPushInter B S hS hsq).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj I))) :=
    hPc.mono (by omega)
  exact (SpaceCohomologyVanishesAbove.obj₁ hT' hmid hthd).of_iso
    ((DQ ⋙ (spaceQuasicoherentProp B S hS X).ι).mapIso
      (spaceDerivedPushforwardQIso B S hS jW I inferInstance))

end Bound

section Base

variable {X : AlgebraicSpaces B S hS}
  {DQ : spaceDerivedCategory B S hS X ⥤ (spaceQuasicoherentProp B S hS X).FullSubcategory}
  (adj : (spaceQuasicoherentProp B S hS X).ι ⊣ DQ) [DQ.CommShift ℤ] [adj.IsTriangulated]

omit [DQ.CommShift ℤ] [adj.IsTriangulated] in
include adj in
/-- Let `j : V ⟶ X` be étale and affine, suppose every object of `D_QCoh(𝒪_V)` is represented by a
complex of quasi-coherent modules, and that the coreflection on `V` of a K-injective `I` with
affine amplitude at most `b` lies in degrees `≤ b`. Then the coherator of `X` carries `j_*I` into
degrees `≤ b`. -/
theorem coheratorBound_of_isAffineHom {V : AlgebraicSpaces B S hS} (j : V ⟶ X)
    (hj : IsEtale B S hS j.hom) (haff : IsAffineHom B S hS j.hom)
    (hrep : ∀ E, spaceQuasicoherentProp B S hS V E →
      ∃ (C : CochainComplex (Modules.{u, u} B S hS V.1 V.2) ℤ)
        (_ : ∀ n, (C.X n).IsQuasicoherentOnSite), Nonempty ((spaceDerivedQ B S hS V).obj C ≅ E))
    (hB : ∀ (b : ℤ) (I : CochainComplex (Modules.{u, u} B S hS V.1 V.2) ℤ), I.IsKInjective →
      SectionsAmplitudeLE B S hS V b I →
        ∃ (E Q' : spaceDerivedCategory B S hS V) (a : E ⟶ (spaceDerivedQ B S hS V).obj I)
          (b' : (spaceDerivedQ B S hS V).obj I ⟶ Q') (c : Q' ⟶ E⟦(1 : ℤ)⟧),
          Triangle.mk a b' c ∈ distTriang _ ∧ spaceQuasicoherentProp B S hS V E ∧
            (spaceQuasicoherentProp B S hS V).rightOrthogonal Q' ∧
            SpaceCohomologyVanishesAbove B S hS V b E)
    (b : ℤ) (I : CochainComplex (Modules.{u, u} B S hS V.1 V.2) ℤ) [I.IsKInjective]
    (hI : SectionsAmplitudeLE B S hS V b I) :
    SpaceCohomologyVanishesAbove B S hS X b
      ((spaceQuasicoherentProp B S hS X).ι.obj (DQ.obj ((spaceDerivedQ B S hS X).obj
        ((complexPushforward B S hS j).obj I)))) := by
  obtain ⟨E, Q', a, b', c, hT, hE, hQ', hEb⟩ := hB b I inferInstance hI
  obtain ⟨C, hC, ⟨e⟩⟩ := hrep E hE
  have hE' : spaceQuasicoherentProp B S hS X ((spaceDerivedPushforward B S hS j).obj E) :=
    ObjectProperty.prop_of_iso _ ((spaceDerivedPushforward B S hS j).mapIso e)
      (spaceQuasicoherentProp_spaceDerivedPushforward_of_isAffineHom j haff C hC)
  have hQ'' := rightOrthogonal_spaceDerivedPushforward B S hS j hj Q' hQ'
  obtain ⟨e'⟩ := coherator_obj_iso_of_decomposition _ adj
    ((spaceDerivedPushforward B S hS j).map_distinguished _ hT) hE' hQ''
  have hRE : SpaceCohomologyVanishesAbove B S hS X b
      ((spaceDerivedPushforward B S hS j).obj E) := by
    let := spaceHasDerivedCategory B S hS V
    let := spaceHasDerivedCategory B S hS X
    rw [spaceCohomologyVanishesAbove_iff_isLE] at hEb ⊢
    exact isLE_derivedModulePushforward_obj_of_isAffineHom B S hS j haff
      (spaceDerivedPushforward B S hS j) (spaceDerivedPushforwardUnit B S hS j) E hE b hEb
  exact (hRE.of_iso e'.symm).of_iso ((DQ ⋙ (spaceQuasicoherentProp B S hS X).ι).mapIso
    (spaceDerivedPushforwardQIso B S hS j I inferInstance))

include adj in
/-- **The bound on the coherator, granted the affine case.** For a quasi-compact quasi-separated
algebraic space `X` whose affine étale objects map to it by affine morphisms there is an integer
`N` such that `ι(DQ_X(I))` has no cohomology sheaves above degree `b + N` for every K-injective
`I` of affine amplitude at most `b`. This is the one-sided form of [Stacks, Tag 0CSS]. -/
theorem exists_coheratorBound_of_affineCase (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hdiag : ∀ V : SpacesEtale B S hS X, IsAffineSpace B S hS V.1.left.1 →
      IsAffineHom B S hS V.1.hom.hom)
    (haffine : ∀ Y : AlgebraicSpaces B S hS, IsAffineSpace B S hS Y.1 →
      (∀ E, spaceQuasicoherentProp B S hS Y E →
        ∃ (C : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ)
          (_ : ∀ n, (C.X n).IsQuasicoherentOnSite),
            Nonempty ((spaceDerivedQ B S hS Y).obj C ≅ E)) ∧
      ∀ (b : ℤ) (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ), I.IsKInjective →
        SectionsAmplitudeLE B S hS Y b I →
          ∃ (E Q' : spaceDerivedCategory B S hS Y) (a : E ⟶ (spaceDerivedQ B S hS Y).obj I)
            (b' : (spaceDerivedQ B S hS Y).obj I ⟶ Q') (c : Q' ⟶ E⟦(1 : ℤ)⟧),
            Triangle.mk a b' c ∈ distTriang _ ∧ spaceQuasicoherentProp B S hS Y E ∧
              (spaceQuasicoherentProp B S hS Y).rightOrthogonal Q' ∧
              SpaceCohomologyVanishesAbove B S hS Y b E) :
    ∃ N : ℤ, ∀ (b : ℤ) (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ), I.IsKInjective →
      SectionsAmplitudeLE B S hS X b I →
        SpaceCohomologyVanishesAbove B S hS X (b + N)
          ((spaceQuasicoherentProp B S hS X).ι.obj (DQ.obj ((spaceDerivedQ B S hS X).obj I))) := by
  have hself : CoheratorBoundPushforward DQ X.1 (𝟙 X.1) := by
    refine qcqs_induction_on_self B S hS hZ X hXqc hXqs (CoheratorBoundPushforward DQ) ?_ ?_
    · intro V hVaff
      refine ⟨0, fun hY hj b I hI hamp => ?_⟩
      have := hI
      rw [add_zero]
      exact coheratorBound_of_isAffineHom adj
        (ObjectProperty.homMk V.1.hom.hom : (⟨V.1.left.1, hY⟩ : AlgebraicSpaces B S hS) ⟶ X) hj
        (hdiag V hVaff) (haffine ⟨_, hY⟩ hVaff).1 (haffine ⟨_, hY⟩ hVaff).2 b I hamp
    · intro W V U f hf hsq _ _ _ _ hU hV hP
      have hV' : CoheratorBoundPushforward DQ V.1.left.1 (f ≫ W.1.hom.hom) := by
        rw [hf]; exact hV
      have hP' : CoheratorBoundPushforward DQ (pullback U.ι f)
          ((pullback.fst U.ι f ≫ U.ι) ≫ W.1.hom.hom) := by
        rw [Category.assoc]; exact hP
      obtain ⟨N, hN⟩ := coheratorBound_of_isElementaryDistinguishedSquare adj (W := W.1.left)
        W.1.hom W.2 hsq hU hV' hP'
      exact ⟨N, fun hY _ b I hI hamp => hN b I hI hamp⟩
  obtain ⟨N, hN⟩ := hself
  refine ⟨N, fun b I hI hamp => ?_⟩
  exact (hN X.2 (isEtale_id B S hS X.1) b I hI hamp).of_iso
    ((DQ ⋙ (spaceQuasicoherentProp B S hS X).ι).mapIso ((spaceDerivedQ B S hS X).mapIso
      ((NatIso.mapHomologicalComplex (modulePushforwardIdIso B S hS X) (ComplexShape.up ℤ)).app I ≪≫
        (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app I)))

end Base

/-- `H^i(K) = 0` for `i < n`. -/
abbrev SpaceCohomologyVanishesBelow (X : AlgebraicSpaces B S hS) (n : ℤ)
    (K : spaceDerivedCategory B S hS X) : Prop :=
  ∀ i : ℤ, i < n → IsZero ((spaceDerivedHomology B S hS X i).obj K)

/-- **The coherator is left t-exact.** If `K` has no cohomology sheaves below degree `n`, neither
has `DQ_X(K)`. -/
theorem coherator_vanishesBelow {X : AlgebraicSpaces B S hS}
    {DQ : spaceDerivedCategory B S hS X ⥤ (spaceQuasicoherentProp B S hS X).FullSubcategory}
    (adj : (spaceQuasicoherentProp B S hS X).ι ⊣ DQ) (n : ℤ) (K : spaceDerivedCategory B S hS X)
    (hK : SpaceCohomologyVanishesBelow X n K) :
    SpaceCohomologyVanishesBelow X n
      ((spaceQuasicoherentProp B S hS X).ι.obj (DQ.obj K)) := by
  let := spaceHasDerivedCategory B S hS X
  let P := spaceQuasicoherentProp B S hS X
  let E := P.ι.obj (DQ.obj K)
  let T := (DerivedCategory.TStructure.t.truncLTι n).app E
  have hqc : P ((DerivedCategory.TStructure.t.truncLT n).obj E) := by
    intro j
    by_cases hj : j < n
    · have := Stacks.TruncationLevel.isIso_homologyMap_truncLTι_app n j hj E
      exact SheafOfModules.IsQuasicoherentOnSite.of_iso
        (asIso ((DerivedCategory.homologyFunctor _ j).map T)).symm ((DQ.obj K).property j)
    · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
        (DerivedCategory.isZero_of_isLE _ (n - 1) j (by omega))
  let F : P.FullSubcategory := ⟨_, hqc⟩
  have hKge : K.IsGE n := (DerivedCategory.isGE_iff K n).2 hK
  have hg : T ≫ adj.counit.app K = 0 :=
    DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ (n - 1) n (by omega)
      inferInstance hKge
  have hT : T = 0 := by
    exact eq_of_comp_counit_eq P adj (F := F) (by rw [zero_comp]; exact hg)
  intro i hi
  have := Stacks.TruncationLevel.isIso_homologyMap_truncLTι_app n i hi E
  have hzero : (DerivedCategory.homologyFunctor _ i).map T = 0 := by
    rw [hT, Functor.map_zero]
  have hepi : Epi ((DerivedCategory.homologyFunctor _ i).map T) := IsIso.epi_of_iso _
  rw [hzero] at hepi
  exact @IsZero.of_epi_zero _ _ _ _ _ hepi

/-! ### The coherator -/

/-- **[Stacks, Tag 0CQS] for `D_QCoh(𝒪_X) ⊆ D(𝒪_X)`**: if every object is coreflective, the
inclusion has a right adjoint. -/
theorem isLeftAdjoint_spaceQuasicoherentι_of_forall {X : AlgebraicSpaces B S hS}
    (h : ∀ K, spaceCoreflective B S hS X K) :
    (spaceQuasicoherentProp B S hS X).ι.IsLeftAdjoint :=
  ((ObjectProperty.isLeftAdjoint_ι_iff_extensionProduct_rightOrthogonal_eq_top_and_isSaturated
    (spaceQuasicoherentProp B S hS X)).1).2 (eq_top_iff.2 fun K _ => h K)

section TwoSided

variable {X : AlgebraicSpaces B S hS}
  {DQ : spaceDerivedCategory B S hS X ⥤ (spaceQuasicoherentProp B S hS X).FullSubcategory}
  (adj : (spaceQuasicoherentProp B S hS X).ι ⊣ DQ) [DQ.CommShift ℤ] [adj.IsTriangulated]

include adj in
/-- **The two-sided bound, granted the affine case.** With `N` the integer of the one-sided bound,
for every object `K` of `D(𝒪_X)` with no cohomology sheaves below degree `a` and represented by a
K-injective complex of affine amplitude at most `b`, the cohomology sheaves of `ι(DQ_X K)` vanish
outside `[a, b + N]`. -/
theorem exists_coheratorBound_twoSided_of_affineCase (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hdiag : ∀ V : SpacesEtale B S hS X, IsAffineSpace B S hS V.1.left.1 →
      IsAffineHom B S hS V.1.hom.hom)
    (haffine : ∀ Y : AlgebraicSpaces B S hS, IsAffineSpace B S hS Y.1 →
      (∀ E, spaceQuasicoherentProp B S hS Y E →
        ∃ (C : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ)
          (_ : ∀ n, (C.X n).IsQuasicoherentOnSite),
            Nonempty ((spaceDerivedQ B S hS Y).obj C ≅ E)) ∧
      ∀ (b : ℤ) (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ), I.IsKInjective →
        SectionsAmplitudeLE B S hS Y b I →
          ∃ (E Q' : spaceDerivedCategory B S hS Y) (a : E ⟶ (spaceDerivedQ B S hS Y).obj I)
            (b' : (spaceDerivedQ B S hS Y).obj I ⟶ Q') (c : Q' ⟶ E⟦(1 : ℤ)⟧),
            Triangle.mk a b' c ∈ distTriang _ ∧ spaceQuasicoherentProp B S hS Y E ∧
              (spaceQuasicoherentProp B S hS Y).rightOrthogonal Q' ∧
              SpaceCohomologyVanishesAbove B S hS Y b E) :
    ∃ N : ℤ, ∀ (a b : ℤ) (K : spaceDerivedCategory B S hS X),
      SpaceCohomologyVanishesBelow X a K →
      (∃ (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (_ : I.IsKInjective),
        Nonempty ((spaceDerivedQ B S hS X).obj I ≅ K) ∧ SectionsAmplitudeLE B S hS X b I) →
        SpaceCohomologyVanishesBelow X a
          ((spaceQuasicoherentProp B S hS X).ι.obj (DQ.obj K)) ∧
        SpaceCohomologyVanishesAbove B S hS X (b + N)
          ((spaceQuasicoherentProp B S hS X).ι.obj (DQ.obj K)) := by
  obtain ⟨N, hN⟩ := exists_coheratorBound_of_affineCase adj hZ hXqc hXqs hdiag haffine
  refine ⟨N, fun a b K hK ⟨I, hI, ⟨e⟩, hamp⟩ => ⟨coherator_vanishesBelow adj a K hK, ?_⟩⟩
  exact (hN b I hI hamp).of_iso ((DQ ⋙ (spaceQuasicoherentProp B S hS X).ι).mapIso e)

end TwoSided

end AlgebraicGeometry.Space

end
