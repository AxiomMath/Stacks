module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomSheafOfDual
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DenseOpenAgreement
public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocusGeneralBase

/-!
# The fppf sheaf property from Zariski gluing and the affine test schemes

Let `Y` be an algebraic space and `R` a functor on the test schemes over `Y`.  If `R` is a sheaf
for the Zariski topology of every test scheme (`AlgebraicGeometry.Space.IsZariskiSheafOver`) and
its restriction to the test schemes over every affine test scheme `V` of `Y` is an fppf sheaf over
`V`, then `R` is an fppf sheaf over `Y`.  This is the combination step of the route to
`AlgebraicGeometry.Space.RelativeDerivedHomZariskiDescent` (step (S) of Stacks 0DLC, part (3),
through the dual of Stacks 0DKY): it reduces that proposition to the Zariski sheaf property of
`T ↦ Hom(K_T, E_T)`, the named proposition
`AlgebraicGeometry.Space.RelativeDerivedHomZariskiGluing` (internal, in progress).

The argument: a covering sieve `𝒮` of a test scheme `T` and a compatible family on it are given.
Over each affine open `V` of `T` the family has a unique amalgamation `g_V`, by the fppf sheaf
property over the affine test scheme `V`
(`AlgebraicGeometry.Space.existsUnique_amalgamation_of_affine`); on `V ⊓ V'` the restrictions of
`g_V` and `g_{V'}` are both amalgamations over a test scheme lying over `V`, hence agree; Zariski
gluing gives `g` over `T`; and `g` restricts to the family on every member `Z ⟶ T` of `𝒮`, because
both agree on the preimages of the affine opens of `T`, which cover `Z`.

Nothing here is registered.

## Main definitions

* `AlgebraicGeometry.Space.IsZariskiSheafOver`: the Zariski sheaf property of a functor on the
  test schemes, for the covering of a test scheme by a family of opens.
* `AlgebraicGeometry.Space.RelativeDerivedHomZariskiGluing`: the Zariski sheaf property of
  `T ↦ Hom(K_T, E_T)` (internal, in progress).

## Main results

* `AlgebraicGeometry.Space.existsUnique_amalgamation_of_isFppfSheafOver`: an fppf sheaf over `Y`
  has unique amalgamations of compatible families over the test schemes.
* `AlgebraicGeometry.Space.existsUnique_amalgamation_of_affine`: the same over a test scheme
  lying over an affine test scheme, from the fppf sheaf property over that affine test scheme.
* `AlgebraicGeometry.Space.isFppfSheafOver_of_isZariskiSheafOver`: the combination.
* `AlgebraicGeometry.Space.relativeDerivedHomZariskiDescent_of_zariskiGluing`:
  `AlgebraicGeometry.Space.RelativeDerivedHomZariskiDescent` from Zariski gluing.
* `AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_of_dual_of_zariskiGluing`:
  Stacks 0DLC, part (3), at `W = Y`, from Stacks 0DKY and Zariski gluing only.

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u w

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Amalgamations from the fppf sheaf property -/

section Amalgamation

variable {Y : AlgebraicSpaces B S hS}

/-- The test scheme of the section of `Y` that a test scheme is has the same structure
morphism. -/
theorem pointTestScheme_testPoint_hom (T : SchemesOver Y) :
    (pointTestScheme T.left (testPoint T)).hom = T.hom :=
  ObjectProperty.hom_ext _ (yonedaEquiv_symm_testPoint T)

/-- The restriction of a test scheme along `h` has the structure morphism of the test scheme of
the restricted section. -/
theorem restrictTest_hom_eq (T : SchemesOver Y) {Z : BigFppfOver B S hS} (h : Z ⟶ T.left) :
    (restrictTest T h).hom = (pointTestScheme Z (Y.1.map h.op (testPoint T))).hom :=
  (congrArg ((schemeSpaceFunctor B S hS).map h ≫ ·) (pointTestScheme_testPoint_hom T).symm).trans
    (pointTestScheme_hom_map h (testPoint T))

/-- The restriction of a test scheme along a morphism `h` of the site is the test scheme of the
restricted section: the identity of the underlying scheme, read as a morphism of test schemes. -/
def restrictTestPointHom (T : SchemesOver Y) {Z : BigFppfOver B S hS} (h : Z ⟶ T.left) :
    pointTestScheme Z (Y.1.map h.op (testPoint T)) ⟶ restrictTest T h :=
  CostructuredArrow.homMk (𝟙 Z) ((congrArg (· ≫ (restrictTest T h).hom)
    (CategoryTheory.Functor.map_id _ _)).trans ((Category.id_comp _).trans
      (restrictTest_hom_eq T h)))

/-- The inverse of `AlgebraicGeometry.Space.restrictTestPointHom`. -/
def restrictTestPointInv (T : SchemesOver Y) {Z : BigFppfOver B S hS} (h : Z ⟶ T.left) :
    restrictTest T h ⟶ pointTestScheme Z (Y.1.map h.op (testPoint T)) :=
  CostructuredArrow.homMk (𝟙 Z) ((congrArg (· ≫ (pointTestScheme Z _).hom)
    (CategoryTheory.Functor.map_id _ _)).trans ((Category.id_comp _).trans
      (restrictTest_hom_eq T h).symm))

/-- `AlgebraicGeometry.Space.restrictTestPointInv` is a left inverse of
`AlgebraicGeometry.Space.restrictTestPointHom`. -/
theorem restrictTestPointInv_hom (T : SchemesOver Y) {Z : BigFppfOver B S hS} (h : Z ⟶ T.left) :
    restrictTestPointInv T h ≫ restrictTestPointHom T h = 𝟙 _ :=
  CostructuredArrow.hom_ext _ _ (Category.comp_id (𝟙 Z))

/-- Restricting along `f₁` after `g₁` agrees with doing so along `f₂` after `g₂` when
`f₁ ≫ g₁ = f₂ ≫ g₂`. -/
private theorem map_op_map_op_eq_of_comp_eq {C : Type*} [Category* C] (R : Cᵒᵖ ⥤ Type w)
    {P Q₁ Q₂ W : C} {f₁ : P ⟶ Q₁} {g₁ : Q₁ ⟶ W} {f₂ : P ⟶ Q₂} {g₂ : Q₂ ⟶ W}
    (h : f₁ ≫ g₁ = f₂ ≫ g₂) (x : R.obj (Opposite.op W)) :
    R.map f₁.op (R.map g₁.op x) = R.map f₂.op (R.map g₂.op x) := by
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, h]

variable (R : (SchemesOver Y)ᵒᵖ ⥤ Type w)

/-- **An fppf sheaf over `Y` has unique amalgamations over the test schemes**: for a test scheme
`T` over `Y`, a covering sieve `𝒮` of its underlying scheme and a compatible family of elements
of `R` over the restrictions of `T` along the members of `𝒮`, there is exactly one element of `R`
over `T` restricting to the family.  This is the converse of
`AlgebraicGeometry.Space.isFppfSheafOver_of_amalgamation`. -/
theorem existsUnique_amalgamation_of_isFppfSheafOver (hR : IsFppfSheafOver R)
    (T : SchemesOver Y) (𝒮 : Sieve T.left) (h𝒮 : 𝒮 ∈ BigFppfOver.topology B S hS T.left)
    (r : ∀ ⦃Z : BigFppfOver B S hS⦄ (h : Z ⟶ T.left), 𝒮.arrows h →
      R.obj (Opposite.op (restrictTest T h)))
    (hr : ∀ ⦃Z Z' : BigFppfOver B S hS⦄ (h : Z ⟶ T.left) (h' : Z' ⟶ T.left) (hh : 𝒮.arrows h)
      (hh' : 𝒮.arrows h') (m : Z' ⟶ Z) (e : m ≫ h = h'),
      R.map (restrictTestMap T m e).op (r h hh) = r h' hh') :
    ∃! g : R.obj (Opposite.op T), ∀ ⦃Z : BigFppfOver B S hS⦄ (h : Z ⟶ T.left)
      (hh : 𝒮.arrows h), R.map (restrictTestHom T h).op g = r h hh := by
  have hR' := (isSheaf_iff_isSheaf_of_type _ _).1 hR
  have hY : Presieve.IsSheaf (BigFppfOver.topology B S hS) Y.1 :=
    (isSheaf_iff_isSheaf_of_type _ _).1 Y.2.isSheaf
  let y₀ := testPoint T
  let xf : Presieve.FamilyOfElements (totalPresheaf R) 𝒮.arrows := fun Z h hh =>
    ⟨Y.1.map h.op y₀, R.map (restrictTestPointHom T h).op (r h hh)⟩
  have hxf : xf.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Z Z' h g hh
    show (⟨Y.1.map (g ≫ h).op y₀, R.map (restrictTestPointHom T (g ≫ h)).op
        (r (g ≫ h) (𝒮.downward_closed hh g))⟩ :
          Σ y' : Y.1.obj (Opposite.op Z'), R.obj (Opposite.op (pointTestScheme Z' y'))) =
      ⟨Y.1.map g.op (Y.1.map h.op y₀), R.map (pointTestHom g rfl).op
        (R.map (restrictTestPointHom T h).op (r h hh))⟩
    rw [← hr h (g ≫ h) hh (𝒮.downward_closed hh g) g rfl]
    exact totalPresheaf_ext₂ R (r h hh) (by rw [op_comp, Functor.map_comp_apply]) _ _ _ _
      (by
        show 𝟙 Z' ≫ g = g ≫ 𝟙 Z
        rw [Category.id_comp, Category.comp_id])
  obtain ⟨⟨y, g'⟩, ht, hu⟩ := hR' 𝒮 h𝒮 xf hxf
  have hy : y = y₀ := (hY 𝒮 h𝒮).isSeparatedFor.ext fun Z h hh =>
    congrArg Sigma.fst (ht h hh)
  subst hy
  have ht' : ∀ ⦃Z : BigFppfOver B S hS⦄ (h : Z ⟶ T.left) (hh : 𝒮.arrows h),
      R.map (pointTestHom h rfl).op g' = R.map (restrictTestPointHom T h).op (r h hh) :=
    fun Z h hh => eq_of_heq (Sigma.mk.inj_iff.1 ((totalPresheaf_map_apply R h.op _).symm.trans
      (ht h hh))).2
  refine ⟨R.map (pointTestSchemeIso T).inv.op g', fun Z h hh => ?_, fun g₁ hg₁ => ?_⟩
  · rw [map_op_map_op_eq_of_comp_eq R (g₂ := pointTestHom h rfl) (f₂ := restrictTestPointInv T h)
      (CostructuredArrow.hom_ext _ _ (by
        show h ≫ 𝟙 _ = 𝟙 Z ≫ h
        rw [Category.comp_id, Category.id_comp])) g', ht' h hh]
    exact FunctorToTypes.map_map_eq_self_of_comp_eq_id R
      (by rw [← op_comp, restrictTestPointInv_hom, op_id]) _
  · have h₁ := hu ⟨y₀, R.map (pointTestSchemeIso T).hom.op g₁⟩ (fun Z h hh => by
      show (⟨Y.1.map h.op y₀, R.map (pointTestHom h rfl).op
          (R.map (pointTestSchemeIso T).hom.op g₁)⟩ :
            Σ y' : Y.1.obj (Opposite.op Z), R.obj (Opposite.op (pointTestScheme Z y'))) =
        ⟨Y.1.map h.op y₀, R.map (restrictTestPointHom T h).op (r h hh)⟩
      rw [← hg₁ h hh]
      exact totalPresheaf_ext₂ R g₁ rfl _ _ _ _ (by
        show h ≫ 𝟙 _ = 𝟙 Z ≫ h
        rw [Category.comp_id, Category.id_comp]))
    have h₂ : R.map (pointTestSchemeIso T).hom.op g₁ = g' :=
      eq_of_heq (Sigma.mk.inj_iff.1 h₁).2
    rw [← h₂]
    exact (FunctorToTypes.map_map_eq_self_of_comp_eq_id R
      (pointTestSchemeIso T).op.hom_inv_id g₁).symm

/-- **Amalgamations over a test scheme lying over an affine test scheme.**  Let `T` be a test
scheme over `Y`, `a : A ⟶ T` a morphism of the site from an affine scheme, and `h₀ : Z₀ ⟶ T`
factoring through `a`.  If the restriction of `R` to the test schemes over the affine test scheme
`A` is an fppf sheaf, then a compatible family on a sieve `𝒮` of `T` whose pullback to `Z₀`
covers has exactly one amalgamation over `Z₀`. -/
theorem existsUnique_amalgamation_of_affine
    (haff : ∀ V : SchemesOver Y, IsAffine ((BigFppfOver.toScheme B S hS).obj V.left) →
      IsFppfSheafOver ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom).op ⋙ R))
    (T : SchemesOver Y) {A Z₀ : BigFppfOver B S hS} (a : A ⟶ T.left)
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A)) (k₀ : Z₀ ⟶ A) (h₀ : Z₀ ⟶ T.left)
    (e₀ : k₀ ≫ a = h₀) (𝒮 : Sieve T.left)
    (h𝒮 : 𝒮.pullback h₀ ∈ BigFppfOver.topology B S hS Z₀)
    (r : ∀ ⦃Z : BigFppfOver B S hS⦄ (h : Z ⟶ T.left), 𝒮.arrows h →
      R.obj (Opposite.op (restrictTest T h)))
    (hr : ∀ ⦃Z Z' : BigFppfOver B S hS⦄ (h : Z ⟶ T.left) (h' : Z' ⟶ T.left) (hh : 𝒮.arrows h)
      (hh' : 𝒮.arrows h') (m : Z' ⟶ Z) (e : m ≫ h = h'),
      R.map (restrictTestMap T m e).op (r h hh) = r h' hh') :
    ∃! g : R.obj (Opposite.op (restrictTest T h₀)), ∀ ⦃Z : BigFppfOver B S hS⦄ (k : Z ⟶ Z₀)
      (h' : Z ⟶ T.left) (e : k ≫ h₀ = h') (hh : 𝒮.arrows h'),
      R.map (restrictTestMap T k e).op g = r h' hh := by
  subst e₀
  let V := restrictTest T a
  let M := CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom
  let T' : SchemesOver ((schemeSpaceFunctor B S hS).obj A) :=
    CostructuredArrow.mk (Y := Z₀) ((schemeSpaceFunctor B S hS).map k₀)
  -- the test schemes over `A`, read over `Y`, are restrictions of `T`
  have hhom : ∀ {Z : BigFppfOver B S hS} (k : Z ⟶ Z₀) (h' : Z ⟶ T.left), k ≫ k₀ ≫ a = h' →
      (schemeSpaceFunctor B S hS).map (𝟙 Z) ≫ (restrictTest T h').hom =
        (M.obj (restrictTest T' k)).hom := by
    rintro Z k - rfl
    simp only [M, V, T', CostructuredArrow.map_obj_hom, CostructuredArrow.mk_hom_eq_self,
      CategoryTheory.Functor.map_comp, Category.assoc, CategoryTheory.Functor.map_id,
      Category.id_comp]
  let φ : ∀ ⦃Z : BigFppfOver B S hS⦄ (k : Z ⟶ Z₀), M.obj (restrictTest T' k) ⟶
      restrictTest T (k ≫ k₀ ≫ a) := fun Z k => CostructuredArrow.homMk (𝟙 Z) (hhom k _ rfl)
  let φ' : ∀ ⦃Z : BigFppfOver B S hS⦄ (k : Z ⟶ Z₀) (h' : Z ⟶ T.left) (_ : k ≫ k₀ ≫ a = h'),
      restrictTest T h' ⟶ M.obj (restrictTest T' k) := fun Z k h' e =>
    CostructuredArrow.homMk (𝟙 Z) ((hhom k h' e).symm)
  let ψ : M.obj T' ⟶ restrictTest T (k₀ ≫ a) := φ (𝟙 Z₀)
  let ψ' : restrictTest T (k₀ ≫ a) ⟶ M.obj T' := φ' (𝟙 Z₀) (k₀ ≫ a) (by simp)
  have hlr : ∀ {Z Z' : BigFppfOver B S hS} (m : Z' ⟶ Z), m ≫ 𝟙 Z = 𝟙 Z' ≫ m :=
    fun m => (Category.comp_id m).trans (Category.id_comp m).symm
  let r' : ∀ ⦃Z : BigFppfOver B S hS⦄ (k : Z ⟶ T'.left), (𝒮.pullback (k₀ ≫ a)).arrows k →
      (M.op ⋙ R).obj (Opposite.op (restrictTest T' k)) := fun Z k hk =>
    R.map (φ k).op (r (k ≫ k₀ ≫ a) hk)
  have hr' : ∀ ⦃Z Z' : BigFppfOver B S hS⦄ (k : Z ⟶ T'.left) (k' : Z' ⟶ T'.left)
      (hk : (𝒮.pullback (k₀ ≫ a)).arrows k) (hk' : (𝒮.pullback (k₀ ≫ a)).arrows k')
      (m : Z' ⟶ Z) (e : m ≫ k = k'),
      (M.op ⋙ R).map (restrictTestMap T' m e).op (r' k hk) = r' k' hk' := by
    intro Z Z' k k' hk hk' m e
    exact (map_op_map_op_eq_of_comp_eq R (g₂ := restrictTestMap T m (by rw [← e, Category.assoc]))
      (CostructuredArrow.hom_ext _ _ (hlr m)) _).trans (congrArg (R.map (φ k').op) (hr _ _ _ _ _ _))
  obtain ⟨g', hg', hu'⟩ := existsUnique_amalgamation_of_isFppfSheafOver (M.op ⋙ R)
    (haff V hA) T' (𝒮.pullback (k₀ ≫ a)) h𝒮 r' hr'
  have hg'' : ∀ ⦃Z : BigFppfOver B S hS⦄ (k : Z ⟶ Z₀) (hk : 𝒮.arrows (k ≫ k₀ ≫ a)),
      R.map (M.map (restrictTestHom T' k)).op g' = R.map (φ k).op (r (k ≫ k₀ ≫ a) hk) :=
    fun Z k hk => hg' k hk
  refine ⟨R.map ψ'.op g', fun Z k h' e hh => ?_, fun g₁ hg₁ => ?_⟩
  · rw [map_op_map_op_eq_of_comp_eq R (g₂ := M.map (restrictTestHom T' k)) (f₂ := φ' k h' e)
      (CostructuredArrow.hom_ext _ _ (hlr k)),
      hg'' k (show 𝒮.arrows (k ≫ k₀ ≫ a) from e ▸ hh),
      ← Functor.map_comp_apply, ← op_comp,
      show φ' k h' e ≫ φ k = restrictTestMap T (𝟙 Z) (by rw [Category.id_comp, e]) from
        CostructuredArrow.hom_ext _ _ (Category.comp_id (𝟙 Z))]
    exact hr _ _ _ _ _ _
  · have hψ : ψ' ≫ ψ = 𝟙 _ := CostructuredArrow.hom_ext _ _ (Category.comp_id (𝟙 Z₀))
    have h₁ : R.map ψ.op g₁ = g' := hu' _ fun Z k hk => by
      change R.map (M.map (restrictTestHom T' k)).op (R.map ψ.op g₁) = R.map (φ k).op _
      exact (map_op_map_op_eq_of_comp_eq R (g₂ := restrictTestMap T k rfl)
        (CostructuredArrow.hom_ext _ _ (hlr k)) g₁).trans
          (congrArg (R.map (φ k).op) (hg₁ k _ rfl hk))
    rw [← h₁]
    exact (FunctorToTypes.map_map_eq_self_of_comp_eq_id R (by rw [← op_comp, hψ, op_id]) g₁).symm

end Amalgamation

/-! ### Zariski gluing -/

section Zariski

variable {Y : AlgebraicSpaces B S hS} (R : (SchemesOver Y)ᵒᵖ ⥤ Type w)

/-- The inclusion of `U ⊓ U'` in `U`, followed by `U ⟶ Z₀ ⟶ T`, is the inclusion of `U ⊓ U'`
followed by `Z₀ ⟶ T`. -/
theorem openSubHomOfLE_comp_openSubHom_comp {Z₀ T₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T₀)
    {U U' : Z₀.left.obj.Opens} (hle : U ≤ U') :
    BigFppfOver.openSubHomOfLE B S hS Z₀ hle ≫ BigFppfOver.openSubHom B S hS Z₀ U' ≫ h₀ =
      BigFppfOver.openSubHom B S hS Z₀ U ≫ h₀ := by
  rw [← Category.assoc, BigFppfOver.openSubHomOfLE_comp_openSubHom]

/-- **The Zariski sheaf property of a functor on the test schemes**, relative to a morphism
`h₀ : Z₀ ⟶ T` of the site into a test scheme `T`: for every family of opens `U_i` covering the
underlying scheme of `Z₀`, elements of `R` over the restrictions of `T` to the `U_i` which agree
on the overlaps `U_i ⊓ U_k` come from exactly one element of `R` over the restriction of `T` to
`Z₀`. -/
def IsZariskiSheafOver : Prop :=
  ∀ (T : SchemesOver Y) {Z₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T.left) {ι : Type u}
    (U : ι → Z₀.left.obj.Opens), iSup U = ⊤ →
    ∀ α : ∀ i, R.obj (Opposite.op (restrictTest T (BigFppfOver.openSubHom B S hS Z₀ (U i) ≫ h₀))),
    (∀ i k, R.map (restrictTestMap T (BigFppfOver.openSubHomOfLE B S hS Z₀
        (inf_le_left : U i ⊓ U k ≤ U i)) (openSubHomOfLE_comp_openSubHom_comp h₀ _)).op (α i) =
      R.map (restrictTestMap T (BigFppfOver.openSubHomOfLE B S hS Z₀
        (inf_le_right : U i ⊓ U k ≤ U k)) (openSubHomOfLE_comp_openSubHom_comp h₀ _)).op (α k)) →
    ∃! g : R.obj (Opposite.op (restrictTest T h₀)),
      ∀ i, R.map (restrictTestMap T (BigFppfOver.openSubHom B S hS Z₀ (U i)) rfl).op g = α i

/-- **The fppf sheaf property from Zariski gluing and the affine test schemes.**  A functor `R`
on the test schemes over `Y` which is a Zariski sheaf (`hZ`) and whose restriction to the test
schemes over every affine test scheme is an fppf sheaf (`haff`) is an fppf sheaf over `Y`. -/
theorem isFppfSheafOver_of_isZariskiSheafOver (hZ : IsZariskiSheafOver R)
    (haff : ∀ V : SchemesOver Y, IsAffine ((BigFppfOver.toScheme B S hS).obj V.left) →
      IsFppfSheafOver ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom).op ⋙ R)) :
    IsFppfSheafOver R := by
  refine isFppfSheafOver_of_amalgamation R fun T 𝒮 h𝒮 r hr => ?_
  let X₀ := (BigFppfOver.toScheme B S hS).obj T.left
  let V : X₀.affineOpens → T.left.left.obj.Opens := fun i => i.1
  have hV : iSup V = ⊤ := iSup_affineOpens_eq_top X₀
  have ha : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
      (BigFppfOver.openSubObj B S hS T.left (V i))) := fun i => i.2
  have hpull : ∀ {Z : BigFppfOver B S hS} (h : Z ⟶ T.left),
      𝒮.pullback h ∈ BigFppfOver.topology B S hS Z := fun h =>
    GrothendieckTopology.pullback_stable _ h h𝒮
  -- the amalgamations over the affine opens of `T`
  have hloc := fun i => existsUnique_amalgamation_of_affine R haff T
    (BigFppfOver.openSubHom B S hS T.left (V i)) (ha i) (𝟙 _)
    (BigFppfOver.openSubHom B S hS T.left (V i) ≫ 𝟙 T.left)
    (by rw [Category.id_comp, Category.comp_id]) 𝒮 (hpull _) r hr
  choose g hg hgu using hloc
  -- they agree on the overlaps
  have hcomp : ∀ i k, R.map (restrictTestMap T (BigFppfOver.openSubHomOfLE B S hS T.left
      (inf_le_left : V i ⊓ V k ≤ V i)) (openSubHomOfLE_comp_openSubHom_comp (𝟙 _) _)).op (g i) =
      R.map (restrictTestMap T (BigFppfOver.openSubHomOfLE B S hS T.left
      (inf_le_right : V i ⊓ V k ≤ V k)) (openSubHomOfLE_comp_openSubHom_comp (𝟙 _) _)).op
        (g k) := by
    intro i k
    obtain ⟨_, -, hu⟩ := existsUnique_amalgamation_of_affine R haff T
      (BigFppfOver.openSubHom B S hS T.left (V i)) (ha i)
      (BigFppfOver.openSubHomOfLE B S hS T.left (inf_le_left : V i ⊓ V k ≤ V i))
      (BigFppfOver.openSubHom B S hS T.left (V i ⊓ V k) ≫ 𝟙 T.left)
      (by rw [Category.comp_id, BigFppfOver.openSubHomOfLE_comp_openSubHom]) 𝒮 (hpull _) r hr
    refine (hu _ fun Z m h' e hh => ?_).trans (hu _ fun Z m h' e hh => ?_).symm <;>
      refine (map_restrictTestMap_restrictTestMap R _ _ m e _
        (by rw [← e, Category.assoc, openSubHomOfLE_comp_openSubHom_comp]) rfl _).trans ?_
    · exact hg i _ _ _ hh
    · exact hg k _ _ _ hh
  obtain ⟨G, hG, hGu⟩ := hZ T (𝟙 T.left) V hV g hcomp
  let ι₀ : T ⟶ restrictTest T (𝟙 T.left) := CostructuredArrow.homMk (𝟙 T.left) (by
    simp only [CostructuredArrow.mk_hom_eq_self, CategoryTheory.Functor.map_id,
      Category.id_comp])
  have hgT : ∀ {Z : BigFppfOver B S hS} (h : Z ⟶ T.left),
      R.map (restrictTestHom T h).op (R.map ι₀.op G) =
        R.map (restrictTestMap T h (Category.comp_id h)).op G := by
    intro Z h
    rw [← Functor.map_comp_apply, ← op_comp]
    exact congrArg (fun k => R.map (Quiver.Hom.op k) G)
      (CostructuredArrow.hom_ext _ _ (Category.comp_id h))
  refine ⟨R.map ι₀.op G, fun Z h hh => ?_, fun G' hG' => ?_⟩
  · -- the glued element restricts to the family
    rw [hgT h]
    let f := (BigFppfOver.toScheme B S hS).map h
    let U : X₀.affineOpens → Z.left.obj.Opens := fun i => f ⁻¹ᵁ V i
    have hU : iSup U = ⊤ := f.iSup_preimage_eq_top hV
    let n : ∀ i, BigFppfOver.openSubObj B S hS Z (U i) ⟶
        BigFppfOver.openSubObj B S hS T.left (V i) := fun i =>
      openSubObjLift B S hS T.left (V i) (BigFppfOver.openSubHom B S hS Z (U i) ≫ h) (by
        rintro _ ⟨x, rfl⟩
        show f ((U i).ι x) ∈ V i
        exact x.2)
    have hn : ∀ i, n i ≫ BigFppfOver.openSubHom B S hS T.left (V i) =
        BigFppfOver.openSubHom B S hS Z (U i) ≫ h := fun i =>
      openSubObjLift_comp_openSubHom B S hS _ _ _ _
    have hn' : ∀ i, n i ≫ BigFppfOver.openSubHom B S hS T.left (V i) ≫ 𝟙 T.left =
        BigFppfOver.openSubHom B S hS Z (U i) ≫ h := fun i => by
      rw [Category.comp_id]
      exact hn i
    have hres : ∀ i, R.map (restrictTestMap T (BigFppfOver.openSubHom B S hS Z (U i)) rfl).op
        (R.map (restrictTestMap T h (Category.comp_id h)).op G) =
          r (BigFppfOver.openSubHom B S hS Z (U i) ≫ h)
            (𝒮.downward_closed hh (BigFppfOver.openSubHom B S hS Z (U i))) := by
      intro i
      refine (map_restrictTestMap_restrictTestMap R h (Category.comp_id h)
        (BigFppfOver.openSubHom B S hS Z (U i)) rfl
        (BigFppfOver.openSubHom B S hS Z (U i) ≫ h) (Category.comp_id _) rfl G).trans ?_
      refine (map_restrictTestMap_restrictTestMap R
        (BigFppfOver.openSubHom B S hS T.left (V i)) rfl (n i) (hn' i)
        (BigFppfOver.openSubHom B S hS Z (U i) ≫ h) (Category.comp_id _) (hn i) G).symm.trans ?_
      rw [hG i]
      exact hg i (n i) _ (hn' i) _
    obtain ⟨_, -, hu⟩ := hZ T h U hU
      (fun i => R.map (restrictTestMap T (BigFppfOver.openSubHom B S hS Z (U i)) rfl).op (r h hh))
      (fun i k => (map_restrictTestMap_restrictTestMap R _ rfl _
          (openSubHomOfLE_comp_openSubHom_comp h _) (BigFppfOver.openSubHom B S hS Z (U i ⊓ U k))
          rfl (BigFppfOver.openSubHomOfLE_comp_openSubHom B S hS Z _) (r h hh)).trans
        (map_restrictTestMap_restrictTestMap R _ rfl _
          (openSubHomOfLE_comp_openSubHom_comp h _) (BigFppfOver.openSubHom B S hS Z (U i ⊓ U k))
          rfl (BigFppfOver.openSubHomOfLE_comp_openSubHom B S hS Z _) (r h hh)).symm)
    refine (hu _ fun i => ?_).trans (hu _ fun i => rfl).symm
    rw [hres i]
    exact (hr h _ hh _ (BigFppfOver.openSubHom B S hS Z (U i)) rfl).symm
  · -- uniqueness
    have hι : ι₀ ≫ restrictTestHom T (𝟙 T.left) = 𝟙 _ :=
      CostructuredArrow.hom_ext _ _ (Category.comp_id _)
    have hG'0 : R.map ι₀.op (R.map (restrictTestHom T (𝟙 T.left)).op G') = G' :=
      FunctorToTypes.map_map_eq_self_of_comp_eq_id R (by rw [← op_comp, hι, op_id]) G'
    rw [← hG'0]
    congr 1
    refine hGu _ fun i => hgu i _ fun Z m h' e hh => ?_
    exact ((congrArg _ (map_restrictTestMap_restrictTestHom R _ rfl G')).trans
      (map_restrictTestMap_restrictTestHom R m e G')).trans (hG' h' hh)

end Zariski

/-! ### The relative derived Hom functor -/

variable (B S hS) in
/-- **Zariski gluing of `T ↦ Hom(K_T, E_T)`** (internal, in progress; the remaining input of
`AlgebraicGeometry.Space.RelativeDerivedHomZariskiDescent`).  Let `f : X ⟶ Y` be a morphism of
algebraic spaces and `K`, `E` pseudo-coherent objects of `D(𝒪_X)` with `Ext^i(K_V, E_V) = 0` for
`i < 0` and every algebraic space `V` over `Y`.  Then `T ↦ Hom(K_T, E_T)` is a sheaf for the
Zariski topology of every test scheme: morphisms `K_{T_k} ⟶ E_{T_k}` on the members of an open
covering of a test scheme `T` which agree on the overlaps glue uniquely to `K_T ⟶ E_T`.  With
`M = Rf_{T,*} R𝓗om(K_T, E_T)` on the small étale site of `T`, the vanishing hypothesis gives
`M ∈ D^{≥ 0}`, so `Hom(K_W, E_W) = Γ(W, H^0(M))` for every open `W` of `T`, a sheaf in `W`. -/
def RelativeDerivedHomZariskiGluing : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (K E : derivedModules B S hS X),
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K →
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E →
    (∀ (V : Over Y) (i : ℤ), i < 0 →
      Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj K ⟶
        (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E)⟦i⟧)) →
    IsZariskiSheafOver (relativeDerivedHom f K E)

/-- **`AlgebraicGeometry.Space.RelativeDerivedHomZariskiDescent` from Zariski gluing**: the fppf
sheaf property of `T ↦ Hom(K_T, E_T)` follows from its Zariski sheaf property and the fppf sheaf
property over the affine test schemes
(`AlgebraicGeometry.Space.isFppfSheafOver_of_isZariskiSheafOver`). -/
theorem relativeDerivedHomZariskiDescent_of_zariskiGluing
    (hZar : RelativeDerivedHomZariskiGluing B S hS) : RelativeDerivedHomZariskiDescent B S hS :=
  fun f K E hK hE hneg haff =>
    isFppfSheafOver_of_isZariskiSheafOver _ (hZar f K E hK hE hneg) haff

/-- **Stacks 0DLC, part (3), in the case `W = Y`, from Zariski gluing**: from part (2) in the
case `W = Y` (`h2`), Stacks 0DKY in its compatible form (`h0DKY`) and Zariski gluing of
`T ↦ Hom(K_T, E_T)` (`hZar`, internal, in progress).  This is
`AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_of_zariski` with its Zariski
descent input reduced to Zariski gluing. -/
theorem relativeDerivedHomRepresentableOfFibres_of_zariskiGluing
    (h2 : NegativeExtVanishesOfFibres B S hS)
    (h0DKY : RelativeDerivedHomDualExistsNaturalCompatible B S hS)
    (hZar : RelativeDerivedHomZariskiGluing B S hS) :
    RelativeDerivedHomRepresentableOfFibres B S hS :=
  relativeDerivedHomRepresentableOfFibres_of_zariski h2 h0DKY
    (relativeDerivedHomZariskiDescent_of_zariskiGluing hZar)

/-- **Stacks 0DLC, part (3), in the case `W = Y`, from Stacks 0DKY and Zariski gluing**: part (2)
in the case `W = Y` is discharged by Stacks 0DKY
(`AlgebraicGeometry.Space.negativeExtVanishesOfFibres_of_dualExists`), so the inputs are Stacks
0DKY in its compatible form (`h0DKY`) and Zariski gluing of `T ↦ Hom(K_T, E_T)` (`hZar`,
internal, in progress). -/
theorem relativeDerivedHomRepresentableOfFibres_of_dual_of_zariskiGluing
    (h0DKY : RelativeDerivedHomDualExistsNaturalCompatible B S hS)
    (hZar : RelativeDerivedHomZariskiGluing B S hS) :
    RelativeDerivedHomRepresentableOfFibres B S hS :=
  relativeDerivedHomRepresentableOfFibres_of_zariskiGluing
    (negativeExtVanishesOfFibres_of_dualExists B S hS h0DKY.relativeDerivedHomDualExists) h0DKY
    hZar

end AlgebraicGeometry.Space

end
