module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFlatBaseChangeSheafFppf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineRingedToposTopologies
public import StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingStandardCovering
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.CategoryTheory.MorphismProperty.OverObjFiniteProducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfCoefficientsOnTheNerve
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FirstVanishingAndSections

/-!
# The extension clause of Stacks 0771 (2) for `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`

Let `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` be a short exact sequence of modules on the fppf site of a category
`𝒳` fibred in groupoids over `(Sch/S)_{fppf}`, with `ℱ₁` and `ℱ₃` in `LQCoh^fbc(𝒪_𝒳)`.  This
file shows that the sequence stays exact in the étale topology, so that `ℱ₂` is in
`LQCoh^fbc(𝒪_𝒳)`.  Over an object `x` lying over an affine scheme `U`, the first Čech cohomology
of `ℱ₁` vanishes on the families of arrows lying over standard fppf coverings of `U`
(**Stacks 03FJ**), and the section map `ℱ₂(x) ⟶ ℱ₃(x)` is surjective (**Stacks 03F8**).

## Main results

* `AlgebraicGeometry.Stack.sectionsIsoOfIsFlatOver`: on the objects of the slice at `x` lying
  flatly over `x`, the sections of a member of `LQCoh^fbc(𝒪_𝒳)` are those of `𝓕`.
* `AlgebraicGeometry.Stack.isZero_cechCohomology_one_of_locallyQuasicoherentFlatBaseChangeSheaf`:
  the first Čech cohomology of a member of `LQCoh^fbc(𝒪_𝒳)` vanishes on a finite family of
  arrows from objects over affine schemes lying over an fppf covering of an affine scheme.
* `AlgebraicGeometry.Stack.surjective_app_of_shortExact_of_isAffineObject`: the section map
  `ℱ₂(x) ⟶ ℱ₃(x)` is surjective over an object lying over an affine scheme.
* `AlgebraicGeometry.Stack.epi_fppfToEtaleSheafOfModules_map_g_of_shortExact`: `ℱ₂ ⟶ ℱ₃` is an
  epimorphism of étale modules.
* `AlgebraicGeometry.Stack.isClosedUnderExtensions_locallyQuasicoherentFlatBaseChangeSheafFppf`
  and `AlgebraicGeometry.Stack.isWeakSerreClass_locallyQuasicoherentFlatBaseChangeSheafFppf`:
  **the extension clause of Stacks 0771 (2)** for the fppf embedding, and the weak Serre class.
* `isWeakSerreClass_locallyQuasicoherentFlatBaseChangeSheafFppf_essentiallySmall`:
  **Stacks 0771 (2)** for the fppf embedding, at an essentially small `𝒳`.
* `AlgebraicGeometry.Stack.isTriangulated_derivedLocallyQuasicoherentFlatBaseChangeSheafFppf`:
  `D_{LQCoh^fbc}(𝒪_𝒳)` is a triangulated subcategory of `D(𝒪_𝒳)`.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 03F8](https://stacks.math.columbia.edu/tag/03F8)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Stacks.CechSite

universe u v w t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-! ### The slice of `𝒳` at an object -/

/-- The functor from the slice of `𝒳` at `x` to schemes, through the scheme below. -/
abbrev overToScheme (x : 𝒳) : Over x ⥤ Scheme.{u} :=
  Over.post (X := x) (p ⋙ Over.forget (B.obj hS)) ⋙
    Over.forget ((p ⋙ Over.forget (B.obj hS)).obj x) ⋙ B.inclusion

/-- The arrows of the slice of `𝒳` at `x` lying over a morphism of schemes which is flat and
locally of finite presentation. -/
abbrev overFlatLfp (x : 𝒳) : MorphismProperty (Over x) :=
  fun _ _ f => Flat ((overToScheme B S hS p x).map f) ∧
    LocallyOfFinitePresentation ((overToScheme B S hS p x).map f)

include hp in
/-- The slice of `𝒳` at `x` has finite limits. -/
theorem hasFiniteLimits_over (x : 𝒳) : HasFiniteLimits (Over x) := by
  have : HasFiniteLimits (Over ((p ⋙ Over.forget (B.obj hS)).obj x)) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  exact ⟨fun J _ _ => Adjunction.hasLimitsOfShape_of_equivalence
    (overPostEquivalence B S hS p hp x).functor⟩

include hp in
/-- The functor from the slice of `𝒳` at `x` to schemes preserves fibre products. -/
theorem preservesPullbacks_overToScheme (x : 𝒳) :
    PreservesLimitsOfShape WalkingCospan (overToScheme B S hS p x) := by
  have := isEquivalence_overPost B S hS p hp x
  infer_instance

include hp in
/-- Lying over a flat morphism locally of finite presentation is stable under base change in the
slice at `x`. -/
theorem isStableUnderBaseChange_overFlatLfp (x : 𝒳) :
    (overFlatLfp B S hS p x).IsStableUnderBaseChange where
  of_isPullback {_ _ _ _ _ _ _ _} sq hg := by
    have := preservesPullbacks_overToScheme B S hS p hp x
    have sq' := sq.map (overToScheme B S hS p x)
    exact ⟨MorphismProperty.of_isPullback sq' hg.1, MorphismProperty.of_isPullback sq' hg.2⟩

/-- Lying over a flat morphism locally of finite presentation is stable under composition. -/
instance isStableUnderComposition_overFlatLfp (x : 𝒳) :
    (overFlatLfp B S hS p x).IsStableUnderComposition where
  comp_mem f g hf hg := by
    simp only [overFlatLfp, Functor.map_comp]
    exact ⟨MorphismProperty.comp_mem _ _ _ hf.1 hg.1, MorphismProperty.comp_mem _ _ _ hf.2 hg.2⟩

/-- The identities of the slice at `x` lie over flat morphisms locally of finite presentation. -/
instance containsIdentities_overFlatLfp (x : 𝒳) :
    (overFlatLfp B S hS p x).ContainsIdentities where
  id_mem Y := by
    simp only [overFlatLfp]
    exact ⟨inferInstance, inferInstance⟩

/-! ### The sections of a member of `LQCoh^fbc(𝒪_𝒳)` over the objects lying flatly over `x` -/

/-- The objects of the slice of `𝒳` at `x` lying flatly over `x`. -/
abbrev IsFlatOver (x : 𝒳) : ObjectProperty (Over x) :=
  fun Z => Flat (B.inclusion.map (p.map Z.hom).left)

section Identification

variable (ℱ : SheafOfModules.{u}
    (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
  (hℱ : locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp ℱ) {x : 𝒳}
  (d : QuasicoherentBelow B E h S hS p hp ℱ.val x)

include hℱ in
/-- Along an object lying flatly over `x`, the sheaf-level inverse identification
`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv` is an isomorphism. -/
theorem isIso_liftedSmallEtaleSheafInv_of_isFlatOver (Z : Over x)
    (hZ : IsFlatOver B S hS p x Z) :
    IsIso (liftedSmallEtaleSheafInv B E h S hS p hp ℱ.val Z.hom d.val d.isSheaf
      (hℱ.1.2 Z.left).choose d.iso.hom) :=
  isIso_liftedSmallEtaleSheafInv_of_isIso_sheafifiedRestrictComparison B E h S hS p hp ℱ.val
    _ d.val d.isSheaf _ d.iso.hom (Iso.isIso_hom d.iso) (hℱ.2 Z.hom hZ)

/-- **The sections of `ℱ` over an object lying flatly over `x` are those of `𝓕`**, for `𝓕` the
quasi-coherent module on the scheme below `x` with `𝓕^a ≅ ℱ|_{U_ét}`: the identification
`AlgebraicGeometry.Stack.liftedSectionsIsoOfInv`. -/
def sectionsIsoOfIsFlatOver (Z : Over x) (hZ : IsFlatOver B S hS p x Z) :
    ((Over.forget x).op ⋙ ℱ.val.presheaf).obj (op Z) ≅
      ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).op ⋙
        overPostSectionsPresheaf B S hS p x d.val d.isQuasicoherent).obj (op Z) :=
  haveI := isIso_liftedSmallEtaleSheafInv_of_isFlatOver B E h S hS p hp ℱ hℱ d Z hZ
  liftedSectionsIsoOfInv B E h S hS p hp ℱ.val Z.hom d.val d.isQuasicoherent d.isSheaf
    (hℱ.1.2 Z.left).choose d.iso

/-- The identification `AlgebraicGeometry.Stack.sectionsIsoOfIsFlatOver` commutes with the
restriction maps between objects lying flatly over `x`. -/
theorem sectionsIsoOfIsFlatOver_naturality {Z Z' : Over x} (hZ : IsFlatOver B S hS p x Z)
    (hZ' : IsFlatOver B S hS p x Z') (r : Z' ⟶ Z) :
    ((Over.forget x).op ⋙ ℱ.val.presheaf).map r.op ≫
        (sectionsIsoOfIsFlatOver B E h S hS p hp ℱ hℱ d Z' hZ').hom =
      (sectionsIsoOfIsFlatOver B E h S hS p hp ℱ hℱ d Z hZ).hom ≫
        ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).op ⋙
          overPostSectionsPresheaf B S hS p x d.val d.isQuasicoherent).map r.op := by
  have := isIso_liftedSmallEtaleSheafInv_of_isFlatOver B E h S hS p hp ℱ hℱ d Z hZ
  have := isIso_liftedSmallEtaleSheafInv_of_isFlatOver B E h S hS p hp ℱ hℱ d Z' hZ'
  have key := liftedSectionsIsoOfInv_cocycle B E h S hS p hp ℱ.val d.val d.isQuasicoherent
    d.isSheaf d.iso r.left Z.hom Z'.hom (Over.w r).symm (hℱ.1.2 Z.left).choose
    (hℱ.1.2 Z'.left).choose
  have harrow : belowArrowSite B S hS p r.left Z.hom Z'.hom (Over.w r).symm =
      (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).map r := rfl
  rw [harrow] at key
  exact key

/-- The Čech cohomology of `ℱ` along a family of the slice at `x` whose iterated fibre products
lie flatly over `x` is that of the presheaf `AlgebraicGeometry.Stack.overPostSectionsPresheaf`. -/
def cechCohomologyIsoOfIsFlatOver {Z : Over x} (G : PreZeroHypercover.{u} Z)
    [∀ (n : ℕ) (i : Fin (n + 1) → G.I₀), HasProduct fun a ↦ Over.mk (G.f (i a))]
    (hQ : ∀ (n : ℕ) (k : Fin (n + 1) → G.I₀),
      IsFlatOver B S hS p x (∏ᶜ fun j ↦ Over.mk (G.f (k j))).left) (n : ℕ) :
    cechCohomology G ((Over.forget x).op ⋙ ℱ.val.presheaf) n ≅
      cechCohomology G ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).op ⋙
        overPostSectionsPresheaf B S hS p x d.val d.isQuasicoherent) n :=
  cechCohomologyIsoOfIsoOnNerve G (IsFlatOver B S hS p x) hQ
    (sectionsIsoOfIsFlatOver B E h S hS p hp ℱ hℱ d)
    (fun {Z Z'} hZ hZ' r ↦ by
      have := sectionsIsoOfIsFlatOver_naturality B E h S hS p hp ℱ hℱ d (Z := Z) (Z' := Z') hZ hZ' r
      convert this using 3) n

end Identification

/-! ### Čech vanishing over a standard fppf covering -/

/-- The family of the slice of `𝒳` at `x` given by a family of arrows with target `x`. -/
@[simps]
def overFamily {x : 𝒳} (F : PreZeroHypercover.{u} x) : PreZeroHypercover.{u} (Over.mk (𝟙 x)) where
  I₀ := F.I₀
  X i := Over.mk (F.f i)
  f i := Over.homMk (F.f i)

/-- The Čech cohomology of a family of arrows with target `x` is that of the corresponding
family of the slice at `x`, with the coefficients restricted to the slice. -/
def cechCohomologyOverFamilyIso {x : 𝒳} (F : PreZeroHypercover.{u} x)
    [hF : ∀ (n : ℕ) (i : Fin (n + 1) → F.I₀), HasProduct fun a ↦ Over.mk (F.f (i a))]
    [∀ (n : ℕ) (i : Fin (n + 1) → (overFamily F).I₀),
      HasProduct fun a ↦ Over.mk ((overFamily F).f (i a))]
    (P : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    cechCohomology F P n ≅ cechCohomology (overFamily F) ((Over.forget x).op ⋙ P) n :=
  letI : (Over.post (X := Over.mk (𝟙 x)) (Over.forget x)).IsEquivalence :=
    (Over.iteratedSliceEquiv (Over.mk (𝟙 x))).isEquivalence_functor
  letI : ∀ (n : ℕ) (i : Fin (n + 1) → ((overFamily F).map (Over.forget x)).I₀),
      HasProduct fun a ↦ Over.mk (((overFamily F).map (Over.forget x)).f (i a)) := hF
  cechCohomologyIsoOfFunctor (Over.forget x) (overFamily F) P
    (fun n i ↦ isIso_cechProductMapOfFunctor _ _ n i) n

include hp in
/-- The slice of the slice of `𝒳` at `x` over its terminal object has finite products. -/
theorem hasFiniteProducts_overOverMkId (x : 𝒳) : HasFiniteProducts (Over (Over.mk (𝟙 x))) := by
  have := hasFiniteLimits_over B S hS p hp x
  have := Over.ConstructProducts.over_binaryProduct_of_pullback (B := Over.mk (𝟙 x))
  exact hasFiniteProducts_of_has_binary_and_terminal

include hp in
/-- **The iterated fibre products of a family lying flatly over `x` lie flatly over `x`.** -/
theorem isFlatOver_pi_overFamily {x : 𝒳} (F : PreZeroHypercover.{u} x)
    (hF : ∀ i, Flat (B.inclusion.map (p.map (F.f i)).left) ∧
      LocallyOfFinitePresentation (B.inclusion.map (p.map (F.f i)).left))
    {n : ℕ} (k : Fin (n + 1) → F.I₀) [HasProduct fun j ↦ Over.mk ((overFamily F).f (k j))] :
    IsFlatOver B S hS p x (∏ᶜ fun j ↦ Over.mk ((overFamily F).f (k j))).left := by
  have := hasFiniteLimits_over B S hS p hp x
  have := isStableUnderBaseChange_overFlatLfp B S hS p hp x
  have : (overFlatLfp B S hS p x).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have := MorphismProperty.isClosedUnderFiniteProducts_overObj (overFlatLfp B S hS p x)
    (Over.mk (𝟙 x))
  have hprod := ObjectProperty.prop_product ((overFlatLfp B S hS p x).overObj)
    (f := fun j ↦ Over.mk ((overFamily F).f (k j))) fun j ↦ hF (k j)
  have hw : (∏ᶜ fun j ↦ Over.mk ((overFamily F).f (k j))).hom.left =
      (∏ᶜ fun j ↦ Over.mk ((overFamily F).f (k j))).left.hom := by
    simpa using Over.w (∏ᶜ fun j ↦ Over.mk ((overFamily F).f (k j))).hom
  show Flat (B.inclusion.map (p.map (∏ᶜ fun j ↦ Over.mk ((overFamily F).f (k j))).left.hom).left)
  rw [← hw]
  exact hprod.1

/-- The presheaf `AlgebraicGeometry.Stack.overPostSectionsPresheaf` on the big fppf site of the
scheme below `x` is the presheaf of Stacks 03DS restricted along the inclusion into all schemes. -/
theorem overPostSectionsPresheaf_eq (x : 𝒳) (𝓕 : (p.obj x).left.1.Modules)
    (h𝓕 : 𝓕.IsQuasicoherent) :
    overPostSectionsPresheaf B S hS p x 𝓕 h𝓕 =
      (Over.post (X := (p ⋙ Over.forget (B.obj hS)).obj x) B.inclusion).op ⋙
        quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕 :=
  rfl

variable (ℱ : SheafOfModules.{u}
    (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
  (hℱ : locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp ℱ)

include hℱ in
/-- **The first Čech cohomology of a member of `LQCoh^fbc(𝒪_𝒳)` vanishes on a family of arrows
lying over a standard fppf covering.**  Let `x` lie over an affine scheme `U` and let
`{z_i ⟶ x}` be a finite family of arrows from objects over affine schemes whose image in schemes
is an fppf covering of `U`.  Then the first Čech cohomology of `ℱ` along the family vanishes
(**Stacks 03FJ**). -/
theorem isZero_cechCohomology_one_of_locallyQuasicoherentFlatBaseChangeSheaf {x : 𝒳}
    (hx : IsAffineObject B S hS p x) (F : PreZeroHypercover.{u} x) [Finite F.I₀]
    (haff : ∀ i, IsAffineObject B S hS p (F.X i))
    (hF : Presieve.ofArrows (fun i ↦ (BigFppfOver.toScheme B S hS).obj (p.obj (F.X i)))
        (fun i ↦ (BigFppfOver.toScheme B S hS).map (p.map (F.f i))) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj (p.obj x)))
    [∀ (n : ℕ) (i : Fin (n + 1) → F.I₀), HasProduct fun a ↦ Over.mk (F.f (i a))] :
    IsZero (cechCohomology F ℱ.val.presheaf 1) := by
  obtain ⟨d⟩ := nonempty_quasicoherentBelow B E h S hS p hp ℱ.val hℱ.1 x
  let := d.isQuasicoherent
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hF
  have := hasFiniteProducts_overOverMkId B S hS p hp x
  have : ∀ (n : ℕ) (i : Fin (n + 1) → (overFamily F).I₀),
      HasProduct fun a ↦ Over.mk ((overFamily F).f (i a)) := fun _ _ ↦ inferInstance
  have e₁ := cechCohomologyOverFamilyIso F ℱ.val.presheaf 1
  have hF' : ∀ i, Flat (B.inclusion.map (p.map (F.f i)).left) ∧
      LocallyOfFinitePresentation (B.inclusion.map (p.map (F.f i)).left) := fun i ↦ hF.2 i
  have hQ : ∀ (n : ℕ) (k : Fin (n + 1) → (overFamily F).I₀),
      IsFlatOver B S hS p x (∏ᶜ fun j ↦ Over.mk ((overFamily F).f (k j))).left :=
    fun n k ↦ isFlatOver_pi_overFamily B S hS p hp F hF' k
  have e₂ := cechCohomologyIsoOfIsFlatOver B E h S hS p hp ℱ hℱ d (overFamily F) hQ 1
  rw [overPostSectionsPresheaf_eq] at e₂
  let w := Over.post (X := x) (p ⋙ Over.forget (B.obj hS))
  let v := Over.post (X := (p ⋙ Over.forget (B.obj hS)).obj x) B.inclusion
  have := isEquivalence_overPost B S hS p hp x
  have : HasFiniteLimits B.Schemes := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesFiniteLimits B.inclusion :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks B.inclusion
  have e₃ := cechCohomologyIsoOfFunctor w (overFamily F)
    (v.op ⋙ quasiCoherentPresheafFunctor (p.obj x).left.1 d.val)
    (fun n i ↦ isIso_cechProductMapOfFunctor _ _ n i) 1
  have e₄ := cechCohomologyIsoOfFunctor v ((overFamily F).map w)
    (quasiCoherentPresheafFunctor (p.obj x).left.1 d.val)
    (fun n i ↦ isIso_cechProductMapOfFunctor _ _ n i) 1
  have : IsAffine (v.obj (w.obj (Over.mk (𝟙 x)))).left := hx
  have hstd : IsStandardCovering .fppf
      (fun i ↦ ((((overFamily F).map w).map v).X i).left)
      (fun i ↦ ((((overFamily F).map w).map v).f i).left) :=
    { finite_index := inferInstanceAs (Finite F.I₀)
      affine_source := haff
      jointly_surjective := by
        refine Set.eq_univ_of_forall fun y ↦ ?_
        obtain ⟨i, hi⟩ := hF.1 y
        exact Set.mem_iUnion.2 ⟨i, hi⟩
      standard := fun i ↦ by
        have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (F.X i))) := haff i
        have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) := hx
        exact ⟨(hF.2 i).1, (hF.2 i).2,
          inferInstanceAs (QuasiCompact ((BigFppfOver.toScheme B S hS).map (p.map (F.f i)))),
          inferInstanceAs (QuasiSeparated ((BigFppfOver.toScheme B S hS).map (p.map (F.f i))))⟩ }
  have hzero := isZero_cechCohomology_succ_quasiCoherentPresheaf
    (v.obj (w.obj (Over.mk (𝟙 x)))) .fppf d.val (((overFamily F).map w).map v) hstd 1 one_pos
  exact (((hzero.of_iso e₄.symm).of_iso e₃.symm).of_iso e₂).of_iso e₁

/-! ### Surjectivity on sections over an object lying over an affine scheme -/

section Surjectivity

/-- The finite families of arrows with target `x` from objects lying over affine schemes which lie
over an fppf covering in schemes, and generate a covering sieve. -/
def affineFppfFamilies (x : 𝒳) : Set (PreZeroHypercover.{u} x) :=
  {F | Finite F.I₀ ∧ (∀ i, IsAffineObject B S hS p (F.X i)) ∧
    Presieve.ofArrows (fun i ↦ (BigFppfOver.toScheme B S hS).obj (p.obj (F.X i)))
        (fun i ↦ (BigFppfOver.toScheme B S hS).map (p.map (F.f i))) ∈
      Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj (p.obj x)) ∧
    F.sieve₀ ∈ BigFppfOver.associatedTopology B S hS p .fppf x}

include hp in
/-- Over an object lying over an affine scheme, the families of
`AlgebraicGeometry.Stack.affineFppfFamilies` are cofinal among the fppf coverings. -/
theorem exists_mem_affineFppfFamilies_le {x : 𝒳} (hx : IsAffineObject B S hS p x)
    {R : Sieve x} (hR : R ∈ BigFppfOver.associatedTopology B S hS p .fppf x) :
    ∃ F : PreZeroHypercover.{u} x, F ∈ affineFppfFamilies B S hS p x ∧ F.sieve₀ ≤ R := by
  obtain ⟨n, z, φ, haff, hRφ, hcov, hfppf⟩ :=
    FibredSite.exists_finite_affine_fppf_ofArrows_le B S hS p hp hx hR
  let F : PreZeroHypercover.{u} x :=
    { I₀ := ULift.{u} (Fin n), X := fun i ↦ z i.down, f := fun i ↦ φ i.down }
  refine ⟨F, ⟨inferInstanceAs (Finite (ULift (Fin n))), fun i ↦ haff i.down,
    Scheme.mem_fppfPrecoverage_of_equiv Equiv.ulift hfppf, ?_⟩, ?_⟩
  · refine (BigFppfOver.associatedTopology B S hS p .fppf).superset_covering ?_ hcov
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact F.sieve₀_f ⟨i⟩
  · rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact hRφ i.down

variable [HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
  [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The forgetful functor from fppf modules to fppf abelian sheaves sends a short exact sequence to
a short exact sequence. -/
theorem shortExact_map_toSheaf
    {T : ShortComplex (SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf))}
    (hT : T.ShortExact) :
    (T.map (SheafOfModules.toSheaf _)).ShortExact := by
  have := hT.mono_f
  have := hT.epi_g
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact hT.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance
  · exact (SheafOfModules.toSheaf _).map_mono T.f
  · exact (SheafOfModules.toSheaf _).map_epi T.g

/-- **Stacks 03F8 at an object lying over an affine scheme.**  Let `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` be a
short exact sequence of modules on the fppf site of `𝒳` with `ℱ₁` in `LQCoh^fbc(𝒪_𝒳)`.  Over an
object `x` lying over an affine scheme, `ℱ₂(x) ⟶ ℱ₃(x)` is surjective. -/
theorem surjective_app_of_shortExact_of_isAffineObject
    {T : ShortComplex (SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf))}
    (hT : T.ShortExact) (h₁ : locallyQuasicoherentFlatBaseChangeSheafFppf B E h S hS p hp T.X₁)
    {x : 𝒳} (hx : IsAffineObject B S hS p x) :
    Function.Surjective (((PresheafOfModules.toPresheaf _).map T.g.val).app (op x)) := by
  have := hasFiniteLimits_over B S hS p hp x
  exact surjective_on_sections_of_isZero_cechCohomology.{u, w, v, u}
    (BigFppfOver.associatedTopology B S hS p .fppf)
    (T.map (SheafOfModules.toSheaf _)) (shortExact_map_toSheaf B S hS p hp hT) x
    (affineFppfFamilies B S hS p x) (fun _ hF ↦ hF.2.2.2)
    (fun _ hR ↦ exists_mem_affineFppfFamilies_le B S hS p hp hx hR)
    (fun _ _ _ _ ↦ inferInstance)
    (fun F hF ↦ by
      have := hF.1
      have := isZero_cechCohomology_one_of_locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp _
        h₁ hx F hF.2.1 hF.2.2.1
      have heq : (sheafToPresheaf (BigFppfOver.associatedTopology B S hS p .fppf)
          AddCommGrpCat.{u}).obj (T.map (SheafOfModules.toSheaf _)).X₁ =
            ((fppfToEtaleSheafOfModules B S hS p hp).obj T.X₁).val.presheaf := rfl
      rw [heq]
      exact this)

/-- **A short exact sequence of fppf modules with first term in `LQCoh^fbc(𝒪_𝒳)` stays
surjective in the étale topology.** -/
theorem epi_fppfToEtaleSheafOfModules_map_g_of_shortExact
    {T : ShortComplex (SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf))}
    (hT : T.ShortExact) (h₁ : locallyQuasicoherentFlatBaseChangeSheafFppf B E h S hS p hp T.X₁) :
    Epi ((fppfToEtaleSheafOfModules B S hS p hp).map T.g) := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {U} s ↦ ?_⟩
  have := (isDenseSubsite_affineInclusion_etale B S hS p hp).isCoverDense'
  have hcov := (AffineCategory.inclusion B S hS p).is_cover_of_isCoverDense
    (associatedTopology B S hS p B.etaleTopology) U
  refine (associatedTopology B S hS p (etaleTopology B)).superset_covering ?_ hcov
  rintro V f ⟨⟨Y, l, m, hfac⟩⟩
  obtain ⟨t, ht⟩ := surjective_app_of_shortExact_of_isAffineObject B E h S hS p hp hT h₁ Y.property
    (((PresheafOfModules.toPresheaf _).obj T.X₃.val).map m.op s)
  refine ⟨((PresheafOfModules.toPresheaf _).obj T.X₂.val).map l.op t, ?_⟩
  have hnat := NatTrans.naturality_apply ((PresheafOfModules.toPresheaf _).map T.g.val) l.op t
  refine hnat.trans ?_
  show ((PresheafOfModules.toPresheaf _).obj T.X₃.val).map l.op
    (((PresheafOfModules.toPresheaf _).map T.g.val).app (op Y.obj) t) = _
  rw [ht]
  show (((PresheafOfModules.toPresheaf _).obj T.X₃.val).map m.op ≫
      ((PresheafOfModules.toPresheaf _).obj T.X₃.val).map l.op) s =
    ((PresheafOfModules.toPresheaf _).obj T.X₃.val).map f.op s
  rw [← Functor.map_comp, ← op_comp, hfac]

variable [HasSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
  [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The extension clause of Stacks 0771 (2) for `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`.**  An extension
in `Mod(𝒪_𝒳)` of two members of `LQCoh^fbc(𝒪_𝒳)` is a member. -/
instance isClosedUnderExtensions_locallyQuasicoherentFlatBaseChangeSheafFppf :
    (locallyQuasicoherentFlatBaseChangeSheafFppf B E h S hS p hp).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {T} hT h₁ h₃ := by
    have := hT.mono_f
    have := epi_fppfToEtaleSheafOfModules_map_g_of_shortExact B E h S hS p hp hT h₁
    have hT' : (T.map (fppfToEtaleSheafOfModules B S hS p hp)).ShortExact :=
      ShortComplex.ShortExact.mk'
        (hT.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance)
        ((fppfToEtaleSheafOfModules B S hS p hp).map_mono T.f) ‹_›
    exact (locallyQuasicoherentFlatBaseChangeSheaf B E h S hS p hp).prop_X₂_of_shortExact hT' h₁ h₃

/-- The weak Serre property of `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`, with the flat base change
property read on sheaves of modules as in the source: `LQCoh^fbc(𝒪_𝒳)` is a weak Serre
subcategory of the modules on the fppf site. -/
instance isWeakSerreClass_locallyQuasicoherentFlatBaseChangeSheafFppf :
    (locallyQuasicoherentFlatBaseChangeSheafFppf B E h S hS p hp).IsWeakSerreClass where

section Derived

variable [HasDerivedCategory.{t}
  (SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf))]

/-- The subcategory `D_{LQCoh^fbc}(𝒪_𝒳) ⊆ D(𝒪_𝒳)` of the complexes of modules on the fppf site
all of whose cohomology modules lie in `LQCoh^fbc(𝒪_𝒳)`, with the flat base change property read
on sheaves of modules as in the source. -/
abbrev derivedLocallyQuasicoherentFlatBaseChangeSheafFppf :
    ObjectProperty (DerivedCategory
      (SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf))) :=
  DerivedCategoryB.derivedCategoryB (locallyQuasicoherentFlatBaseChangeSheafFppf B E h S hS p hp)

/-- **`D_{LQCoh^fbc}(𝒪_𝒳)` is a triangulated subcategory of `D(𝒪_𝒳)`.** -/
theorem isTriangulated_derivedLocallyQuasicoherentFlatBaseChangeSheafFppf :
    (derivedLocallyQuasicoherentFlatBaseChangeSheafFppf B E h S hS p hp).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated _
    (WeakSerre.isWeakSerre_of_isWeakSerreClass _)

end Derived

end Surjectivity

/-! ### At the seating of an essentially small `𝒳` -/

section EssentiallySmall

variable {𝒴 : Type (u + 1)} [Category.{u} 𝒴] [EssentiallySmall.{u} 𝒴]
  (q : 𝒴 ⥤ BigFppfOver B S hS) (hq : q.IsFiberedInGroupoids)

/-- On an essentially small site, sheafification of abelian groups exists and `W` is the class of
locally bijective morphisms. -/
private theorem hasSheafify_and_wEqualsLocallyBijective_of_essentiallySmall
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u} C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{u} ∧ J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  ⟨hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _,
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _⟩

/-- **Stacks 0771 (2) for the embedding `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)`**, with the flat base change
property read on sheaves of modules as in the source: `LQCoh^fbc(𝒪_𝒳)` is a weak Serre
subcategory of the modules on the fppf site.  The sheafification conditions under which
`Mod(𝒪_𝒳)` and `Mod(𝒳_étale, 𝒪_𝒳)` are abelian hold because `𝒳` is essentially small. -/
theorem isWeakSerreClass_locallyQuasicoherentFlatBaseChangeSheafFppf_essentiallySmall :
    letI : HasSheafify (associatedTopology B S hS q (etaleTopology B)) AddCommGrpCat.{u} :=
      hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
    letI : (associatedTopology B S hS q (etaleTopology B)).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
      GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _
    letI : HasSheafify (BigFppfOver.associatedTopology B S hS q .fppf) AddCommGrpCat.{u} :=
      hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
    letI : (BigFppfOver.associatedTopology B S hS q .fppf).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
      GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _
    (locallyQuasicoherentFlatBaseChangeSheafFppf B E h S hS q hq).IsWeakSerreClass := by
  obtain ⟨_, _⟩ := hasSheafify_and_wEqualsLocallyBijective_of_essentiallySmall
    (associatedTopology B S hS q (etaleTopology B))
  obtain ⟨_, _⟩ := hasSheafify_and_wEqualsLocallyBijective_of_essentiallySmall
    (BigFppfOver.associatedTopology B S hS q .fppf)
  exact isWeakSerreClass_locallyQuasicoherentFlatBaseChangeSheafFppf B E h S hS q hq

end EssentiallySmall

end AlgebraicGeometry.Stack

end
