module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleTotalSpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreBaseChangeCharts
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleClassifyingMap
public import StacksFrontier.AlgebraicGeometry.RelativeSpecClosedImmersion.AlgebraHomComparison
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBaseChangeExcess

/-!
# The normal cone inside the vector bundle of a virtual normal bundle, under base change

Let `Z' = Z ×_X X'` be a cartesian square of schemes with `i : Z ⟶ X` and `i' : Z' ⟶ X'` closed
immersions, `g : Z' ⟶ Z`, `f : X' ⟶ X`, and let `𝒩` be a virtual normal bundle for `i`, with base
change `g^*𝒩` (Stacks 0FBJ). The normal cones are compared by `C_{Z'}X' ⟶ C_ZX`
(`Stacks.Chow.normalConeBaseChangeMap`), the vector bundles by `V(g^*𝒩) ⟶ V(𝒩)`. This file proves
that the canonical closed immersions `ι : C_ZX ⟶ V(𝒩)` and `ι' : C_{Z'}X' ⟶ V(g^*𝒩)` of the
construction preceding Stacks 0FBK are compatible:

  `C_{Z'}X' ⟶ C_ZX ⟶ V(𝒩)  =  C_{Z'}X' ⟶ V(g^*𝒩) ⟶ V(𝒩)`.

Both sides are morphisms over `Z` into the vector bundle `V(𝒩) = Spec_Z(Sym(𝒩^∨))`, so they are
determined by their classifying maps `𝒩^∨ ⟶ (C_{Z'}X' ⟶ Z)_* 𝒪`. Those factor through the
degree-one part `𝒞_{Z/X} ⟶ 𝒞_{Z/X,*}` of the conormal algebra, and the statement becomes the
compatibility of the comparison of the normal cones with the conormal comparison map
`g^*𝒞_{Z/X} ⟶ 𝒞_{Z'/X'}` of Stacks 0473. That is checked on the affine charts of the normal cones,
where both are computed on degree-one classes of the associated graded rings: the class of
`a ∈ I` goes to the class of its image in `I'`.

## Main results

* `Stacks.Chow.normalConeBaseChangeMap_comp_normalConeEmbedding` — the compatibility of `ι` with
  base change.
* `Stacks.Chow.conormalDegreeOneIncl_comp_pushforwardAlgebraMap_normalConeBaseChangeOver` — the
  comparison of the normal cones on degree-one classes of the conormal algebra is the conormal
  comparison map of Stacks 0473, transposed along `g^* ⊣ g_*`.
* `Stacks.Chow.vectorBundleClassifyingMap_normalConeEmbedding` — the classifying module map of
  `ι` is `σ` followed by the degree-one inclusion of the conormal algebra.
* `Stacks.Chow.normalCone_sections_ext` — sections of the normal cone are determined on the
  affine charts.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0637](https://stacks.math.columbia.edu/tag/0637)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence Stacks.SymAlgSheaf Stacks.RelativeSpec.AlgebraSheaf
open Stacks.AlgebraicGeometry.ReflexiveModules AlgebraicGeometry.Scheme.Modules
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AffineAlgebraEquivalence

/-- **Sections of a relative spectrum over an affine chart**: the chart of `Spec_S(A)` over an
affine open `U` of `S` carries the identification `A(U) ≅ Γ(Spec_S(A), π⁻¹U)` of Stacks 01LX (3)
to the identification `A(U) ≅ Γ(Spec A(U), ⊤)`. -/
theorem ι_appLE_pushforwardAlgebraIso_inv {S : Scheme.{u}} (A : Stacks.RelativeSpec.AlgebraSheaf S)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A] (U : S.affineOpens)
    (x : A.right.obj.obj (op U.1)) :
    ((colimit.ι (relativeSpecGluingData A).functor U).appLE
        ((relativeSpecGluingData A).toBase ⁻¹ᵁ U.1) ⊤
        (le_ι_preimage (relativeSpecGluingData A) U)).hom
        ((pushforwardAlgebraIso A).inv.right.hom.app (op U.1) x) =
      (Scheme.ΓSpecIso (A.right.obj.obj (op U.1))).inv.hom x := by
  have h := congrArg (fun φ => φ.hom ((pushforwardAlgebraIso A).inv.right.hom.app (op U.1) x))
    (pushforwardSheafIso_hom_app A U)
  have h' : ((pushforwardAlgebraIso A).hom.right.hom.app (op U.1)).hom
      ((pushforwardAlgebraIso A).inv.right.hom.app (op U.1) x) = x :=
    congrArg (fun φ : A ⟶ A => (φ.right.hom.app (op U.1)).hom x)
      (pushforwardAlgebraIso A).inv_hom_id
  change ((pushforwardAlgebraIso A).hom.right.hom.app (op U.1)).hom _ =
    ((sectionsIso A U).hom).hom _ at h
  rw [h'] at h
  have h2 : (sectionsIso A U).hom.hom ((pushforwardAlgebraIso A).inv.right.hom.app (op U.1) x) =
      (Scheme.ΓSpecIso (A.right.obj.obj (op U.1))).hom.hom
        (((colimit.ι (relativeSpecGluingData A).functor U).appLE
          ((relativeSpecGluingData A).toBase ⁻¹ᵁ U.1) ⊤
          (le_ι_preimage (relativeSpecGluingData A) U)).hom
          ((pushforwardAlgebraIso A).inv.right.hom.app (op U.1) x)) := rfl
  rw [h2] at h
  refine Eq.trans ?_ (congrArg (Scheme.ΓSpecIso (A.right.obj.obj (op U.1))).inv.hom h).symm
  exact (congrArg (fun φ => CommRingCat.Hom.hom φ _)
    (Iso.hom_inv_id (Scheme.ΓSpecIso (A.right.obj.obj (op U.1))))).symm

end Stacks.AffineAlgebraEquivalence

namespace Stacks.Chow

section Sections

variable {S : Scheme.{u}}

/-- A composite of morphisms of sheaves of modules, on a local section. -/
theorem modules_comp_val_app_hom {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N P : SheafOfModules.{u} R} (a : M ⟶ N) (b : N ⟶ P) (W : Cᵒᵖ)
    (x : M.val.obj W) : ((a ≫ b).val.app W).hom x = (b.val.app W).hom ((a.val.app W).hom x) :=
  rfl

/-- **Two morphisms of sheaves of modules agreeing on the sections over a basis are equal.** -/
theorem sheafOfModules_hom_ext_of_isBasis {T : Type u} [TopologicalSpace T]
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    {M N : SheafOfModules.{u} R} (φ ψ : M ⟶ N) {ι : Type*} {B : ι → TopologicalSpace.Opens T}
    (hB : TopologicalSpace.Opens.IsBasis (Set.range B))
    (h : ∀ (j : ι) (x : M.val.obj (op (B j))),
      (φ.val.app (op (B j))).hom x = (ψ.val.app (op (B j))).hom x) : φ = ψ := by
  refine SheafOfModules.hom_ext ((PresheafOfModules.toPresheaf _).map_injective ?_)
  refine TopCat.Sheaf.hom_ext (X := TopCat.of T) (B := B) _
    (show TopCat.Sheaf _ (TopCat.of T) from ⟨_, N.isSheaf⟩) hB (fun j => ?_)
  ext x
  exact h j x

/-- The unit of `g^* ⊣ g_*` followed by a direct image is the transpose along the adjunction of
ringed spaces. -/
theorem pullbackPushforwardAdjunction_unit_comp_pushforward_map {T : Scheme.{u}} (g : T ⟶ S)
    (M : S.Modules) (N : T.Modules) (φ : (modulePullback g.toLRSHom.toShHom).obj M ⟶ N) :
    (pullbackPushforwardAdjunction g).unit.app M ≫ (pushforward g).map φ =
      (modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv _ _ φ :=
  (Adjunction.homEquiv_unit _ _ _ _).symm

end Sections

section Embedding

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]

/-- The degree-one inclusion `𝒞_{Z/X,1} ⟶ 𝒞_{Z/X,*}` of the conormal algebra, as a morphism of
modules: the generator of `Sym(𝒞_{Z/X,1})` followed by the canonical map
`Sym(𝒞_{Z/X,1}) ⟶ 𝒞_{Z/X,*}`. -/
def conormalDegreeOneIncl (i : Z ⟶ X) [IsImmersion i] :
    Stacks.Conormal.conormalSheafDegreeOne i ⟶
      underlyingModule (Stacks.Conormal.conormalAlgebraSheaf i) :=
  symmetricAlgebraSheafι (Stacks.Conormal.conormalSheafDegreeOne i) ≫
    underlyingModuleMap (Stacks.Conormal.conormalSymmetricAlgebraSheafHom i)

/-- The degree-one inclusion of the conormal algebra carries a degree-one local section to its
image in the ungraded realization. -/
theorem conormalDegreeOneIncl_app (i : Z ⟶ X) [IsImmersion i] (W : Z.Opensᵒᵖ)
    (x : (Stacks.Conormal.conormalSheafDegreeOne i).val.obj W) :
    (conormalDegreeOneIncl i).val.app W x =
      (Stacks.Conormal.conormalAlgebra i).algebra.ungradedIncl (1 : ℤ) x := by
  change ((SheafOfModules.GradedAlgebra.ungradedSheafMap
      (Stacks.Conormal.conormalSymmetricHom i)).hom.app W).hom
      ((Scheme.Modules.symmetricAlgebra Z _).ungradedIncl 1
        ((Scheme.Modules.symmetricAlgebraGen Z _).val.app W x)) = _
  refine (SheafOfModules.GradedAlgebra.ungradedIncl_ungradedSheafMap _ 1 _).trans ?_
  exact congrArg _ (congrArg (fun φ => φ.val.app W x) (Stacks.Conormal.conormalSymmetricHom_gen i))

/-- The canonical closed immersion `C_ZX ⟶ N_ZX` of Stacks 0637, as a morphism over `Z`. -/
abbrev normalConeToNormalBundleOver (i : Z ⟶ X) [IsImmersion i] :
    (Over.mk (Stacks.Conormal.normalConeToBase i) : Over Z) ⟶
      vectorBundleOver Z (F := Stacks.Conormal.conormalSheafDegreeOne i) :=
  Over.homMk (Stacks.Conormal.normalConeToNormalBundle i)
    (Stacks.Conormal.normalConeToNormalBundle_toBase i)

/-- The canonical map of `C_ZX ⟶ N_ZX` on pushed-forward structure sheaves is the canonical map
`Sym(𝒞_{Z/X,1}) ⟶ 𝒞_{Z/X,*}`, read through Stacks 01LX (3). -/
theorem pushforwardAlgebraMap_normalConeToNormalBundleOver (i : Z ⟶ X) [IsImmersion i] :
    pushforwardAlgebraMap (normalConeToNormalBundleOver i) =
      (vectorBundlePushforwardIso Z (F := Stacks.Conormal.conormalSheafDegreeOne i)).hom ≫
        Stacks.Conormal.conormalSymmetricAlgebraSheafHom i ≫
          (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i)).inv := by
  have h : normalConeToNormalBundleOver i =
      relativeSpecMapOfAlgebraHom (Stacks.Conormal.normalBundleAlgebra i)
        (Stacks.Conormal.conormalAlgebraSheaf i)
        (Stacks.Conormal.conormalSymmetricAlgebraSheafHom i) :=
    Over.OverMorphism.ext (Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom_eq _ _ _ _)
  rw [h]
  exact pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom _ _ _

/-- The classifying module map of `C_ZX ⟶ N_ZX` is the degree-one inclusion of the conormal
algebra. -/
theorem vectorBundleClassifyingMap_normalConeToNormalBundleOver (i : Z ⟶ X) [IsImmersion i] :
    vectorBundleClassifyingMap (Stacks.Conormal.conormalSheafDegreeOne i)
        (normalConeToNormalBundleOver i) =
      conormalDegreeOneIncl i ≫
        underlyingModuleMap
          (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i)).inv := by
  rw [vectorBundleClassifyingMap, pushforwardAlgebraMap_normalConeToNormalBundleOver]
  refine (congrArg (fun k => _ ≫ underlyingModuleMap k) (Iso.inv_hom_id_assoc _ _)).trans ?_
  exact (congrArg (_ ≫ ·) ((underlyingModuleFunctor Z).map_comp _ _)).trans
    (Category.assoc _ _ _).symm

/-- **The classifying module map of `ι : C_ZX ⟶ V(𝒩)`**, as the morphism of schemes over `Z`
`C_ZX ⟶ N_ZX ⟶ V(𝒩)`: it is `σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` followed by the degree-one inclusion of the
conormal algebra. -/
theorem vectorBundleClassifyingMap_normalConeEmbedding (𝒩 : VirtualNormalBundle i) :
    vectorBundleClassifyingMap (dualSheaf 𝒩.bundle)
        (normalConeToNormalBundleOver i ≫ vectorBundleMap Z 𝒩.conormalDegreeOneSurjection) =
      𝒩.conormalDegreeOneSurjection ≫ conormalDegreeOneIncl i ≫
        underlyingModuleMap (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i)).inv :=
  (vectorBundleClassifyingMap_comp_vectorBundleMap (dualSheaf 𝒩.bundle)
    𝒩.conormalDegreeOneSurjection (normalConeToNormalBundleOver i)).trans
    (congrArg (_ ≫ ·) (vectorBundleClassifyingMap_normalConeToNormalBundleOver i))

end Embedding

section Separation

variable {Z' X' : Scheme.{u}} (i' : Z' ⟶ X') [IsClosedImmersion i']

/-- The chart of `C_{Z'}X'` over an affine open `U'` lands in the part of `C_{Z'}X'` over `U'`. -/
theorem top_le_normalConeChart_preimage (U' : X'.affineOpens) :
    (⊤ : (normalConeChartSource i' U').Opens) ≤
      normalConeChart i' U' ⁻¹ᵁ (normalConeToX i' ⁻¹ᵁ U'.1) := by
  intro x _
  change (normalConeChart i' U' ≫ normalConeToX i') x ∈ U'.1
  rw [← (isPullback_normalConeChart i' U').w]
  exact (normalConeChartProj i' U' x).2

/-- The part of `C_{Z'}X'` over an affine open `U'` is the range of its chart. -/
theorem opensRange_normalConeChart (U' : X'.affineOpens) :
    (normalConeChart i' U').opensRange = normalConeToX i' ⁻¹ᵁ U'.1 := by
  rw [AlgebraicGeometry.Proj.opensRange_eq_preimage_of_isPullback
      (isPullback_normalConeChart i' U'),
    Scheme.Opens.opensRange_ι]

/-- **Sections of the normal cone are determined on the affine charts.** Two sections of `C_{Z'}X'`
over an open `O` lying over an open `T ⊆ X'` agree if they agree on the chart of `C_{Z'}X'` over
every affine open `U' ⊆ T`. -/
theorem normalCone_sections_ext {O : (Stacks.Conormal.normalCone i').Opens} (T : X'.Opens)
    (hle : ∀ U' : X'.affineOpens, U'.1 ≤ T → normalConeToX i' ⁻¹ᵁ U'.1 ≤ O)
    (hcov : O ≤ normalConeToX i' ⁻¹ᵁ T) {a b : Γ(Stacks.Conormal.normalCone i', O)}
    (h : ∀ (U' : X'.affineOpens) (hU' : U'.1 ≤ T),
      ((normalConeChart i' U').appLE O ⊤ ((top_le_normalConeChart_preimage i' U').trans
        ((normalConeChart i' U').preimage_mono (hle U' hU')))).hom a =
      ((normalConeChart i' U').appLE O ⊤ ((top_le_normalConeChart_preimage i' U').trans
        ((normalConeChart i' U').preimage_mono (hle U' hU')))).hom b) : a = b := by
  refine TopCat.Sheaf.eq_of_locally_eq' (Stacks.Conormal.normalCone i').sheaf
    (fun j : {U' : X'.affineOpens // U'.1 ≤ T} => normalConeToX i' ⁻¹ᵁ j.1.1) O
    (fun j => homOfLE (hle j.1 j.2)) ?_ a b (fun j => ?_)
  · intro x hx
    obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hU'T⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
      (hcov hx) T.2
    exact (TopologicalSpace.Opens.mem_iSup).2 ⟨⟨⟨U', hU'⟩, hU'T⟩, hxU'⟩
  · have hinj : Function.Injective ((normalConeChart i' j.1).appLE
        (normalConeToX i' ⁻¹ᵁ j.1.1) ⊤ (top_le_normalConeChart_preimage i' j.1)).hom := by
      have e := (normalConeChart i' j.1).appIso_hom' ⊤
      have hW : (normalConeChart i' j.1) ''ᵁ ⊤ = normalConeToX i' ⁻¹ᵁ j.1.1 := by
        rw [Scheme.Hom.image_top_eq_opensRange, opensRange_normalConeChart]
      have key : ∀ (W : (Stacks.Conormal.normalCone i').Opens)
          (hW : (normalConeChart i' j.1) ''ᵁ ⊤ = W)
          (hle : ⊤ ≤ normalConeChart i' j.1 ⁻¹ᵁ W),
          Function.Injective ((normalConeChart i' j.1).appLE W ⊤ hle).hom := by
        rintro W rfl hle
        rw [← e]
        exact ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).1
      exact key _ hW _
    apply hinj
    have hm : ∀ x : Γ(Stacks.Conormal.normalCone i', O),
        ((normalConeChart i' j.1).appLE (normalConeToX i' ⁻¹ᵁ j.1.1) ⊤
          (top_le_normalConeChart_preimage i' j.1)).hom
          (((Stacks.Conormal.normalCone i').presheaf.map (homOfLE (hle j.1 j.2)).op).hom x) =
        ((normalConeChart i' j.1).appLE O ⊤ ((top_le_normalConeChart_preimage i' j.1).trans
          ((normalConeChart i' j.1).preimage_mono (hle j.1 j.2)))).hom x := fun x => by
      rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    exact (hm a).trans ((h j.1 j.2).trans (hm b).symm)

/-- **Sections of the conormal algebra on a chart of the normal cone.** A section of the
conormal algebra over an open `T ⊇ Z' ∩ U'`, viewed on `C_{Z'}X'` over `T`, pulled back to the
chart of `C_{Z'}X'` over `U'`, is its restriction to `Z' ∩ U'`. -/
theorem normalConeChart_appLE_pushforwardAlgebraIso_inv (U' : X'.affineOpens) (T : Z'.Opens)
    (hT : (subschemeAffineOpen i' U').1 ≤ T)
    (y : (Stacks.Conormal.conormalAlgebraSheaf i').right.obj.obj (op T))
    (h₁ : ⊤ ≤ normalConeChart i' U' ⁻¹ᵁ
      ((relativeSpecGluingData (Stacks.Conormal.conormalAlgebraSheaf i')).toBase ⁻¹ᵁ T)) :
    ((normalConeChart i' U').appLE _ ⊤ h₁).hom
        ((pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i')).inv.right.hom.app
          (op T) y) =
      (Scheme.ΓSpecIso _).inv.hom
        (((Stacks.Conormal.conormalAlgebraSheaf i').right.obj.map (homOfLE hT).op).hom y) := by
  have hres := congrArg (fun φ => CommRingCat.Hom.hom φ y)
    ((pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i')).inv.right.hom.naturality
      (homOfLE hT).op)
  have hmap : ((normalConeChart i' U').appLE _ ⊤ h₁) =
      (Stacks.Conormal.normalCone i').presheaf.map
          (homOfLE
            ((relativeSpecGluingData (Stacks.Conormal.conormalAlgebraSheaf i')).toBase.preimage_mono
              hT)).op ≫
        (normalConeChart i' U').appLE _ ⊤ (by exact (le_ι_preimage
          (relativeSpecGluingData (Stacks.Conormal.conormalAlgebraSheaf i'))
            (subschemeAffineOpen i' U'))) :=
    (Scheme.Hom.map_appLE _ _ _).symm
  refine (congrArg (fun φ => CommRingCat.Hom.hom φ
    ((pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i')).inv.right.hom.app
      (op T) y)) hmap).trans ?_
  exact (congrArg ((normalConeChart i' U').appLE _ ⊤ (by exact (le_ι_preimage
      (relativeSpecGluingData (Stacks.Conormal.conormalAlgebraSheaf i'))
        (subschemeAffineOpen i' U')))).hom hres.symm).trans
    (ι_appLE_pushforwardAlgebraIso_inv (Stacks.Conormal.conormalAlgebraSheaf i')
      (subschemeAffineOpen i' U') _)

end Separation

/-- The affine model of an affine chart of a closed immersion, with its ideal named as the kernel
ideal of the chart. -/
private theorem exists_chartIdeal_affineModel {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.affineOpens) :
    ∃ e : pullback i U.1.ι ≅ Spec (.of (Γ(X, U) ⧸ Stacks.Conormal.chartIdeal i U)),
      pullback.snd i U.1.ι ≫ U.2.isoSpec.hom =
        e.hom ≫ Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Stacks.Conormal.chartIdeal i U))) := by
  obtain ⟨I, e, he⟩ := Stacks.Conormal.exists_affineModel i U.1 U.2
  obtain rfl : Stacks.Conormal.chartIdeal i U = I := by
    rw [Stacks.Conormal.chartIdeal, Scheme.Hom.app_eq_appLE]
    exact Stacks.Conormal.ker_appLE_eq_of_affineModel i U.1 U.2 I e he
  exact ⟨e, he⟩

section Charts

variable {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ X')
  [IsClosedImmersion i'] (g : Z' ⟶ Z) (f : X' ⟶ X) (hcomm : i' ≫ f = g ≫ i)
  {U : X.affineOpens} {U' : X'.affineOpens} (hUU' : U'.1 ≤ f ⁻¹ᵁ U.1)

include hcomm in
/-- The comparison `φ : Γ(X, U) ⟶ Γ(X', U')` maps the ideal of `Z ∩ U` into that of `Z' ∩ U'`. -/
theorem affineBaseChangeMap_mem_chartIdeal {a : Γ(X, U.1)}
    (ha : a ∈ Stacks.Conormal.chartIdeal i U) :
    affineBaseChangeMap f hUU' a ∈ Stacks.Conormal.chartIdeal i' U' := by
  have h := map_ideal_ker_le f hUU' i i' g hcomm
  rw [← chartIdeal_eq_ker_ideal, ← chartIdeal_eq_ker_ideal] at h
  exact h (Ideal.mem_map_of_mem _ ha)

/-- The comparison of the conormal algebras on the charts, on the classes of the associated graded
ring: it is the map `Gr_I(A) ⟶ Gr_{I'}(A')` induced by `φ : Γ(X, U) ⟶ Γ(X', U')`. -/
theorem conormalSectionsBaseChange_exceptionalChartSectionsIso
    (z : AssociatedGraded.gradedRing (i.ker.ideal U)) :
    (conormalSectionsBaseChange f i i' g hcomm hUU').hom
        ((exceptionalChartSectionsIso i U).hom.hom
          ((conormalEquivInfinityChartFibre (i.ker.ideal U)).toRingHom z)) =
      (exceptionalChartSectionsIso i' U').hom.hom
        ((conormalEquivInfinityChartFibre (i'.ker.ideal U')).toRingHom
          ((AssociatedGraded.gradedRingMapOfRingHom (affineBaseChangeMap f hUU')
            (map_ideal_ker_le f hUU' i i' g hcomm)) z)) := by
  change (exceptionalChartSectionsIso i' U').hom.hom (infinityChartFibreMap
    (affineBaseChangeMap f hUU') (map_ideal_ker_le f hUU' i i' g hcomm)
    ((exceptionalChartSectionsIso i U).inv.hom ((exceptionalChartSectionsIso i U).hom.hom
      ((conormalEquivInfinityChartFibre (i.ker.ideal U)).toRingHom z)))) = _
  rw [Iso.hom_inv_id_apply]
  exact congrArg (exceptionalChartSectionsIso i' U').hom.hom
    (infinityChartFibreMap_conormalEquiv _ _ z)

/-- **The comparison of the conormal algebras on degree-one classes**: the degree-one class of
`a ∈ I` goes to the degree-one class of `φ(a) ∈ I'`. -/
theorem conormalSectionsBaseChange_ungradedIncl_localMap (a : Γ(X, U.1))
    (ha : a ∈ Stacks.Conormal.chartIdeal i U ^ 1) :
    (conormalSectionsBaseChange f i i' g hcomm hUU').hom
        ((Stacks.Conormal.conormalAlgebra i).algebra.ungradedIncl (1 : ℕ)
          ((Stacks.Conormal.conormalAlgebra i).localMap U inferInstance 1 ⟨a, ha⟩)) =
      (Stacks.Conormal.conormalAlgebra i').algebra.ungradedIncl (1 : ℕ)
        ((Stacks.Conormal.conormalAlgebra i').localMap U' inferInstance 1
          ⟨affineBaseChangeMap f hUU' a, by
            have h := map_ideal_ker_le f hUU' i i' g hcomm
            rw [← chartIdeal_eq_ker_ideal, ← chartIdeal_eq_ker_ideal] at h
            rw [pow_one] at ha ⊢
            exact h (Ideal.mem_map_of_mem _ ha)⟩) := by
  have ha' : a ∈ i.ker.ideal U := by
    rw [← chartIdeal_eq_ker_ideal]
    simpa using ha
  have hz := Stacks.Conormal.conormalAlgebraSheafSectionsEquiv_of_mk i U inferInstance 1 a ha
  have hz' := Stacks.Conormal.conormalAlgebraSheafSectionsEquiv_of_mk i' U' inferInstance 1
    (affineBaseChangeMap f hUU' a) (by
      rw [pow_one] at ha ⊢
      exact affineBaseChangeMap_mem_chartIdeal i i' g f hcomm hUU' ha)
  let z : AssociatedGraded.gradedRing (i.ker.ideal U) :=
    DirectSum.of (fun k => AssociatedGraded.piece (M := Γ(X, U.1)) (i.ker.ideal U) k) 1
      (AssociatedGraded.mk (i.ker.ideal U) 1 ⟨a, by simpa using ha'⟩)
  have e1 := exceptionalChartSectionsEquiv_conormalEquiv i U z
  have e2 := exceptionalChartSectionsEquiv_conormalEquiv i' U'
    (AssociatedGraded.gradedRingMapOfRingHom (affineBaseChangeMap f hUU')
      (map_ideal_ker_le f hUU' i i' g hcomm) z)
  have e3 := conormalSectionsBaseChange_exceptionalChartSectionsIso i i' g f hcomm hUU' z
  refine (congrArg _ hz.symm).trans (Eq.trans ?_ hz')
  simp only [z, AssociatedGraded.gradedRingMapOfRingHom_of, AssociatedGraded.pieceMapOfRingHom_mk]
    at e1 e2 e3
  exact (congrArg _ e1.symm).trans (e3.trans e2)

/-- **The comparison of the conormal algebras on the conormal sheaf.** On the charts over `U` and
`U' ⊆ f⁻¹U`, the comparison of the conormal algebras carries the degree-one class of a section
`c` of `𝒞_{Z/X}` over `Z ∩ U` to the degree-one class of the image of `c` under the conormal
comparison map `g^*𝒞_{Z/X} ⟶ 𝒞_{Z'/X'}` of Stacks 0473, transposed along `g^* ⊣ g_*` and
restricted to `Z' ∩ U'`. -/
theorem conormalSectionsBaseChange_conormalDegreeOneHom
    (c : (Stacks.Conormal.conormalSheaf i).val.obj (op (i ⁻¹ᵁ U.1))) :
    (conormalSectionsBaseChange f i i' g hcomm hUU').hom
        ((conormalDegreeOneIncl i).val.app (op (i ⁻¹ᵁ U.1))
          ((Stacks.Conormal.conormalDegreeOneHom i).val.app (op (i ⁻¹ᵁ U.1)) c)) =
      (conormalDegreeOneIncl i').val.app (op (i' ⁻¹ᵁ U'.1))
        ((Stacks.Conormal.conormalDegreeOneHom i').val.app (op (i' ⁻¹ᵁ U'.1))
          ((Stacks.Conormal.conormalSheaf i').val.map
            (homOfLE (Stacks.Immersion.preimage_le_preimage_of_square hcomm U'.1 U.1 hUU')).op
            (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv _ _
              (Stacks.Immersion.immersionConormalSheafMap i' i g f
                (Stacks.Immersion.toShHom_square hcomm))).val.app (op (i ⁻¹ᵁ U.1)) c))) := by
  obtain ⟨eW, heW⟩ := exists_chartIdeal_affineModel i U
  obtain ⟨eZ, heZ⟩ := exists_chartIdeal_affineModel i' U'
  obtain ⟨a, ha⟩ := Ideal.toCotangent_surjective (Stacks.Conormal.chartIdeal i U)
    ((Stacks.Conormal.affineConormalIsoCotangent i U.1 U.2 _ eW heW).hom.hom c)
  obtain rfl : c = (Stacks.Conormal.affineConormalIsoCotangent i U.1 U.2 _ eW heW).inv.hom
      ((Stacks.Conormal.chartIdeal i U).toCotangent a) := by
    rw [ha]
    exact (congrArg (fun k => k.hom c)
      (Stacks.Conormal.affineConormalIsoCotangent i U.1 U.2 _ eW heW).hom_inv_id).symm
  have hb := affineBaseChangeMap_mem_chartIdeal i i' g f hcomm hUU' a.2
  have hInd := Stacks.Immersion.isInducedConormalSheafMap_immersionConormalSheafMap i' i g f hcomm
    U'.1 U'.2 U.1 U.2 hUU' (Stacks.Conormal.chartIdeal i' U') (Stacks.Conormal.chartIdeal i U)
    eZ heZ eW heW a ⟨_, hb⟩ rfl
  refine Eq.trans ?_ (congrArg (fun y => (conormalDegreeOneIncl i').val.app (op (i' ⁻¹ᵁ U'.1))
    ((Stacks.Conormal.conormalDegreeOneHom i').val.app (op (i' ⁻¹ᵁ U'.1)) y)) hInd).symm
  refine Eq.trans ?_ (congrArg (fun y => (conormalDegreeOneIncl i').val.app (op (i' ⁻¹ᵁ U'.1)) y)
    (Stacks.Conormal.conormalDegreeOneHom_localMap i' U' inferInstance eZ heZ ⟨_, hb⟩)).symm
  refine Eq.trans ?_ (conormalDegreeOneIncl_app i' _ _).symm
  refine (congrArg (fun y => (conormalSectionsBaseChange f i i' g hcomm hUU').hom
    ((conormalDegreeOneIncl i).val.app (op (i ⁻¹ᵁ U.1)) y))
    (Stacks.Conormal.conormalDegreeOneHom_localMap i U inferInstance eW heW a)).trans ?_
  refine (congrArg (fun y => (conormalSectionsBaseChange f i i' g hcomm hUU').hom y)
    (conormalDegreeOneIncl_app i _ _)).trans ?_
  exact conormalSectionsBaseChange_ungradedIncl_localMap i i' g f hcomm hUU' a.1 _

/-- `Stacks.Chow.conormalSectionsBaseChange_conormalDegreeOneHom`, with the restriction to
`Z' ∩ U'` taken in the conormal algebra. -/
theorem conormalSectionsBaseChange_conormalDegreeOneHom'
    (c : (Stacks.Conormal.conormalSheaf i).val.obj (op (i ⁻¹ᵁ U.1))) :
    (conormalSectionsBaseChange f i i' g hcomm hUU').hom
        ((conormalDegreeOneIncl i).val.app (op (i ⁻¹ᵁ U.1))
          ((Stacks.Conormal.conormalDegreeOneHom i).val.app (op (i ⁻¹ᵁ U.1)) c)) =
      ((Stacks.Conormal.conormalAlgebraSheaf i').right.obj.map
        (homOfLE (Stacks.Immersion.preimage_le_preimage_of_square hcomm U'.1 U.1 hUU')).op).hom
        ((conormalDegreeOneIncl i').val.app (op (g ⁻¹ᵁ (i ⁻¹ᵁ U.1)))
          ((Stacks.Conormal.conormalDegreeOneHom i').val.app (op (g ⁻¹ᵁ (i ⁻¹ᵁ U.1)))
            (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv _ _
              (Stacks.Immersion.immersionConormalSheafMap i' i g f
                (Stacks.Immersion.toShHom_square hcomm))).val.app (op (i ⁻¹ᵁ U.1)) c))) := by
  refine (conormalSectionsBaseChange_conormalDegreeOneHom i i' g f hcomm hUU' c).trans ?_
  have h1 := PresheafOfModules.naturality_apply (Stacks.Conormal.conormalDegreeOneHom i').val
    (homOfLE (Stacks.Immersion.preimage_le_preimage_of_square hcomm U'.1 U.1 hUU')).op
  have h2 := PresheafOfModules.naturality_apply (conormalDegreeOneIncl i').val
    (homOfLE (Stacks.Immersion.preimage_le_preimage_of_square hcomm U'.1 U.1 hUU')).op
  exact (congrArg (fun y => (conormalDegreeOneIncl i').val.app (op (i' ⁻¹ᵁ U'.1)) y)
    (h1 _)).trans (h2 _)

variable {S : Scheme.{u}} (sX : X ⟶ S) (hker : i'.ker = i.ker.comap f)

/-- On global sections, `Spec.map φ` corresponds to `φ` under `Scheme.ΓSpecIso`. -/
theorem Spec_map_appLE_top_ΓSpecIso_inv_apply {R R' : CommRingCat.{u}} (φ : R ⟶ R') (x : R) :
    ((Spec.map φ).appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso R).inv.hom x) =
      (Scheme.ΓSpecIso R').inv.hom (φ.hom x) := by
  change ((Spec.map φ).appLE ⊤ (Spec.map φ ⁻¹ᵁ ⊤) le_rfl).hom _ = _
  rw [Scheme.Hom.appLE_eq_app]
  exact (congrArg (fun ψ => CommRingCat.Hom.hom ψ x) (Scheme.ΓSpecIso_inv_naturality φ)).symm

/-- **The comparison of the normal cones on sections over the charts.** A section of the
conormal algebra over `Z ∩ U`, viewed on `C_ZX` over `U`, pulled back along the comparison
`C_{Z'}X' ⟶ C_ZX` and then to the chart of `C_{Z'}X'` over `U'`, is the image of the section
under the comparison of the conormal algebras. -/
theorem normalConeChart_appLE_normalConeBaseChangeMap_appLE
    (x : (Stacks.Conormal.conormalAlgebraSheaf i).right.obj.obj (op (i ⁻¹ᵁ U.1)))
    (O : (Stacks.Conormal.normalCone i').Opens) (h₁ : ⊤ ≤ normalConeChart i' U' ⁻¹ᵁ O)
    (h₂ : O ≤ normalConeBaseChangeMap f sX i i' hker ⁻¹ᵁ
      ((relativeSpecGluingData (Stacks.Conormal.conormalAlgebraSheaf i)).toBase ⁻¹ᵁ
        (subschemeAffineOpen i U).1)) :
    ((normalConeChart i' U').appLE O ⊤ h₁).hom
        ((normalConeBaseChangeMap f sX i i' hker).appLE _ O h₂ |>.hom
          ((pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i)).inv.right.hom.app
            (op (i ⁻¹ᵁ U.1)) x)) =
      (Scheme.ΓSpecIso _).inv.hom ((conormalSectionsBaseChange f i i' g hcomm hUU').hom x) := by
  have hcomp : ∀ y, ((normalConeChart i' U').appLE O ⊤ h₁).hom
      (((normalConeBaseChangeMap f sX i i' hker).appLE _ O h₂).hom y) =
      ((normalConeChart i' U' ≫ normalConeBaseChangeMap f sX i i' hker).appLE _ ⊤
        (by rw [Scheme.Hom.comp_preimage]
            exact h₁.trans ((normalConeChart i' U').preimage_mono h₂))).hom y := fun y => by
    rw [← Scheme.Hom.appLE_comp_appLE]
    rfl
  refine (hcomp _).trans ?_
  have key : ∀ (m : normalConeChartSource i' U' ⟶ Stacks.Conormal.normalCone i)
      (hm : m = Spec.map (conormalSectionsBaseChange f i i' g hcomm hUU') ≫ normalConeChart i U)
      (e : ⊤ ≤ m ⁻¹ᵁ ((relativeSpecGluingData (Stacks.Conormal.conormalAlgebraSheaf i)).toBase ⁻¹ᵁ
        (subschemeAffineOpen i U).1)),
      (m.appLE _ ⊤ e).hom ((pushforwardAlgebraIso
          (Stacks.Conormal.conormalAlgebraSheaf i)).inv.right.hom.app (op (i ⁻¹ᵁ U.1)) x) =
        (Scheme.ΓSpecIso _).inv.hom ((conormalSectionsBaseChange f i i' g hcomm hUU').hom x) := by
    rintro m rfl e
    have h1 : (Spec.map (conormalSectionsBaseChange f i i' g hcomm hUU') ≫
        normalConeChart i U).appLE _ ⊤ e =
        (normalConeChart i U).appLE _ ⊤
          (by exact (le_ι_preimage (relativeSpecGluingData (Stacks.Conormal.conormalAlgebraSheaf i))
            (subschemeAffineOpen i U))) ≫
          (Spec.map (conormalSectionsBaseChange f i i' g hcomm hUU')).appLE ⊤ ⊤ le_top :=
      (Scheme.Hom.appLE_comp_appLE (Spec.map (conormalSectionsBaseChange f i i' g hcomm hUU'))
        (normalConeChart i U) _ ⊤ ⊤ (by exact (le_ι_preimage
          (relativeSpecGluingData (Stacks.Conormal.conormalAlgebraSheaf i))
            (subschemeAffineOpen i U))) le_top).symm
    rw [h1]
    have h2 := ι_appLE_pushforwardAlgebraIso_inv (Stacks.Conormal.conormalAlgebraSheaf i)
      (subschemeAffineOpen i U) x
    exact (congrArg _ h2).trans (Spec_map_appLE_top_ΓSpecIso_inv_apply _ x)
  exact key _
    (specMap_conormalSectionsBaseChange_normalConeChart f sX i i' g hcomm hker hUU').symm _

end Charts

section Reduction

variable {S Z X Z' X' : Scheme.{u}} (sX : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]
  (i' : Z' ⟶ X') [IsClosedImmersion i'] (g : Z' ⟶ Z) (f : X' ⟶ X) (sq : IsPullback i' g f i)
  (𝒩 : VirtualNormalBundle i)

/-- The comparison of the normal cones as a morphism of schemes over `Z`. -/
abbrev normalConeBaseChangeOver :
    (Over.mk (Stacks.Conormal.normalConeToBase i' ≫ g) : Over Z) ⟶
      Over.mk (Stacks.Conormal.normalConeToBase i) :=
  Over.homMk (normalConeBaseChangeMap f sX i i' (ker_eq_comap_of_isPullback f sq))
    (normalConeBaseChangeMap_toBase f sX i i' _ g sq.w)

/-- **The compatibility of `ι` with base change, from the equality of classifying maps**: two
morphisms over `Z` into `V(𝒩)` with the same classifying map agree. -/
theorem normalConeBaseChangeMap_comp_normalConeEmbedding_of_classifying
    (hcl : vectorBundleClassifyingMap (dualSheaf 𝒩.bundle)
        (normalConeBaseChangeOver sX i i' g f sq ≫
          (normalConeToNormalBundleOver i ≫ vectorBundleMap Z 𝒩.conormalDegreeOneSurjection)) =
      vectorBundleClassifyingMap (dualSheaf 𝒩.bundle)
        ((Over.map g).map (normalConeToNormalBundleOver i' ≫
            vectorBundleMap Z' (𝒩.baseChange i i' g f sq).conormalDegreeOneSurjection) ≫
          𝒩.baseChangeTotalSpaceOver i i' g f sq)) :
    normalConeBaseChangeMap f sX i i' (ker_eq_comap_of_isPullback f sq) ≫
        𝒩.normalConeEmbedding =
      (𝒩.baseChange i i' g f sq).normalConeEmbedding ≫ 𝒩.baseChangeTotalSpaceMap i i' g f sq := by
  refine (congrArg Over.Hom.left (vectorBundle_hom_ext _ hcl)).trans ?_
  rw [Over.comp_left, VirtualNormalBundle.baseChangeTotalSpaceOver_left]
  rfl

/-- **The equality of classifying maps behind the compatibility of `ι` with base change**, from
the corresponding equality of module maps out of `𝒩^∨`. -/
theorem vectorBundleClassifyingMap_normalConeBaseChangeOver_eq_of
    (hkey : (𝒩.conormalDegreeOneSurjection ≫ conormalDegreeOneIncl i ≫
        underlyingModuleMap (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i)).inv) ≫
        underlyingModuleMap (pushforwardAlgebraMap (normalConeBaseChangeOver sX i i' g f sq)) =
      (pullbackPushforwardAdjunction g).unit.app _ ≫
        (pushforward g).map (pullbackDualMap g 𝒩.bundle ≫
          (𝒩.baseChange i i' g f sq).conormalDegreeOneSurjection ≫ conormalDegreeOneIncl i' ≫
            underlyingModuleMap
              (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i')).inv)) :
    vectorBundleClassifyingMap (dualSheaf 𝒩.bundle)
        (normalConeBaseChangeOver sX i i' g f sq ≫
          (normalConeToNormalBundleOver i ≫ vectorBundleMap Z 𝒩.conormalDegreeOneSurjection)) =
      vectorBundleClassifyingMap (dualSheaf 𝒩.bundle)
        ((Over.map g).map (normalConeToNormalBundleOver i' ≫
            vectorBundleMap Z' (𝒩.baseChange i i' g f sq).conormalDegreeOneSurjection) ≫
          𝒩.baseChangeTotalSpaceOver i i' g f sq) := by
  refine (vectorBundleClassifyingMap_comp _ _ _).trans ?_
  refine (congrArg (· ≫ _) (vectorBundleClassifyingMap_normalConeEmbedding 𝒩)).trans ?_
  refine hkey.trans ?_
  have h2 := 𝒩.vectorBundleClassifyingMap_map_comp_baseChangeTotalSpaceOver i i' g f sq
    (normalConeToNormalBundleOver i' ≫
      vectorBundleMap Z' (𝒩.baseChange i i' g f sq).conormalDegreeOneSurjection)
  have h3 := vectorBundleClassifyingMap_normalConeEmbedding (𝒩.baseChange i i' g f sq)
  rw [h3] at h2
  exact h2.symm

/-- The chart computation behind
`Stacks.Chow.conormalDegreeOneIncl_comp_pushforwardAlgebraMap_normalConeBaseChangeOver`: the two
sides agree on the chart of `C_{Z'}X'` over an affine open `U' ⊆ f⁻¹U`. -/
theorem normalConeChart_appLE_pushforwardAlgebraMap_normalConeBaseChangeOver
    (U : X.affineOpens) (U' : X'.affineOpens) (hU' : U'.1 ≤ f ⁻¹ᵁ U.1)
    (c : (Stacks.Conormal.conormalSheaf i).val.obj (op (i ⁻¹ᵁ U.1)))
    (h₁ : ⊤ ≤ normalConeChart i' U' ⁻¹ᵁ
      ((Stacks.Conormal.normalConeToBase i' ≫ g) ⁻¹ᵁ (i ⁻¹ᵁ U.1))) :
    ((normalConeChart i' U').appLE _ ⊤ h₁).hom
        (((pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i)).inv.right.hom.app
            (op (i ⁻¹ᵁ U.1)) ≫
          (pushforwardAlgebraMap (normalConeBaseChangeOver sX i i' g f sq)).right.hom.app
            (op (i ⁻¹ᵁ U.1))).hom
          ((conormalDegreeOneIncl i).val.app (op (i ⁻¹ᵁ U.1))
            ((Stacks.Conormal.conormalDegreeOneHom i).val.app (op (i ⁻¹ᵁ U.1)) c))) =
      ((normalConeChart i' U').appLE _ ⊤ h₁).hom
        ((pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i')).inv.right.hom.app
          (op (g ⁻¹ᵁ (i ⁻¹ᵁ U.1)))
          ((conormalDegreeOneIncl i').val.app (op (g ⁻¹ᵁ (i ⁻¹ᵁ U.1)))
            ((Stacks.Conormal.conormalDegreeOneHom i').val.app (op (g ⁻¹ᵁ (i ⁻¹ᵁ U.1)))
              (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv _ _
                (Stacks.Immersion.immersionConormalSheafMap i' i g f
                  (Stacks.Immersion.toShHom_square sq.w))).val.app (op (i ⁻¹ᵁ U.1)) c)))) := by
  have hTle : (subschemeAffineOpen i' U').1 ≤ g ⁻¹ᵁ (i ⁻¹ᵁ U.1) :=
    Stacks.Immersion.preimage_le_preimage_of_square sq.w U'.1 U.1 hU'
  have hA := pushforwardAlgebraMap_app (normalConeBaseChangeOver sX i i' g f sq) (i ⁻¹ᵁ U.1)
    (preimage_le_preimage_preimage _ _)
  have hL := normalConeChart_appLE_normalConeBaseChangeMap_appLE i i' g f sq.w hU' sX
    (ker_eq_comap_of_isPullback f sq)
    ((conormalDegreeOneIncl i).val.app (op (i ⁻¹ᵁ U.1))
      ((Stacks.Conormal.conormalDegreeOneHom i).val.app (op (i ⁻¹ᵁ U.1)) c))
    ((Stacks.Conormal.normalConeToBase i' ≫ g) ⁻¹ᵁ (i ⁻¹ᵁ U.1)) h₁
    (preimage_le_preimage_preimage (normalConeBaseChangeOver sX i i' g f sq) _)
  have hR := normalConeChart_appLE_pushforwardAlgebraIso_inv i' U' (g ⁻¹ᵁ (i ⁻¹ᵁ U.1)) hTle
    ((conormalDegreeOneIncl i').val.app (op (g ⁻¹ᵁ (i ⁻¹ᵁ U.1)))
      ((Stacks.Conormal.conormalDegreeOneHom i').val.app (op (g ⁻¹ᵁ (i ⁻¹ᵁ U.1)))
        (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv _ _
          (Stacks.Immersion.immersionConormalSheafMap i' i g f
            (Stacks.Immersion.toShHom_square sq.w))).val.app (op (i ⁻¹ᵁ U.1)) c))) h₁
  have hC := conormalSectionsBaseChange_conormalDegreeOneHom' i i' g f sq.w hU' c
  refine Eq.trans ?_ ((hL.trans (congrArg (Scheme.ΓSpecIso _).inv.hom hC)).trans hR.symm)
  exact congrArg ((normalConeChart i' U').appLE _ ⊤ h₁).hom
    (congrArg (fun φ => CommRingCat.Hom.hom φ _) hA)

/-- `Stacks.Chow.normalConeChart_appLE_pushforwardAlgebraMap_normalConeBaseChangeOver`, with the
two sides written as morphisms of modules. -/
theorem normalConeChart_appLE_pushforwardAlgebraMap_normalConeBaseChangeOver'
    (U : X.affineOpens) (U' : X'.affineOpens) (hU' : U'.1 ≤ f ⁻¹ᵁ U.1)
    (c : (Stacks.Conormal.conormalSheaf i).val.obj (op (i ⁻¹ᵁ U.1)))
    (h₁ : ⊤ ≤ normalConeChart i' U' ⁻¹ᵁ
      ((Stacks.Conormal.normalConeToBase i' ≫ g) ⁻¹ᵁ (i ⁻¹ᵁ U.1))) :
    ((normalConeChart i' U').appLE _ ⊤ h₁).hom
        (((Stacks.Conormal.conormalDegreeOneHom i ≫ conormalDegreeOneIncl i ≫
          underlyingModuleMap (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i)).inv ≫
          underlyingModuleMap
            (pushforwardAlgebraMap (normalConeBaseChangeOver sX i i' g f sq))).val.app
            (op (i ⁻¹ᵁ U.1))).hom c) =
      ((normalConeChart i' U').appLE _ ⊤ h₁).hom
        ((((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv _ _
          (Stacks.Immersion.immersionConormalSheafMap i' i g f
            (Stacks.Immersion.toShHom_square sq.w)) ≫
        (pushforward g).map (Stacks.Conormal.conormalDegreeOneHom i' ≫ conormalDegreeOneIncl i' ≫
            underlyingModuleMap
              (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i')).inv)).val.app
              (op (i ⁻¹ᵁ U.1))).hom c) :=
  normalConeChart_appLE_pushforwardAlgebraMap_normalConeBaseChangeOver sX i i' g f sq U U' hU' c h₁

/-- `Stacks.Chow.conormalDegreeOneIncl_comp_pushforwardAlgebraMap_normalConeBaseChangeOver` on the
sections over `Z ∩ U`, `U ⊆ X` an affine open. -/
theorem conormalDegreeOneIncl_comp_pushforwardAlgebraMap_normalConeBaseChangeOver_app
    (U : X.affineOpens) (c : (Stacks.Conormal.conormalSheaf i).val.obj (op (i ⁻¹ᵁ U.1))) :
    ((Stacks.Conormal.conormalDegreeOneHom i ≫ conormalDegreeOneIncl i ≫
          underlyingModuleMap (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i)).inv ≫
          underlyingModuleMap
            (pushforwardAlgebraMap (normalConeBaseChangeOver sX i i' g f sq))).val.app
            (op (i ⁻¹ᵁ U.1))).hom c =
      (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv _ _
          (Stacks.Immersion.immersionConormalSheafMap i' i g f
            (Stacks.Immersion.toShHom_square sq.w)) ≫
        (pushforward g).map (Stacks.Conormal.conormalDegreeOneHom i' ≫ conormalDegreeOneIncl i' ≫
            underlyingModuleMap
              (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i')).inv)).val.app
              (op (i ⁻¹ᵁ U.1))).hom c := by
  have hOle : ∀ U' : X'.affineOpens, U'.1 ≤ f ⁻¹ᵁ U.1 →
      normalConeToX i' ⁻¹ᵁ U'.1 ≤ (Stacks.Conormal.normalConeToBase i' ≫ g) ⁻¹ᵁ (i ⁻¹ᵁ U.1) := by
    intro U' hU' x hx
    change (Stacks.Conormal.normalConeToBase i' ≫ g ≫ i) x ∈ U.1
    rw [← sq.w]
    exact hU' hx
  refine normalCone_sections_ext i' (f ⁻¹ᵁ U.1) hOle ?_ ?_
  · intro x hx
    change (Stacks.Conormal.normalConeToBase i' ≫ i' ≫ f) x ∈ U.1
    rw [sq.w]
    exact hx
  · intro U' hU'
    exact normalConeChart_appLE_pushforwardAlgebraMap_normalConeBaseChangeOver' sX i i' g f sq
      U U' hU' c _

/-- **The comparison of the normal cones on degree-one classes of the conormal algebra.** On
the pushed-forward structure sheaves, the comparison `C_{Z'}X' ⟶ C_ZX` carries the degree-one
class of a local section of `𝒞_{Z/X}` to the degree-one class of its image under the conormal
comparison map of Stacks 0473, transposed along `g^* ⊣ g_*`. -/
theorem conormalDegreeOneIncl_comp_pushforwardAlgebraMap_normalConeBaseChangeOver :
    Stacks.Conormal.conormalDegreeOneHom i ≫ conormalDegreeOneIncl i ≫
        underlyingModuleMap (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i)).inv ≫
        underlyingModuleMap (pushforwardAlgebraMap (normalConeBaseChangeOver sX i i' g f sq)) =
      (modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv _ _
          (Stacks.Immersion.immersionConormalSheafMap i' i g f
            (Stacks.Immersion.toShHom_square sq.w)) ≫
        (pushforward g).map (Stacks.Conormal.conormalDegreeOneHom i' ≫ conormalDegreeOneIncl i' ≫
            underlyingModuleMap
              (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i')).inv) := by
  have hB : TopologicalSpace.Opens.IsBasis (Set.range fun U : X.affineOpens => i ⁻¹ᵁ U.1) := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro O z hz
    obtain ⟨_, ⟨V, rfl⟩, hzV, hVO⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Stacks.Conormal.conormalChart_isBasis i) hz
    exact ⟨_, ⟨V.1, rfl⟩, hzV, hVO⟩
  refine sheafOfModules_hom_ext_of_isBasis _ _ hB fun U c => ?_
  have h :=
    conormalDegreeOneIncl_comp_pushforwardAlgebraMap_normalConeBaseChangeOver_app sX i i' g f sq U c
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · rfl

/-- The right-hand side of
`Stacks.Chow.conormalDegreeOneSurjection_comp_pushforwardAlgebraMap_normalConeBaseChangeOver`,
through `σ'`, the conormal comparison map and the unit of `g^* ⊣ g_*`. -/
theorem pullbackPushforwardAdjunction_unit_comp_baseChange_conormalDegreeOneSurjection :
    (pullbackPushforwardAdjunction g).unit.app _ ≫
        (pushforward g).map (pullbackDualMap g 𝒩.bundle ≫
          (𝒩.baseChange i i' g f sq).conormalDegreeOneSurjection ≫ conormalDegreeOneIncl i' ≫
            underlyingModuleMap (pushforwardAlgebraIso
              (Stacks.Conormal.conormalAlgebraSheaf i')).inv) =
      𝒩.surjection ≫ ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv _ _
          (Stacks.Immersion.immersionConormalSheafMap i' i g f
            (Stacks.Immersion.toShHom_square sq.w)) ≫
        (modulePushforward g.toLRSHom.toShHom).map (Stacks.Conormal.conormalDegreeOneHom i' ≫
          conormalDegreeOneIncl i' ≫
            underlyingModuleMap
              (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i')).inv)) := by
  have hσ : pullbackDualMap g 𝒩.bundle ≫ (𝒩.baseChange i i' g f sq).surjection =
      (modulePullback g.toLRSHom.toShHom).map 𝒩.surjection ≫
        Stacks.Immersion.immersionConormalSheafMap i' i g f
          (Stacks.Immersion.toShHom_square sq.w) := by
    rw [VirtualNormalBundle.baseChange_surjection]
    exact Iso.hom_inv_id_assoc (@asIso _ _ _ _ (pullbackDualMap g 𝒩.bundle)
      (pullbackDualMap_isIso g 𝒩.bundle 𝒩.isFiniteLocallyFree)) _
  have e2 : pullbackDualMap g 𝒩.bundle ≫ (𝒩.baseChange i i' g f sq).conormalDegreeOneSurjection =
      (modulePullback g.toLRSHom.toShHom).map 𝒩.surjection ≫
        Stacks.Immersion.immersionConormalSheafMap i' i g f
          (Stacks.Immersion.toShHom_square sq.w) ≫ Stacks.Conormal.conormalDegreeOneHom i' :=
    (congrArg (pullbackDualMap g 𝒩.bundle ≫ ·) (congrArg ((𝒩.baseChange i i' g f sq).surjection ≫ ·)
      (Stacks.Conormal.conormalDegreeOneIso_hom i'))).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Stacks.Conormal.conormalDegreeOneHom i') hσ).trans (Category.assoc _ _ _)))
  have e3 : pullbackDualMap g 𝒩.bundle ≫ (𝒩.baseChange i i' g f sq).conormalDegreeOneSurjection ≫
      conormalDegreeOneIncl i' ≫
        underlyingModuleMap (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i')).inv =
      (modulePullback g.toLRSHom.toShHom).map 𝒩.surjection ≫
        Stacks.Immersion.immersionConormalSheafMap i' i g f
          (Stacks.Immersion.toShHom_square sq.w) ≫ (Stacks.Conormal.conormalDegreeOneHom i' ≫
            conormalDegreeOneIncl i' ≫
              underlyingModuleMap
                (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i')).inv) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (conormalDegreeOneIncl i' ≫
      underlyingModuleMap
        (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i')).inv)) e2).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))))
  exact (pullbackPushforwardAdjunction_unit_comp_pushforward_map g _ _ _).trans
    ((congrArg ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv _ _) e3).trans
    (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv_naturality_left _ _).trans
    (congrArg (𝒩.surjection ≫ ·)
      ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).homEquiv_naturality_right _ _))))

/-- `Stacks.Chow.conormalDegreeOneSurjection_comp_pushforwardAlgebraMap_normalConeBaseChangeOver`
on local sections. -/
theorem conormalDegreeOneSurjection_comp_pushforwardAlgebraMap_normalConeBaseChangeOver_app
    (W : Z.Opensᵒᵖ) (s : (dualSheaf 𝒩.bundle).val.obj W) :
    ((((𝒩.conormalDegreeOneSurjection ≫ conormalDegreeOneIncl i ≫
        underlyingModuleMap (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i)).inv) ≫
        underlyingModuleMap
          (pushforwardAlgebraMap (normalConeBaseChangeOver sX i i' g f sq)))).val.app
          W).hom s =
      (((pullbackPushforwardAdjunction g).unit.app _ ≫
        (pushforward g).map (pullbackDualMap g 𝒩.bundle ≫
          (𝒩.baseChange i i' g f sq).conormalDegreeOneSurjection ≫ conormalDegreeOneIncl i' ≫
            underlyingModuleMap (pushforwardAlgebraIso
              (Stacks.Conormal.conormalAlgebraSheaf i')).inv)).val.app W).hom s := by
  have hkey := congrArg (fun φ => (φ.val.app W).hom ((𝒩.surjection.val.app W).hom s))
    (conormalDegreeOneIncl_comp_pushforwardAlgebraMap_normalConeBaseChangeOver sX i i' g f sq)
  have h1 := congrArg (fun φ => (φ.val.app W).hom ((𝒩.surjection.val.app W).hom s))
    (Stacks.Conormal.conormalDegreeOneIso_hom i)
  have h2 := congrArg (fun y => ((underlyingModuleMap (pushforwardAlgebraMap
      (normalConeBaseChangeOver sX i i' g f sq))).val.app W).hom (((underlyingModuleMap
      (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i)).inv).val.app W).hom
      (((conormalDegreeOneIncl i).val.app W).hom y))) h1
  refine Eq.trans ?_ ((h2.trans (Eq.trans ?_ hkey)).trans ?_)
  · rfl
  · rfl
  refine Eq.trans ?_ ((modules_comp_val_app_hom _ _ W s).symm.trans
    ((congrArg (fun φ => (φ.val.app W).hom s)
      (pullbackPushforwardAdjunction_unit_comp_baseChange_conormalDegreeOneSurjection
        i i' g f sq 𝒩)).symm.trans ?_))
  · rfl
  · rfl

/-- **The compatibility of the classifying maps**: `σ` followed by the comparison of the normal
cones on pushed-forward structure sheaves is the unit of `g^* ⊣ g_*` followed by the direct image
of `σ'` for `g^*𝒩`. -/
theorem conormalDegreeOneSurjection_comp_pushforwardAlgebraMap_normalConeBaseChangeOver :
    (𝒩.conormalDegreeOneSurjection ≫ conormalDegreeOneIncl i ≫
        underlyingModuleMap (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i)).inv) ≫
        underlyingModuleMap (pushforwardAlgebraMap (normalConeBaseChangeOver sX i i' g f sq)) =
      (pullbackPushforwardAdjunction g).unit.app _ ≫
        (pushforward g).map (pullbackDualMap g 𝒩.bundle ≫
          (𝒩.baseChange i i' g f sq).conormalDegreeOneSurjection ≫ conormalDegreeOneIncl i' ≫
            underlyingModuleMap
              (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i')).inv) := by
  apply SheafOfModules.hom_ext
  refine PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
  exact conormalDegreeOneSurjection_comp_pushforwardAlgebraMap_normalConeBaseChangeOver_app
    sX i i' g f sq 𝒩 W s

/-- **The compatibility of `ι` with base change.** For a cartesian square of closed immersions
`Z' = Z ×_X X'`, the comparison `C_{Z'}X' ⟶ C_ZX` of the normal cones followed by
`ι : C_ZX ⟶ V(𝒩)` is `ι' : C_{Z'}X' ⟶ V(g^*𝒩)` followed by `V(g^*𝒩) ⟶ V(𝒩)`. -/
theorem normalConeBaseChangeMap_comp_normalConeEmbedding :
    normalConeBaseChangeMap f sX i i' (ker_eq_comap_of_isPullback f sq) ≫
        𝒩.normalConeEmbedding =
      (𝒩.baseChange i i' g f sq).normalConeEmbedding ≫ 𝒩.baseChangeTotalSpaceMap i i' g f sq :=
  normalConeBaseChangeMap_comp_normalConeEmbedding_of_classifying sX i i' g f sq 𝒩
    (vectorBundleClassifyingMap_normalConeBaseChangeOver_eq_of sX i i' g f sq 𝒩
      (conormalDegreeOneSurjection_comp_pushforwardAlgebraMap_normalConeBaseChangeOver
        sX i i' g f sq 𝒩))

end Reduction

end Stacks.Chow

end
