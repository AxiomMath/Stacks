module

public import StacksFrontier.Topology.Simplicial.QcSmallTotalSiteComparison
public import StacksFrontier.Topology.Simplicial.SimplicialSpace
public import StacksFrontier.Topology.Simplicial.AugmentationFibrePartTwo

/-!
# Proper hypercoverings in topology: the comparison square

Let `U` be a simplicial object of `LC` and let `a : U → X` be an augmentation, `U` and `X` lying
in a chosen quasi-compact site `LC_qc` of **Tag 09X2**. **Tag 0DAF** asserts that there is a
commutative diagram of topoi
```
Sh((LC_qc/U)_total) --h--> Sh(U_Zar)
        | a_qc                 | a
Sh(LC_qc/X)       --h₋₁--> Sh(X)
```
whose left vertical arrow is the augmentation of **Section 09X8** and whose right vertical arrow
is the augmentation of **Tag 09W4**. The horizontal arrows are the comparison morphisms of
Cohomology on Sites, Section 21.31 (**Tag 09WY**): `h₋₁` is the comparison morphism
`a_X : Sh(LC_qc/X) → Sh(X)` and `h` is the morphism of topoi of the functor
`U_Zar → (LC_qc/U)_total`, `V ↦ V/U_n`.

This file constructs `h₋₁` and proves that the square commutes, as an isomorphism of the direct
images of the two composites and, by uniqueness of adjoints, of their inverse images.

## The proof

The direct image of `h₋₁ ∘ a_qc` sends a sheaf `F` on the total site to the sheaf
`W ↦ (a_{qc,*}F)(W/X)`. The direct image `a_{qc,*}F` is the right Kan extension of `F` along the
functor `V/U_n ↦ V/X`, so its sections over `W/X` are the compatible families of sections of `F`
over the objects `V/U_n` of the total site *lying over* `W`, those whose image `V/X` maps to
`W/X` (`Stacks.Topology.Simplicial.qcSmallRanEquiv`). The direct image of `a ∘ h` sends `F` to
the sheaf whose sections over `W` are the morphisms `a⁻¹(h_W) ⟶ h_*F`; the sheaf `a⁻¹(h_W)` has a
section over `(n, V)` exactly when `V ⊆ a_n⁻¹(W)`, and then only one, so these are the
compatible families of sections of `F` over the objects `V/U_n` cut out by the opens
`V ⊆ a_n⁻¹(W)` (`Stacks.Topology.Simplicial.qcZariskiSectionsEquiv`). The two kinds of family
agree (`Stacks.Topology.Simplicial.qcSmallFamilyEquiv`): an object lying over `W` maps, in its own
simplicial degree and uniquely, to the object cut out by `a_n⁻¹(W)`, so a family over the
objects cut out by opens extends uniquely to all objects lying over `W`. This is the computation
the source performs through Lemma 0D99, done directly on sections. Throughout, morphisms *into*
an object `W/X` or `V/U_n` cut out by an open are unique when they exist, because the inclusion
of an open subspace is a monomorphism; that is what makes every compatibility in the argument
automatic.

## Main definitions

* `MorphismOfTopoi.ofEquivalence`: the morphism of topoi given by an equivalence of categories.
* `Stacks.Topology.Simplicial.qcSmallOpensFunctor`: the functor `X_Zar → LC_qc/X`, `W ↦ W/X`,
  into the small model.
* `Stacks.Topology.Simplicial.qcSmallBottomMorphism`: the bottom horizontal arrow `h₋₁`.
* `Stacks.Topology.Simplicial.qcZariskiAugmentation`: the right vertical arrow `a`, the
  augmentation of `U_Zar` towards `X` of Tag 09W4.
* `Stacks.Topology.Simplicial.qcSmallTotalFamily` and
  `Stacks.Topology.Simplicial.qcSmallZariskiFamily`: the two kinds of compatible family of
  sections through which the two direct images are compared.

## Main results

* `Stacks.Topology.Simplicial.qcSmallRanEquiv`,
  `Stacks.Topology.Simplicial.qcZariskiSectionsEquiv` and
  `Stacks.Topology.Simplicial.qcSmallFamilyEquiv`: the sections of the two composite direct
  images, as compatible families, and the comparison of the families.
* `Stacks.Topology.Simplicial.qcComparisonSquarePushforwardIso`: **Tag 0DAF**, the commutative
  square, on direct images.
* `Stacks.Topology.Simplicial.qcComparisonSquareInverseImageIso`: the same square on inverse
  images, `a_qc⁻¹ ∘ h₋₁⁻¹ ≅ h⁻¹ ∘ a⁻¹`.
* `Stacks.Topology.Simplicial.exists_qcComparisonSquare`: **Tag 0DAF** for an arbitrary
  simplicial object `U` of `LC` and augmentation `U → X`: a site `LC_qc` containing `X` and
  every `U_n` exists (Tag 09X2), and for it the square commutes.

## Implementation notes

The total site `(LC_qc/U)_total` and the augmentation `a_qc` are those of Section 09X8 as this
development forms them, over the small model of `LC_qc`
(`Stacks.Topology.Simplicial.ProperHypercovering.qcTotalSituation` and
`Stacks.Topology.Simplicial.ProperHypercovering.qcAugmentationMorphism`). Accordingly
`Sh(LC_qc/X)` is read through the identification
`Stacks.Topology.LocallyQuasiCompactQcSite.smallOverSheafEquiv` with sheaves on the localization
of the small model, and `h₋₁` is the comparison morphism `a_X` of Tag 09WY
(`Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcTopologicalMorphism`) composed with that
identification. Its inverse image is therefore
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcSmallTopologicalInverseImage` on the nose.

As in Tags 0D98 and 0D99, the equality of morphisms of topoi of the source is expressed by
natural isomorphisms of direct-image and of inverse-image functors, since composites of the
chosen adjoints are not definitionally equal.

## References

* [Stacks Project, Tag 0DAF](https://stacks.math.columbia.edu/tag/0DAF)
* [Stacks Project, Section 09X8](https://stacks.math.columbia.edu/tag/09X8)
* [Stacks Project, Tag 09W4](https://stacks.math.columbia.edu/tag/09W4)
* [Stacks Project, Section 09WY](https://stacks.math.columbia.edu/tag/09WY)
* [Stacks Project, Tag 0D99](https://stacks.math.columbia.edu/tag/0D99)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u w t₁ t₂ v₁ v₂ u₁ u₂

/-- The morphism of topoi given by an equivalence of categories, in the direction of its
inverse: the inverse image is the forward functor and the direct image the inverse. -/
def MorphismOfTopoi.ofEquivalence {E : Type u₁} [Category.{v₁} E] {F : Type u₂} [Category.{v₂} F]
    (e : F ≌ E) : MorphismOfTopoi E F where
  pushforward := e.inverse
  inverseImage := e.functor
  adj := e.toAdjunction
  preservesFiniteLimits := inferInstance

namespace Stacks.Topology.LocallyQuasiCompactQcSite

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactQcSite.{u, w} S₀ Bound)

/-- The comparison of the localization `LC_qc/Y` with the localization of the small model at the
image of `Y` is continuous. -/
instance overPost_smallEquivalence_isContinuous (Y : S.category) :
    (Over.post (X := Y) S.smallEquivalence.functor).IsContinuous (S.grothendieckTopology.over Y)
      (S.smallOverTopology Y) := by
  rw [smallOverTopology_eq]
  have : (Over.postEquiv (X := Y) S.smallEquivalence).symm.functor.IsCocontinuous
      (S.smallTopology.over (S.smallEquivalence.functor.obj Y)) (S.grothendieckTopology.over Y) :=
    inferInstanceAs ((Over.postEquiv (X := Y) S.smallEquivalence).inverse.IsCocontinuous _ _)
  exact (Over.postEquiv (X := Y) S.smallEquivalence).symm.toAdjunction
    |>.isContinuous_of_isCocontinuous (S.smallTopology.over
      (S.smallEquivalence.functor.obj Y)) (S.grothendieckTopology.over Y)

/-- The inverse functor of the identification `smallOverSheafEquiv` of `Sh(LC_qc/Y)` with the
sheaves on the localization of the small model is restriction along the comparison
`LC_qc/Y ⥤ (small model)/F(Y)`. -/
def smallOverSheafEquivInverseIso (Y : S.category) (A : Type t₁) [Category.{t₂} A] :
    (S.smallOverSheafEquiv Y A).inverse ≅
      (Over.post (X := Y) S.smallEquivalence.functor).sheafPushforwardContinuous A
        (S.grothendieckTopology.over Y) (S.smallOverTopology Y) := by
  have key : ∀ (K : GrothendieckTopology (Over (S.smallEquivalence.functor.obj Y)))
      (hK : K = S.smallTopology.over (S.smallEquivalence.functor.obj Y))
      [(Over.post (X := Y) S.smallEquivalence.functor).IsContinuous
        (S.grothendieckTopology.over Y) K]
      (h : (Sheaf (S.grothendieckTopology.over Y) A ≌ Sheaf K A) =
        (Sheaf (S.grothendieckTopology.over Y) A ≌
          Sheaf (S.smallTopology.over (S.smallEquivalence.functor.obj Y)) A)),
      (h.mpr (Over.postEquivSheafCongr S.smallEquivalence Y A)).inverse ≅
        (Over.post (X := Y) S.smallEquivalence.functor).sheafPushforwardContinuous A
          (S.grothendieckTopology.over Y) K := by
    intro K hK _ h
    subst hK
    exact Iso.refl _
  exact key _ (S.smallOverTopology_eq Y) _

end Stacks.Topology.LocallyQuasiCompactQcSite

namespace Stacks.Topology.Simplicial

open Stacks.Topology Stacks.Topology.Simplicial.ProperHypercovering
open Stacks.CategoryTheory.Hypercovering CategoryTheory.SimplicialSemiRepresentable
open Stacks.Topology.LocallyQuasiCompactZariskiSituation

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)

/-! ### The bottom horizontal arrow -/

/-- The functor `X_Zar ⥤ LC_qc/X`, `W ↦ W/X`, of Section 09WY, read in the small model of
`LC_qc`. -/
abbrev qcSmallOpensFunctor : Opens X.obj ⥤ Over (S.qcSite.smallEquivalence.functor.obj X) :=
  (S.opensToSlice X).1 ⋙ Over.post S.qcSite.smallEquivalence.functor

/-- The open-subset functor `X_Zar ⥤ LC_qc/X` is cover-preserving for the quasi-compact
localized topology. -/
theorem opensToSlice_coverPreserving_qcTopology :
    CoverPreserving (Opens.grothendieckTopology X.obj.obj)
      (S.qcSite.grothendieckTopology.over X) (S.opensToSlice X).1 := by
  let hc : (S.opensToSlice X).1.IsContinuous (Opens.grothendieckTopology X.obj.obj)
      (S.zariskiTopology.over X) := S.opensToSlice_isContinuous X
  refine ⟨fun {_ _} hS => ?_⟩
  exact S.zariskiTopology_over_le_qc X _
    ((CoverPreserving.of_isContinuous (F := (S.opensToSlice X).1)
      (Opens.grothendieckTopology X.obj.obj) (S.zariskiTopology.over X)).cover_preserve hS)

/-- The open-subset functor `X_Zar ⥤ LC_qc/X` is continuous for the quasi-compact localized
topology: it is cover-preserving and representably flat. -/
instance opensToSlice_isContinuous_qcTopology :
    (S.opensToSlice X).1.IsContinuous (Opens.grothendieckTopology X.obj.obj)
      (S.qcSite.grothendieckTopology.over X) := by
  have : RepresentablyFlat (S.opensToSlice X).1 := opensToSlice_representablyFlat S X
  exact (Functor.isContinuous_iff_coverPreserving (F := (S.opensToSlice X).1)
    (J := Opens.grothendieckTopology X.obj.obj)
    (K := S.qcSite.grothendieckTopology.over X)).2 (opensToSlice_coverPreserving_qcTopology S X)

/-- The functor `W ↦ W/X` into the localization of the small model is continuous. -/
instance qcSmallOpensFunctor_isContinuous :
    (qcSmallOpensFunctor S X).IsContinuous (Opens.grothendieckTopology X.obj.obj)
      (S.qcSite.smallOverTopology X) :=
  Functor.isContinuous_comp _ _ _ (S.qcSite.grothendieckTopology.over X) _

/-- **The bottom horizontal arrow of the diagram of Tag 0DAF**, the comparison morphism of topoi
`h₋₁ = a_X : Sh(LC_qc/X) → Sh(X)` of Section 09WY, with `Sh(LC_qc/X)` read as the sheaves on the
localization of the small model. -/
@[stacks 0DAF "the lower horizontal arrow h_{-1} : Sh(LC_qc/X) → Sh(X) of the diagram"]
def qcSmallBottomMorphism :
    MorphismOfTopoi (Sheaf (S.qcSite.smallOverTopology X) (Type u))
      (Sheaf (Opens.grothendieckTopology X.obj.obj) (Type u)) :=
  (qcTopologicalMorphism.{u, w, u} S X).comp
    (MorphismOfTopoi.ofEquivalence (S.qcSite.smallOverSheafEquiv X (Type u)))

/-- The inverse image of `h₋₁` is the functor `(h₋₁)^{-1}` of
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcSmallTopologicalInverseImage`. -/
theorem qcSmallBottomMorphism_inverseImage :
    (qcSmallBottomMorphism S X).inverseImage = qcSmallTopologicalInverseImage S X := rfl

/-- The direct image of `h₋₁` is restriction along the functor `W ↦ W/X`. -/
def qcSmallBottomPushforwardIso :
    (qcSmallBottomMorphism S X).pushforward ≅
      (qcSmallOpensFunctor S X).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X) :=
  Functor.isoWhiskerRight (S.qcSite.smallOverSheafEquivInverseIso X (Type u)) _ ≪≫ Iso.refl _

/-! ### Morphisms into the objects `W/X` -/

/-- The points of an object `y : V → X` of the localization of the small model: the transpose of
`y` across the comparison of `LC_qc` with its small model. -/
def qcSmallOverPoint (t : Over (S.qcSite.smallEquivalence.functor.obj X)) :
    S.qcSite.smallEquivalence.inverse.obj t.left ⟶ X :=
  (S.qcSite.smallEquivalence.symm.toAdjunction.homEquiv _ _).symm t.hom

/-- If `g : t ⟶ F(Y)` followed by `F(k)` is the structure map of `t`, the point of `t` is the
transpose of `g` followed by `k`. -/
private theorem qcSmallOverPoint_eq {t : Over (S.qcSite.smallEquivalence.functor.obj X)}
    {Y : S.category} (g : t.left ⟶ S.qcSite.smallEquivalence.functor.obj Y) (k : Y ⟶ X)
    (h : g ≫ S.qcSite.smallEquivalence.functor.map k = t.hom) :
    qcSmallOverPoint S X t =
      (S.qcSite.smallEquivalence.symm.toAdjunction.homEquiv _ _).symm g ≫ k := by
  rw [← S.qcSite.smallEquivalence.symm.toAdjunction.homEquiv_naturality_right_symm]
  exact congrArg _ h.symm

/-- Morphisms into an object `W/X` are unique. -/
theorem qcSmallOpens_hom_ext {t : Over (S.qcSite.smallEquivalence.functor.obj X)}
    {W : Opens X.obj} (f g : t ⟶ (qcSmallOpensFunctor S X).obj W) : f = g := by
  have := S.mono_opensToSlice_hom X W
  apply Over.OverMorphism.ext
  apply (cancel_mono (S.qcSite.smallEquivalence.functor.map ((S.opensToSlice X).1.obj W).hom)).1
  exact (Over.w f).trans (Over.w g).symm

/-- The points of the source of a morphism into `W/X` lie in `W`. -/
theorem qcSmallOpens_mem {t : Over (S.qcSite.smallEquivalence.functor.obj X)}
    {W : Opens X.obj} (f : t ⟶ (qcSmallOpensFunctor S X).obj W)
    (p : (S.qcSite.smallEquivalence.inverse.obj t.left).obj) :
    ((qcSmallOverPoint S X t : _ ⟶ X) : _ → X.obj) p ∈ W := by
  have ht := qcSmallOverPoint_eq S X f.left ((S.opensToSlice X).1.obj W).hom (Over.w f)
  rw [ht]
  exact S.opensToSlice_hom_mem W _

/-- A morphism into `W/X` from an object whose points lie in `W`. -/
def qcSmallOpensHomMk (t : Over (S.qcSite.smallEquivalence.functor.obj X)) (W : Opens X.obj)
    (h : ∀ p : (S.qcSite.smallEquivalence.inverse.obj t.left).obj,
      ((qcSmallOverPoint S X t : _ ⟶ X) : _ → X.obj) p ∈ W) :
    t ⟶ (qcSmallOpensFunctor S X).obj W := by
  let e := S.qcSite.smallEquivalence
  let ψ := (S.nonempty_over_hom_opensToSlice (Over.mk (qcSmallOverPoint S X t)) W h).some
  refine Over.homMk (e.symm.toAdjunction.homEquiv _ _ ψ.left) ?_
  change e.symm.toAdjunction.homEquiv _ _ ψ.left ≫ e.functor.map ((S.opensToSlice X).1.obj W).hom =
    t.hom
  calc e.symm.toAdjunction.homEquiv _ _ ψ.left ≫ e.functor.map ((S.opensToSlice X).1.obj W).hom
      = e.symm.toAdjunction.homEquiv _ _ (ψ.left ≫ ((S.opensToSlice X).1.obj W).hom) :=
        (e.symm.toAdjunction.homEquiv_naturality_right _ _).symm
    _ = e.symm.toAdjunction.homEquiv _ _ (qcSmallOverPoint S X t) :=
        congrArg (e.symm.toAdjunction.homEquiv _ _) (Over.w ψ)
    _ = t.hom := (e.symm.toAdjunction.homEquiv _ _).apply_symm_apply _

variable (U : SimplicialObject S.category) (a : U ⟶ (SimplicialObject.const S.category).obj X)

/-- The augmentation `a : U → X`, read as an augmentation of the underlying simplicial
topological space. -/
def qcTopologicalAugmentation : qcSimplicialSpace S U ⟶
    (SimplicialObject.const TopCat).obj
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj X) where
  app n := (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map (a.app n)
  naturality n m φ := by
    have h : U.map φ ≫ a.app m = a.app n := by simp
    change (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map (U.map φ) ≫
      (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map (a.app m) =
        (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map (a.app n) ≫ 𝟙 _
    rw [← Functor.map_comp, h, Category.comp_id]

/-- **The right vertical arrow of the diagram of Tag 0DAF**, the augmentation morphism of topoi
`a : Sh(U_Zar) → Sh(X)` of Tag 09W4. -/
abbrev qcZariskiAugmentation :
    MorphismOfTopoi (Sheaf (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)) (Type u))
      (Sheaf (Opens.grothendieckTopology X.obj.obj) (Type u)) :=
  (augmentationMorphism (qcSimplicialSpace S U) _
    (qcTopologicalAugmentation S X U a)).toMorphismOfTopoi

/-- The points of the image in the localization `LC_qc/X` of an object `V → U_n` of the total
site are its points followed by `a_n`. -/
theorem qcSmallOverPoint_totalForget (t : qcSmallTotal S X U a) :
    qcSmallOverPoint S X ((totalForget (qcSmallSemiRep S X U a)).obj t) =
      qcSmallPoint S X U a t ≫ a.app t.base := by
  exact qcSmallOverPoint_eq S X t.fiber.2.hom.left (a.app t.base) (Over.w t.fiber.2.hom)

/-! ### Sections over an open, read on the two sites -/

/-- An object `V → U_n` of the total site *lies over* an open `W` of `X` when its image `V/X` in
`LC_qc/X` maps to `W/X`, that is, when its points, carried to `X` by `a_n`, lie in `W`
(`qcSmallLiesOver.mem`, `qcSmallLiesOver.of_mem`). -/
abbrev qcSmallLiesOver (W : Opens X.obj) (t : qcSmallTotal S X U a) : Prop :=
  Nonempty ((totalForget (qcSmallSemiRep S X U a)).obj t ⟶ (qcSmallOpensFunctor S X).obj W)

/-- An object mapping to an object lying over `W` lies over `W`. -/
theorem qcSmallLiesOver.of_hom {W : Opens X.obj} {t t' : qcSmallTotal S X U a} (g : t' ⟶ t)
    (ht : qcSmallLiesOver S X U a W t) : qcSmallLiesOver S X U a W t' :=
  ⟨(totalForget (qcSmallSemiRep S X U a)).map g ≫ ht.some⟩

/-- The points of an object lying over `W`, carried to `X` by `a_n`, lie in `W`. -/
theorem qcSmallLiesOver.mem {W : Opens X.obj} {t : qcSmallTotal S X U a}
    (ht : qcSmallLiesOver S X U a W t)
    (p : (S.qcSite.smallEquivalence.inverse.obj t.fiber.2.left.left).obj) :
    ((qcSmallPoint S X U a t ≫ a.app t.base : _ ⟶ X) : _ → X.obj) p ∈ W := by
  have h := qcSmallOpens_mem S X ht.some p
  rwa [qcSmallOverPoint_totalForget] at h

/-- An object whose points, carried to `X` by `a_n`, all lie in `W` lies over `W`. -/
theorem qcSmallLiesOver.of_mem {W : Opens X.obj} {t : qcSmallTotal S X U a}
    (h : ∀ p : (S.qcSite.smallEquivalence.inverse.obj t.fiber.2.left.left).obj,
      ((qcSmallPoint S X U a t ≫ a.app t.base : _ ⟶ X) : _ → X.obj) p ∈ W) :
    qcSmallLiesOver S X U a W t :=
  ⟨qcSmallOpensHomMk S X _ W (fun p => by rw [qcSmallOverPoint_totalForget]; exact h p)⟩

/-- The open `a_n⁻¹(W)` of `U_n`. -/
abbrev qcFibreOpens (W : Opens X.obj) (n : SimplexCategoryᵒᵖ) :
    Opens ((qcSimplicialSpace S U).obj n) :=
  fibreOpens (qcSimplicialSpace S U) _ (qcTopologicalAugmentation S X U a) W n

/-- The comparison object of a simplicial open inside `a_n⁻¹(W)` lies over `W`. -/
theorem qcSmallLiesOver_comparisonObj {W : Opens X.obj} {A : SimplicialOpen (qcSimplicialSpace S U)}
    (h : A.toOpens ≤ qcFibreOpens S X U a W A.degree) :
    qcSmallLiesOver S X U a W (qcSmallComparisonObj S X U a A) :=
  qcSmallLiesOver.of_mem S X U a (fun p => h (qcSmallPoint_comparisonObj_mem S X U a A p))

/-- An object lying over `W` maps, in its own simplicial degree, to the comparison object of
`a_n⁻¹(W)`. -/
def qcSmallLiesOverHom {W : Opens X.obj} (t : qcSmallTotal S X U a)
    (ht : qcSmallLiesOver S X U a W t) :
    t ⟶ qcSmallComparisonObj S X U a ⟨t.base, qcFibreOpens S X U a W t.base⟩ :=
  qcSmallHomMk S X U a t _ (𝟙 _) (fun p => by
    rw [U.map_id, Category.comp_id]
    exact ht.mem S X U a p)

/-- The inclusion `a_m⁻¹(W) ⊆ U(β)⁻¹(a_n⁻¹(W))` of opens, for a simplex map `β`. -/
def qcFibreOpensHom (W : Opens X.obj) {m n : SimplexCategoryᵒᵖ} (β : m ⟶ n) :
    (⟨m, qcFibreOpens S X U a W m⟩ : SimplicialOpen (qcSimplicialSpace S U)) ⟶
      ⟨n, qcFibreOpens S X U a W n⟩ where
  base := β
  le x hx := by
    change ((qcTopologicalAugmentation S X U a).app n) (((qcSimplicialSpace S U).map β) x) ∈ W
    rw [← ConcreteCategory.comp_apply,
      augmentation_comp_app (qcSimplicialSpace S U) _ (qcTopologicalAugmentation S X U a) β]
    exact hx

/-- **Compatible families of sections over the objects of the total site lying over `W`.** -/
abbrev qcSmallTotalFamily (F : (qcSmallTotal S X U a)ᵒᵖ ⥤ Type u) (W : Opens X.obj) : Type u :=
  { x : ∀ t : qcSmallTotal S X U a, qcSmallLiesOver S X U a W t → F.obj (op t) //
    ∀ {t t' : qcSmallTotal S X U a} (g : t' ⟶ t) (ht ht'), F.map g.op (x t ht) = x t' ht' }

/-- **Compatible families of sections of a presheaf on the total site over the comparison objects
of the simplicial opens inside the fibre `a⁻¹(W)`.** -/
abbrev qcSmallZariskiFamily (F : (qcSmallTotal S X U a)ᵒᵖ ⥤ Type u) (W : Opens X.obj) : Type u :=
  { y : ∀ A : SimplicialOpen (qcSimplicialSpace S U),
      A.toOpens ≤ qcFibreOpens S X U a W A.degree → F.obj (op (qcSmallComparisonObj S X U a A)) //
    ∀ {A A' : SimplicialOpen (qcSimplicialSpace S U)} (g : A' ⟶ A) (h h'),
      F.map ((qcSmallComparisonFunctor S X U a).map g).op (y A h) = y A' h' }

/-- **The combinatorial core of Tag 0DAF.** A compatible family of sections of `F` over the
objects of the total site lying over `W` is the same as a compatible family of sections over the
comparison objects of the simplicial opens inside `a⁻¹(W)`: an object lying over `W` maps,
uniquely, to the comparison object of `a_n⁻¹(W)`. -/
def qcSmallFamilyEquiv (F : (qcSmallTotal S X U a)ᵒᵖ ⥤ Type u) (W : Opens X.obj) :
    qcSmallTotalFamily S X U a F W ≃
      qcSmallZariskiFamily S X U a F W where
  toFun x := ⟨fun A h => x.1 _ (qcSmallLiesOver_comparisonObj S X U a h),
    fun g _ _ => x.2 _ _ _⟩
  invFun y := ⟨fun t ht => F.map (qcSmallLiesOverHom S X U a t ht).op (y.1 _ le_rfl),
    fun {t t'} g ht ht' => by
      dsimp only
      let k := qcFibreOpensHom S X U a W g.base
      have he : g ≫ qcSmallLiesOverHom S X U a t ht =
          (qcSmallLiesOverHom S X U a t' ht' ≫ (qcSmallComparisonFunctor S X U a).map k :
            t' ⟶ qcSmallComparisonObj S X U a _) :=
        qcSmallComparison_hom_ext S X U a _ _
          ((Category.comp_id _).trans (Category.id_comp _).symm)
      calc F.map g.op (F.map (qcSmallLiesOverHom S X U a t ht).op (y.1 _ le_rfl))
          = F.map ((g ≫ qcSmallLiesOverHom S X U a t ht).op) (y.1 _ le_rfl) :=
            (Functor.map_comp_apply F (qcSmallLiesOverHom S X U a t ht).op g.op _).symm
        _ = F.map ((qcSmallLiesOverHom S X U a t' ht' ≫ (qcSmallComparisonFunctor S X U a).map k :
              t' ⟶ qcSmallComparisonObj S X U a _).op) (y.1 _ le_rfl) := by rw [he]
        _ = F.map (qcSmallLiesOverHom S X U a t' ht').op
              (F.map ((qcSmallComparisonFunctor S X U a).map k).op (y.1 _ le_rfl)) :=
            Functor.map_comp_apply F ((qcSmallComparisonFunctor S X U a).map k).op
              (qcSmallLiesOverHom S X U a t' ht').op _
        _ = _ := by rw [y.2 k]⟩
  left_inv x := Subtype.ext <| funext fun _ => funext fun _ => x.2 _ _ _
  right_inv y := by
    apply Subtype.ext
    funext A h
    let k : A ⟶ ⟨A.degree, qcFibreOpens S X U a W A.degree⟩ :=
      ⟨𝟙 _, fun x hx => by
        rw [(qcSimplicialSpace S U).map_id]
        exact h hx⟩
    have he : qcSmallLiesOverHom S X U a (qcSmallComparisonObj S X U a A)
        (qcSmallLiesOver_comparisonObj S X U a h) = (qcSmallComparisonFunctor S X U a).map k :=
      qcSmallComparison_hom_ext S X U a _ _ rfl
    change F.map (qcSmallLiesOverHom S X U a (qcSmallComparisonObj S X U a A)
        (qcSmallLiesOver_comparisonObj S X U a h)).op
        (y.1 ⟨A.degree, qcFibreOpens S X U a W A.degree⟩ le_rfl) = y.1 A h
    rw [he]
    exact y.2 k _ _

/-- Restriction of compatible families on the total site along an inclusion `W' ⊆ W`. -/
def qcSmallTotalFamily.restrict {F : (qcSmallTotal S X U a)ᵒᵖ ⥤ Type u} {W W' : Opens X.obj}
    (r : W' ≤ W) (x : qcSmallTotalFamily S X U a F W) : qcSmallTotalFamily S X U a F W' :=
  ⟨fun t ht => x.1 t ⟨ht.some ≫ (qcSmallOpensFunctor S X).map (homOfLE r)⟩,
    fun g _ _ => x.2 g _ _⟩

/-- Restriction of compatible families over the fibre along an inclusion `W' ⊆ W`. -/
def qcSmallZariskiFamily.restrict {F : (qcSmallTotal S X U a)ᵒᵖ ⥤ Type u} {W W' : Opens X.obj}
    (r : W' ≤ W) (y : qcSmallZariskiFamily S X U a F W) : qcSmallZariskiFamily S X U a F W' :=
  ⟨fun A h => y.1 A (h.trans ((Opens.map _).monotone r)), fun g _ _ => y.2 g _ _⟩

/-- Compatible families on the total site, pushed along a morphism of presheaves. -/
def qcSmallTotalFamily.map {F G : (qcSmallTotal S X U a)ᵒᵖ ⥤ Type u} (α : F ⟶ G)
    {W : Opens X.obj} (x : qcSmallTotalFamily S X U a F W) : qcSmallTotalFamily S X U a G W :=
  ⟨fun t ht => α.app _ (x.1 t ht), fun g ht ht' => by
    dsimp only
    rw [← NatTrans.naturality_apply, x.2 g ht ht']⟩

/-- Compatible families over the fibre, pushed along a morphism of presheaves. -/
def qcSmallZariskiFamily.map {F G : (qcSmallTotal S X U a)ᵒᵖ ⥤ Type u} (α : F ⟶ G)
    {W : Opens X.obj} (y : qcSmallZariskiFamily S X U a F W) : qcSmallZariskiFamily S X U a G W :=
  ⟨fun A h => α.app _ (y.1 A h), fun g h h' =>
    (NatTrans.naturality_apply α _ _).symm.trans (congrArg (α.app _) (y.2 g h h'))⟩

/-- `qcSmallFamilyEquiv` commutes with restriction along an inclusion `W' ⊆ W`. -/
theorem qcSmallFamilyEquiv_restrict (F : (qcSmallTotal S X U a)ᵒᵖ ⥤ Type u) {W W' : Opens X.obj}
    (r : W' ≤ W) (x : qcSmallTotalFamily S X U a F W) :
    qcSmallFamilyEquiv S X U a F W' (x.restrict S X U a r) =
      (qcSmallFamilyEquiv S X U a F W x).restrict S X U a r := rfl

/-- `qcSmallFamilyEquiv` is natural in the presheaf. -/
theorem qcSmallFamilyEquiv_map {F G : (qcSmallTotal S X U a)ᵒᵖ ⥤ Type u} (α : F ⟶ G)
    (W : Opens X.obj) (x : qcSmallTotalFamily S X U a F W) :
    qcSmallFamilyEquiv S X U a G W (x.map S X U a α) =
      (qcSmallFamilyEquiv S X U a F W x).map S X U a α := rfl

/-! ### The sections of `h₋₁,* a_{qc,*} F` -/

/-- An object lying over `W`, as a structured arrow from `W/X` along the localization functor. -/
def qcSmallLiesOverArrow {W : Opens X.obj} (t : qcSmallTotal S X U a)
    (ht : qcSmallLiesOver S X U a W t) :
    StructuredArrow (op ((qcSmallOpensFunctor S X).obj W))
      (totalForget (qcSmallSemiRep S X U a)).op :=
  StructuredArrow.mk (Y := op t) ht.some.op

/-- **The sections over `W/X` of the direct image along the augmentation of `(LC_qc/U)_total`**
are the compatible families of sections over the objects of the total site lying over `W`: the
direct image is the right Kan extension along `V/U_n ↦ V/X`, and its sections over `W/X` are the
limit over the objects whose image maps to `W/X`. -/
def qcSmallRanEquiv (F : (qcSmallTotal S X U a)ᵒᵖ ⥤ Type u) (W : Opens X.obj) :
    ((totalForget (qcSmallSemiRep S X U a)).op.ran.obj F).obj
        (op ((qcSmallOpensFunctor S X).obj W)) ≃ qcSmallTotalFamily S X U a F W :=
  ((Functor.ranObjObjIsoLimit _ F _).toEquiv.trans (Types.limitEquivSections _)).trans
    { toFun := fun s => ⟨fun t ht => s.1 (qcSmallLiesOverArrow S X U a t ht),
        fun g ht ht' => s.2 (StructuredArrow.homMk (f := qcSmallLiesOverArrow S X U a _ ht)
          (f' := qcSmallLiesOverArrow S X U a _ ht') g.op
          (Quiver.Hom.unop_inj (qcSmallOpens_hom_ext S X _ _)))⟩
      invFun := fun x => ⟨fun j => x.1 j.right.unop ⟨j.hom.unop⟩,
        fun {j j'} f => x.2 f.right.unop _ _⟩
      left_inv := fun s => by
        apply Subtype.ext
        funext j
        exact (s.2 (StructuredArrow.homMk (f := j)
          (f' := qcSmallLiesOverArrow S X U a j.right.unop ⟨j.hom.unop⟩) (𝟙 _)
          (Quiver.Hom.unop_inj (qcSmallOpens_hom_ext S X _ _)))).symm.trans
          (Functor.map_id_apply F _ _)
      right_inv := fun x => rfl }

/-- The component of `qcSmallRanEquiv` at an object `t` lying over `W` is the counit of the right
Kan extension at `t`, applied to the restriction of the section to the image of `t`. -/
theorem qcSmallRanEquiv_apply (F : (qcSmallTotal S X U a)ᵒᵖ ⥤ Type u) (W : Opens X.obj)
    (z : ((totalForget (qcSmallSemiRep S X U a)).op.ran.obj F).obj
      (op ((qcSmallOpensFunctor S X).obj W)))
    (t : qcSmallTotal S X U a) (ht : qcSmallLiesOver S X U a W t) :
    (qcSmallRanEquiv S X U a F W z).1 t ht =
      ((totalForget (qcSmallSemiRep S X U a)).op.ranCounit.app F).app (op t)
        (((totalForget (qcSmallSemiRep S X U a)).op.ran.obj F).map ht.some.op z) := by
  show ((Functor.ranObjObjIsoLimit _ F _).hom ≫ Limits.limit.π _
    (qcSmallLiesOverArrow S X U a t ht)) z = _
  rw [Functor.ranObjObjIsoLimit_hom_π]
  rfl

/-- `qcSmallRanEquiv` commutes with restriction along an inclusion `W' ⊆ W`. -/
theorem qcSmallRanEquiv_restrict (F : (qcSmallTotal S X U a)ᵒᵖ ⥤ Type u) {W W' : Opens X.obj}
    (r : W' ⟶ W)
    (z : ((totalForget (qcSmallSemiRep S X U a)).op.ran.obj F).obj
      (op ((qcSmallOpensFunctor S X).obj W))) :
    qcSmallRanEquiv S X U a F W'
        (((totalForget (qcSmallSemiRep S X U a)).op.ran.obj F).map
          ((qcSmallOpensFunctor S X).map r).op z) =
      (qcSmallRanEquiv S X U a F W z).restrict S X U a (leOfHom r) := by
  apply Subtype.ext
  funext t ht
  show _ = (qcSmallRanEquiv S X U a F W z).1 t _
  rw [qcSmallRanEquiv_apply, qcSmallRanEquiv_apply, ← Functor.map_comp_apply, ← op_comp,
    qcSmallOpens_hom_ext S X (ht.some ≫ (qcSmallOpensFunctor S X).map r)
      (Nonempty.some ⟨ht.some ≫ (qcSmallOpensFunctor S X).map (homOfLE (leOfHom r))⟩)]

/-- `qcSmallRanEquiv` is natural in the presheaf. -/
theorem qcSmallRanEquiv_map {F G : (qcSmallTotal S X U a)ᵒᵖ ⥤ Type u} (α : F ⟶ G)
    (W : Opens X.obj)
    (z : ((totalForget (qcSmallSemiRep S X U a)).op.ran.obj F).obj
      (op ((qcSmallOpensFunctor S X).obj W))) :
    qcSmallRanEquiv S X U a G W
        (((totalForget (qcSmallSemiRep S X U a)).op.ran.map α).app _ z) =
      (qcSmallRanEquiv S X U a F W z).map S X U a α := by
  apply Subtype.ext
  funext t ht
  show _ = α.app _ ((qcSmallRanEquiv S X U a F W z).1 t ht)
  rw [qcSmallRanEquiv_apply, qcSmallRanEquiv_apply, ← NatTrans.naturality_apply]
  exact ConcreteCategory.congr_hom
    (congr_app ((totalForget (qcSmallSemiRep S X U a)).op.ranCounit.naturality α) (op t)) _

/-! ### The sections of `a_* h_* F` -/

attribute [local instance] opens_subcanonical

/-- The sheaf `a⁻¹(h_W)` on `U_Zar`, whose sections over `(n, V)` are the proofs that
`V ⊆ a_n⁻¹(W)`. -/
abbrev qcFibreSupport (W : Opens X.obj) :
    Sheaf (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)) (Type u) :=
  fibreSupport (qcSimplicialSpace S U) _ (qcTopologicalAugmentation S X U a) W

/-- Sections over `W` of the direct image along the augmentation of `U_Zar` are the morphisms out
of `a⁻¹(h_W)`. -/
def qcZariskiSectionsHomEquiv
    (G : Sheaf (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)) (Type u))
    (W : Opens X.obj) :
    ((qcZariskiAugmentation S X U a).pushforward.obj G).obj.obj (op W) ≃
      (qcFibreSupport S X U a W ⟶ G) :=
  (Opens.grothendieckTopology _).yonedaEquiv.symm.trans
    ((qcZariskiAugmentation S X U a).adj.homEquiv _ _).symm

/-- Morphisms out of `a⁻¹(h_W)` into the direct image along `h` of a sheaf `F` on the total site
are the compatible families of sections of `F` over the comparison objects of the simplicial opens
inside `a⁻¹(W)`. -/
def qcFibreSupportHomEquiv (F : Sheaf (qcSmallTotalTopology S X U a) (Type u))
    (W : Opens X.obj) :
    (qcFibreSupport S X U a W ⟶ (qcSmallComparisonMorphism S X U a).pushforward.obj F) ≃
      qcSmallZariskiFamily S X U a F.obj W where
  toFun φ := ⟨fun A h => φ.hom.app (op A)
      ((augmentationOpenEquiv (qcSimplicialSpace S U) _ (qcTopologicalAugmentation S X U a) W
        A).symm (homOfLE h)),
    fun g _ _ => (NatTrans.naturality_apply φ.hom g.op _).symm.trans
      (congrArg _ (@Subsingleton.elim _ (subsingleton_fibreSupport _ _ _ _ _) _ _))⟩
  invFun y := ObjectProperty.homMk
    { app := fun A => TypeCat.ofHom fun p => y.1 A.unop (leOfHom
        (augmentationOpenEquiv (qcSimplicialSpace S U) _ (qcTopologicalAugmentation S X U a) W
          A.unop p))
      naturality := fun _ _ g => by
        ext p
        exact (y.2 g.unop _ _).symm }
  left_inv φ := by
    apply Sheaf.hom_ext
    ext A p
    exact congrArg (φ.hom.app A) (@Subsingleton.elim _ (subsingleton_fibreSupport _ _ _ _ _) _ _)
  right_inv y := rfl

/-- **The sections over `W` of `a_* h_* F`** are the compatible families of sections of `F` over
the comparison objects of the simplicial opens inside `a⁻¹(W)`. -/
def qcZariskiSectionsEquiv (F : Sheaf (qcSmallTotalTopology S X U a) (Type u)) (W : Opens X.obj) :
    ((qcZariskiAugmentation S X U a).pushforward.obj
        ((qcSmallComparisonMorphism S X U a).pushforward.obj F)).obj.obj (op W) ≃
      qcSmallZariskiFamily S X U a F.obj W :=
  (qcZariskiSectionsHomEquiv S X U a _ W).trans (qcFibreSupportHomEquiv S X U a F W)

/-- `qcZariskiSectionsEquiv` commutes with restriction along an inclusion `W' ⊆ W`. -/
theorem qcZariskiSectionsEquiv_restrict (F : Sheaf (qcSmallTotalTopology S X U a) (Type u))
    {W W' : Opens X.obj} (r : W' ⟶ W)
    (z : ((qcZariskiAugmentation S X U a).pushforward.obj
        ((qcSmallComparisonMorphism S X U a).pushforward.obj F)).obj.obj (op W)) :
    qcZariskiSectionsEquiv S X U a F W'
        (((qcZariskiAugmentation S X U a).pushforward.obj
          ((qcSmallComparisonMorphism S X U a).pushforward.obj F)).obj.map r.op z) =
      (qcZariskiSectionsEquiv S X U a F W z).restrict S X U a (leOfHom r) := by
  apply Subtype.ext
  funext A h
  show (((qcZariskiAugmentation S X U a).adj.homEquiv _ _).symm
      ((Opens.grothendieckTopology _).yonedaEquiv.symm
        (((qcZariskiAugmentation S X U a).pushforward.obj
          ((qcSmallComparisonMorphism S X U a).pushforward.obj F)).obj.map r.op z))).hom.app
        (op A) _ = (((qcZariskiAugmentation S X U a).adj.homEquiv _ _).symm
      ((Opens.grothendieckTopology _).yonedaEquiv.symm z)).hom.app (op A) _
  rw [GrothendieckTopology.yonedaEquiv_symm_map, Adjunction.homEquiv_naturality_left_symm]
  exact congrArg ((((qcZariskiAugmentation S X U a).adj.homEquiv _ _).symm
      ((Opens.grothendieckTopology _).yonedaEquiv.symm z)).hom.app (op A))
    (@Subsingleton.elim _ (subsingleton_fibreSupport _ _ _ _ _) _ _)

/-- `qcZariskiSectionsEquiv` is natural in the sheaf. -/
theorem qcZariskiSectionsEquiv_map {F F' : Sheaf (qcSmallTotalTopology S X U a) (Type u)}
    (k : F ⟶ F') (W : Opens X.obj)
    (z : ((qcZariskiAugmentation S X U a).pushforward.obj
        ((qcSmallComparisonMorphism S X U a).pushforward.obj F)).obj.obj (op W)) :
    qcZariskiSectionsEquiv S X U a F' W
        (((qcZariskiAugmentation S X U a).pushforward.map
          ((qcSmallComparisonMorphism S X U a).pushforward.map k)).hom.app (op W) z) =
      (qcZariskiSectionsEquiv S X U a F W z).map S X U a k.hom := by
  apply Subtype.ext
  funext A h
  show (((qcZariskiAugmentation S X U a).adj.homEquiv _ _).symm
      ((Opens.grothendieckTopology _).yonedaEquiv.symm
        (((qcZariskiAugmentation S X U a).pushforward.map
          ((qcSmallComparisonMorphism S X U a).pushforward.map k)).hom.app (op W) z))).hom.app
        (op A) _ = k.hom.app _ ((((qcZariskiAugmentation S X U a).adj.homEquiv _ _).symm
      ((Opens.grothendieckTopology _).yonedaEquiv.symm z)).hom.app (op A) _)
  rw [← GrothendieckTopology.yonedaEquiv_symm_naturality_right,
    Adjunction.homEquiv_naturality_right_symm]
  rfl

/-! ### The square -/

/-- The comparison of the sections over `W` of the two composite direct images. -/
def qcComparisonSquareSectionsEquiv (F : Sheaf (qcSmallTotalTopology S X U a) (Type u))
    (W : Opens X.obj) :
    (((qcSmallOpensFunctor S X).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X)).obj
          ((qcAugmentationMorphism S X U a).pushforward.obj F)).obj.obj (op W) ≃
      ((qcZariskiAugmentation S X U a).pushforward.obj
        ((qcSmallComparisonMorphism S X U a).pushforward.obj F)).obj.obj (op W) :=
  (qcSmallRanEquiv S X U a F.obj W).trans
    ((qcSmallFamilyEquiv S X U a F.obj W).trans (qcZariskiSectionsEquiv S X U a F W).symm)

/-- `qcComparisonSquareSectionsEquiv` commutes with restriction along an inclusion `W' ⊆ W`. -/
theorem qcComparisonSquareSectionsEquiv_restrict
    (F : Sheaf (qcSmallTotalTopology S X U a) (Type u)) {W W' : Opens X.obj} (r : W' ⟶ W)
    (z : (((qcSmallOpensFunctor S X).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X)).obj
          ((qcAugmentationMorphism S X U a).pushforward.obj F)).obj.obj (op W)) :
    qcComparisonSquareSectionsEquiv S X U a F W'
        ((((qcSmallOpensFunctor S X).sheafPushforwardContinuous (Type u)
          (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X)).obj
            ((qcAugmentationMorphism S X U a).pushforward.obj F)).obj.map r.op z) =
      ((qcZariskiAugmentation S X U a).pushforward.obj
        ((qcSmallComparisonMorphism S X U a).pushforward.obj F)).obj.map r.op
          (qcComparisonSquareSectionsEquiv S X U a F W z) := by
  apply (qcZariskiSectionsEquiv S X U a F W').injective
  rw [qcZariskiSectionsEquiv_restrict]
  refine (Equiv.apply_symm_apply _ _).trans ?_
  refine (congrArg (qcSmallFamilyEquiv S X U a F.obj W')
    (qcSmallRanEquiv_restrict S X U a F.obj r z)).trans ?_
  exact (qcSmallFamilyEquiv_restrict S X U a F.obj (leOfHom r) _).trans
    (congrArg _ (Equiv.apply_symm_apply (qcZariskiSectionsEquiv S X U a F W) _).symm)

/-- `qcComparisonSquareSectionsEquiv` is natural in the sheaf. -/
theorem qcComparisonSquareSectionsEquiv_map
    {F F' : Sheaf (qcSmallTotalTopology S X U a) (Type u)} (k : F ⟶ F') (W : Opens X.obj)
    (z : (((qcSmallOpensFunctor S X).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X)).obj
          ((qcAugmentationMorphism S X U a).pushforward.obj F)).obj.obj (op W)) :
    qcComparisonSquareSectionsEquiv S X U a F' W
        ((((qcSmallOpensFunctor S X).sheafPushforwardContinuous (Type u)
          (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X)).map
            ((qcAugmentationMorphism S X U a).pushforward.map k)).hom.app (op W) z) =
      (((qcZariskiAugmentation S X U a).pushforward.map
        ((qcSmallComparisonMorphism S X U a).pushforward.map k)).hom.app (op W)
          (qcComparisonSquareSectionsEquiv S X U a F W z)) := by
  apply (qcZariskiSectionsEquiv S X U a F' W).injective
  rw [qcZariskiSectionsEquiv_map]
  refine (Equiv.apply_symm_apply _ _).trans ?_
  refine (congrArg (qcSmallFamilyEquiv S X U a F'.obj W)
    (qcSmallRanEquiv_map S X U a k.hom W z)).trans ?_
  exact (qcSmallFamilyEquiv_map S X U a k.hom W _).trans
    (congrArg _ (Equiv.apply_symm_apply (qcZariskiSectionsEquiv S X U a F W) _).symm)

/-- The square of Tag 0DAF with `h₋₁,*` written as restriction along `W ↦ W/X`. -/
def qcComparisonSquareRestrictionIso :
    (qcAugmentationMorphism S X U a).pushforward ⋙
        (qcSmallOpensFunctor S X).sheafPushforwardContinuous (Type u)
          (Opens.grothendieckTopology X.obj.obj) (S.qcSite.smallOverTopology X) ≅
      (qcSmallComparisonMorphism S X U a).pushforward ⋙
        (qcZariskiAugmentation S X U a).pushforward :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _
      (NatIso.ofComponents
        (fun W => (qcComparisonSquareSectionsEquiv S X U a F W.unop).toIso)
        (fun {W W'} r => by
          ext z
          exact qcComparisonSquareSectionsEquiv_restrict S X U a F r.unop z)))
    (fun {F F'} k => by
      apply Sheaf.hom_ext
      ext W z
      exact qcComparisonSquareSectionsEquiv_map S X U a k W.unop z)

/-- **Tag 0DAF.** The diagram of topoi
```
Sh((LC_qc/U)_total) --h--> Sh(U_Zar)
        | a_qc                 | a
Sh(LC_qc/X)       --h₋₁--> Sh(X)
```
commutes: the direct image of `h₋₁ ∘ a_qc` is that of `a ∘ h`. -/
@[stacks 0DAF "the commutative diagram of topoi, on direct images"]
def qcComparisonSquarePushforwardIso :
    (qcAugmentationMorphism S X U a).pushforward ⋙ (qcSmallBottomMorphism S X).pushforward ≅
      (qcSmallComparisonMorphism S X U a).pushforward ⋙
        (qcZariskiAugmentation S X U a).pushforward :=
  Functor.isoWhiskerLeft _ (qcSmallBottomPushforwardIso S X) ≪≫
    qcComparisonSquareRestrictionIso S X U a

/-- **Tag 0DAF**, on inverse images: `a_qc⁻¹ ∘ h₋₁⁻¹ ≅ h⁻¹ ∘ a⁻¹`. The inverse images are left
adjoint to the direct images, so this is the conjugate of
`qcComparisonSquarePushforwardIso`. -/
@[stacks 0DAF "the commutative diagram of topoi, on inverse images"]
def qcComparisonSquareInverseImageIso :
    (qcZariskiAugmentation S X U a).inverseImage ⋙
        (qcSmallComparisonMorphism S X U a).inverseImage ≅
      qcSmallTopologicalInverseImage S X ⋙ (qcAugmentationMorphism S X U a).inverseImage :=
  (conjugateIsoEquiv
    ((qcSmallBottomMorphism S X).adj.comp (qcAugmentationMorphism S X U a).adj)
    ((qcZariskiAugmentation S X U a).adj.comp (qcSmallComparisonMorphism S X U a).adj)).symm
      (qcComparisonSquarePushforwardIso S X U a)

/-! ### An arbitrary simplicial object of `LC` -/

section Arbitrary

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-- A simplicial object of `LC` all of whose terms lie in a chosen site `LC_qc`, read as a
simplicial object of `LC_qc`. -/
abbrev qcLift (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (Y : SimplicialObject LocallyQuasiCompactHausdorff.{u})
    (hY : ∀ n, S.qcSite.Contains (Y.obj n)) : SimplicialObject S.category :=
  ObjectProperty.lift _ Y hY

/-- An augmentation in `LC` of a simplicial object lying in `LC_qc` towards an object of
`LC_qc`, read as an augmentation in `LC_qc`. -/
def qcLiftAugmentation (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    {Y : SimplicialObject LocallyQuasiCompactHausdorff.{u}} {T : LocallyQuasiCompactHausdorff.{u}}
    (b : Y ⟶ (SimplicialObject.const _).obj T) (hY : ∀ n, S.qcSite.Contains (Y.obj n))
    (hT : S.qcSite.Contains T) :
    qcLift S Y hY ⟶ (SimplicialObject.const S.category).obj ⟨T, hT⟩ where
  app n := ObjectProperty.homMk (b.app n)
  naturality _ _ φ := ObjectProperty.hom_ext _ (b.naturality φ)

/-- **Tag 0DAF for an arbitrary simplicial object of `LC`.** Let `U` be a simplicial object of
`LC` and let `a : U → X` be an augmentation. Then a site `LC_qc` of Tag 09X2 can be chosen
containing `X` and every `U_n`, and for it the square of topoi
`h₋₁ ∘ a_qc = a ∘ h` commutes, both on direct images and on inverse images. The right-hand
column is the augmentation of `U_Zar` towards `X` of Tag 09W4 for the underlying simplicial
space of `U` itself: the simplicial space of the lift is `U` followed by the inclusion of `LC`
into topological spaces, on the nose. -/
@[stacks 0DAF "for an arbitrary simplicial object U of LC and augmentation a : U → X: a site \
LC_qc containing X and the U_n exists, and for it the diagram of topoi commutes"]
theorem exists_qcComparisonSquare (Y : SimplicialObject LocallyQuasiCompactHausdorff.{u})
    (T : LocallyQuasiCompactHausdorff.{u}) (b : Y ⟶ (SimplicialObject.const _).obj T) :
    ∃ (S : LocallyQuasiCompactZariskiSituation.{u, u + 1} (Set.range Y.obj ∪ {T})
        Cardinal.stacksBound) (hY : ∀ n, S.qcSite.Contains (Y.obj n))
      (hT : S.qcSite.Contains T),
      qcSimplicialSpace S (qcLift S Y hY) = Y ⋙ locallyQuasiCompactHausdorffToTop ∧
      Nonempty ((qcAugmentationMorphism S ⟨T, hT⟩ (qcLift S Y hY)
          (qcLiftAugmentation S b hY hT)).pushforward ⋙
            (qcSmallBottomMorphism S ⟨T, hT⟩).pushforward ≅
        (qcSmallComparisonMorphism S ⟨T, hT⟩ (qcLift S Y hY)
          (qcLiftAugmentation S b hY hT)).pushforward ⋙
            (qcZariskiAugmentation S ⟨T, hT⟩ (qcLift S Y hY)
              (qcLiftAugmentation S b hY hT)).pushforward) ∧
      Nonempty ((qcZariskiAugmentation S ⟨T, hT⟩ (qcLift S Y hY)
          (qcLiftAugmentation S b hY hT)).inverseImage ⋙
            (qcSmallComparisonMorphism S ⟨T, hT⟩ (qcLift S Y hY)
              (qcLiftAugmentation S b hY hT)).inverseImage ≅
        qcSmallTopologicalInverseImage S ⟨T, hT⟩ ⋙
          (qcAugmentationMorphism S ⟨T, hT⟩ (qcLift S Y hY)
            (qcLiftAugmentation S b hY hT)).inverseImage) := by
  obtain ⟨B⟩ := exists_boundedLCSubcategory (Set.range Y.obj ∪ {T})
  obtain ⟨Q, hQ⟩ := exists_locallyQuasiCompactQcSite _ B
  let S : LocallyQuasiCompactZariskiSituation.{u, u + 1} (Set.range Y.obj ∪ {T})
      Cardinal.stacksBound := ⟨Q⟩
  have hc : ∀ Z ∈ Set.range Y.obj ∪ {T}, S.qcSite.Contains Z := fun Z hZ => by
    show lcSize Z < Q.boundedSubcategory.cutoff
    rw [hQ]
    exact B.contains_initial Z hZ
  have hY : ∀ n, S.qcSite.Contains (Y.obj n) := fun n => hc _ (Or.inl ⟨n, rfl⟩)
  have hT : S.qcSite.Contains T := hc _ (Or.inr rfl)
  exact ⟨S, hY, hT, rfl, ⟨qcComparisonSquarePushforwardIso S ⟨T, hT⟩ _ _⟩,
    ⟨qcComparisonSquareInverseImageIso S ⟨T, hT⟩ _ _⟩⟩

end Arbitrary

end Stacks.Topology.Simplicial

end
