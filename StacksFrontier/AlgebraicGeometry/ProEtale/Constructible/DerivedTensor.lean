module

public import StacksFrontier.Algebra.Homology.DerivedCategory.WeakSerreDevissage
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.WeakSerre
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.InverseImage
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.LocallyConstant
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorBoundedAbove
import StacksCore.Tactic.StacksAttribute

/-!
# Derived tensor products of constructible complexes on the pro-étale site

Let `X` be a scheme and `Λ` a Noetherian ring. If `K` and `L` are bounded above objects of the
derived category `D(X_proét, Λ)` of sheaves of `Λ`-modules on the small pro-étale site whose
cohomology sheaves are constructible (Tag 09AJ), then so is their derived tensor product
`K ⊗_Λ^L L`. This is Stacks 09BQ: `D_c^-(X_proét, Λ)` is stable under the derived tensor product.

## Main results

* `AlgebraicGeometry.ProEtale.isConstructibleModuleSheaf'_homology_tensor_single`: the cohomology
  sheaves of the derived tensor product of two constructible sheaves are constructible.
* `AlgebraicGeometry.ProEtale.isConstructibleModuleSheaf'_homology_tensor_of_isGE_of_isLE`: the
  same for bounded complexes with constructible cohomology sheaves.
* `AlgebraicGeometry.ProEtale.minus_tensor_and_isConstructibleModuleSheaf'_homology`:
  **Stacks 09BQ**.

## Implementation notes

The derived tensor product is `Stacks.ModuleSheaf.derivedMonoidal`, the tensor product of sheaves
of `Λ`-modules (`CategoryTheory.Sheaf.monoidalCategory`) derived by K-flat resolutions, on the
standard derived category.

The proof follows the source, which reduces to the bounded case by truncation and then, through
the comparison with the étale site, to the étale statement Tag 0961; here the bounded case is
proved directly on the pro-étale site. Boundedness above of `K ⊗_Λ^L L` is right t-exactness of
the derived tensor product, `Stacks.ModuleSheaf.isLE_tensor`, and in each degree the cohomology
sheaf only depends on bounded truncations of `K` and `L`
(`Stacks.ConstantSheaf.prop_homology_of_isLE_add`). Since constructible sheaves form a weak Serre
subcategory (Tag 09B5) and the derived tensor product is exact in each variable, the bounded case
reduces, by induction on the length of the two complexes
(`DerivedCategoryB.derivedCategoryB_map_obj_of_isGE_of_isLE`), to two single constructible
sheaves `F` and `G`. On an affine open, one constructible partition makes both locally constant
of finite type on every stratum (`AlgebraicGeometry.ProEtale.exists_stratification_forall`);
inverse image to a stratum commutes with the cohomology of the derived tensor product
(`Stacks.ModuleSheaf.nonempty_homology_sheafPullback_tensor_iso`), and on the stratum the
cohomology sheaves of the derived tensor product of two sheaves locally constant of finite type
are locally constant of finite type
(`Stacks.ModuleSheaf.isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_single`).

The coefficient ring lives in the universe `max (u + 1) w` of the module sections:
`ModuleCat.{s} Λ` is monoidal only for `Λ : Type s`, and the module sections must contain the
universe `u + 1` of the objects of the small pro-étale site. Every ring is isomorphic to one in
such a universe.

## References

* [Stacks Project, Tag 09BQ](https://stacks.math.columbia.edu/tag/09BQ)
* [Stacks Project, Tag 09AJ](https://stacks.math.columbia.edu/tag/09AJ)
* [Stacks Project, Tag 09B5](https://stacks.math.columbia.edu/tag/09B5)
* [Stacks Project, Tag 0961](https://stacks.math.columbia.edu/tag/0961)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Stacks.ModuleSheaf

universe t w u

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Sheaf.monoidalCategory derivedMonoidal

variable {X : Scheme.{u}} {Λ : Type (max (u + 1) w)} [CommRing Λ] [IsNoetherianRing Λ]
  [HasDerivedCategory.{t} (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))]

/-- The comma categories of pro-étale base change are cofiltered: base change preserves finite
limits. -/
theorem isFiltered_costructuredArrow_proetaleBaseChange {Z : Scheme.{u}} (g : Z ⟶ X)
    (V : Z.ProEtᵒᵖ) : IsFiltered (CostructuredArrow (Scheme.proetaleBaseChange g).op V) := by
  have : RepresentablyFlat (Scheme.proetaleBaseChange g) := flat_of_preservesFiniteLimits _
  exact IsFiltered.of_equivalence
    (structuredArrowOpEquivalence (Scheme.proetaleBaseChange g) (Opposite.unop V))

/-- **The cohomology sheaves of the derived tensor product of two constructible sheaves of
`Λ`-modules on the small pro-étale site are constructible.** -/
theorem isConstructibleModuleSheaf'_homology_tensor_single
    {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)}
    (hF : IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ F)
    (hG : IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ G) (n : ℤ) :
    IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
      ((DerivedCategory.homologyFunctor _ n).obj
        ((DerivedCategory.singleFunctor _ 0).obj F ⊗
          (DerivedCategory.singleFunctor _ 0).obj G)) := by
  intro U
  obtain ⟨r, hr⟩ := exists_stratification_forall (F := ![F, G])
    (fun j => by fin_cases j <;> assumption) U
  refine ⟨r, fun k => ?_⟩
  let := HasDerivedCategory.standard
    (Sheaf (Scheme.ProEt.topology (r.piece k)) (ModuleCat.{max (u + 1) w} Λ))
  let g := r.inclusion k
  have := isFiltered_costructuredArrow_proetaleBaseChange g
  let Φ := (Scheme.proetaleBaseChange g).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology (r.piece k))
  let e := proetaleModuleInverseImageIsoSheafPullback.{u, max (u + 1) w, w} Λ g
  have : PreservesFiniteLimits Φ := preservesFiniteLimits_of_natIso e
  have hF' : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, w}
      (Scheme.ProEt.topology (r.piece k)) Λ (Φ.obj F) :=
    ObjectProperty.prop_of_iso _ (e.app F) (hr k 0)
  have hG' : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, w}
      (Scheme.ProEt.topology (r.piece k)) Λ (Φ.obj G) :=
    ObjectProperty.prop_of_iso _ (e.app G) (hr k 1)
  obtain ⟨e₁⟩ := nonempty_homology_sheafPullback_tensor_iso (Scheme.proetaleBaseChange g) Λ
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology (r.piece k))
    ((DerivedCategory.singleFunctor _ 0).obj F) ((DerivedCategory.singleFunctor _ 0).obj G) 0 n
  refine ObjectProperty.prop_of_iso _ ?_
    (isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_single hF' hG' n)
  exact ((DerivedCategory.homologyFunctor _ n).mapIso
    ((Φ.mapDerivedCategorySingleFunctor 0).app F ⊗ᵢ
      (Φ.mapDerivedCategorySingleFunctor 0).app G)).symm ≪≫ e₁.symm ≪≫ (e.app _).symm

/-- **The cohomology sheaves of the derived tensor product of two bounded complexes with
constructible cohomology sheaves are constructible.** By induction on the length of the two
complexes, using the truncation triangles, the exactness of the derived tensor product in each
variable and the weak Serre property of constructible sheaves (Tag 09B5), this reduces to the case
of single sheaves. -/
theorem isConstructibleModuleSheaf'_homology_tensor_of_isGE_of_isLE
    (K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
    (a b a' b' : ℤ) [K.IsGE a] [K.IsLE b] [L.IsGE a'] [L.IsLE b']
    (hK : ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
      ((DerivedCategory.homologyFunctor _ i).obj K))
    (hL : ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
      ((DerivedCategory.homologyFunctor _ i).obj L)) (n : ℤ) :
    IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
      ((DerivedCategory.homologyFunctor _ n).obj (K ⊗ L)) := by
  let W : ObjectProperty (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) :=
    fun F => IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ F
  have := isWeakSerreClass_isConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
  have hW : WeakSerre.IsWeakSerre W := WeakSerre.isWeakSerre_of_isWeakSerreClass W
  have step : ∀ G, W G → DerivedCategoryB.derivedCategoryB W
      (K ⊗ (DerivedCategory.singleFunctor _ 0).obj G) := by
    intro G hG
    obtain ⟨s, hs⟩ := exists_commShift_isTriangulated_tensorRight _ Λ
      ((DerivedCategory.singleFunctor _ 0).obj G)
    let := s
    exact DerivedCategoryB.derivedCategoryB_map_obj_of_isGE_of_isLE
      (tensorRight ((DerivedCategory.singleFunctor _ 0).obj G)) W hW W
      (fun M hM i => isConstructibleModuleSheaf'_homology_tensor_single hM hG i) K a b hK
  obtain ⟨s, hs⟩ := exists_commShift_isTriangulated_tensorLeft _ Λ K
  let := s
  exact DerivedCategoryB.derivedCategoryB_map_obj_of_isGE_of_isLE (tensorLeft K) W hW W step
    L a' b' hL n

/-- **Stacks 09BQ.** Let `X` be a scheme and `Λ` a Noetherian ring. If `K` and `L` are bounded
above objects of `D(X_proét, Λ)` whose cohomology sheaves are constructible, then their derived
tensor product `K ⊗_Λ^L L` is bounded above and has constructible cohomology sheaves: it lies in
`D_c^-(X_proét, Λ)`. -/
@[stacks 09BQ]
theorem minus_tensor_and_isConstructibleModuleSheaf'_homology
    (K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
    (hK : DerivedCategory.TStructure.t.minus K) (hL : DerivedCategory.TStructure.t.minus L)
    (hKc : ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
      ((DerivedCategory.homologyFunctor _ i).obj K))
    (hLc : ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
      ((DerivedCategory.homologyFunctor _ i).obj L)) :
    DerivedCategory.TStructure.t.minus (K ⊗ L) ∧
      ∀ i, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
        ((DerivedCategory.homologyFunctor _ i).obj (K ⊗ L)) := by
  let W : ObjectProperty (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) :=
    fun F => IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ F
  have := isWeakSerreClass_isConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
  have hbound : ∀ (K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{max (u + 1) w} Λ))) (a b : ℤ), K.IsLE a → L.IsLE b →
      (((curriedTensor _).obj K).obj L).IsLE (a + b) :=
    fun K L a b _ _ => isLE_tensor K L a b
  obtain ⟨a, ha⟩ := hK
  obtain ⟨b, hb⟩ := hL
  refine ⟨⟨a + b, hbound K L a b ha hb⟩, ?_⟩
  have hl := fun K => exists_commShift_isTriangulated_tensorLeft
    (Scheme.ProEt.topology X) Λ K
  have hr := fun L => exists_commShift_isTriangulated_tensorRight
    (Scheme.ProEt.topology X) Λ L
  let : ∀ K, ((curriedTensor (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{max (u + 1) w} Λ)))).obj K).CommShift ℤ := fun K => (hl K).choose
  have : ∀ K, ((curriedTensor (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{max (u + 1) w} Λ)))).obj K).IsTriangulated := fun K => (hl K).choose_spec
  let : ∀ L, ((curriedTensor (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{max (u + 1) w} Λ)))).flip.obj L).CommShift ℤ := fun L => (hr L).choose
  have : ∀ L, ((curriedTensor (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{max (u + 1) w} Λ)))).flip.obj L).IsTriangulated := fun L => (hr L).choose_spec
  refine Stacks.ConstantSheaf.prop_homology_of_isLE_add (curriedTensor _) W hbound
    (fun K L hK hL i => ?_) ⟨K, ⟨a, ha⟩⟩ ⟨L, ⟨b, hb⟩⟩ hKc hLc
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := K.property
  obtain ⟨⟨c', hc'⟩, ⟨d', hd'⟩⟩ := L.property
  exact isConstructibleModuleSheaf'_homology_tensor_of_isGE_of_isLE K.obj L.obj c d c' d' hK hL i

end AlgebraicGeometry.ProEtale
