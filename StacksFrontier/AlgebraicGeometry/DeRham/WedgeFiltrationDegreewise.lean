module

public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltration
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.ImageFiltration
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.WedgeImageSystem
public import StacksFrontier.Algebra.Homology.SpectralSequence.SpectralObjectConvergence
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.WedgeProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.DiffOpBoxTotal
public import StacksFrontier.AlgebraicGeometry.DeRham.TotalComplexImageSubobject
public import StacksFrontier.CategoryTheory.Abelian.InverseSystem

/-!
# The wedge filtration of a de Rham complex, degree by degree

`AlgebraicGeometry.SheafOfModules.wedgeFiltered` is the wedge filtration of `Ω^•` determined by a
morphism of complexes `ι : P ⟶ Ω^•`: its `k`-th step is the image of the wedge map
`Tot(σ^{≥k}P ⊗_A Ω^•) ⟶ Ω^•`. This file reads that step in a single degree, as the image of the
degree-`n` component of the wedge map, and computes that image from the summands of the total
complex.

## Main results

* `AlgebraicGeometry.SheafOfModules.isZero_wedgeFiltrationStep_X` and
  `AlgebraicGeometry.SheafOfModules.isZero_wedgeFiltered_filtration_obj_X`: the `k`-th step
  vanishes in degrees below `k`.
* `AlgebraicGeometry.SheafOfModules.mapSubobjects_wedgeFiltrationStep`: the degree-`n` term of the
  `k`-th step is the image of the degree-`n` component of the wedge map.
* `AlgebraicGeometry.SheafOfModules.isLUB_imageSubobject_ιMapBifunctor_wedgeAlong` and
  `AlgebraicGeometry.SheafOfModules.imageSubobject_wedgeAlongBrutal_eq_of_le`: that degree-`m`
  image is the least upper bound of the images of the summands `P^i ⊗_A Ω^{m-i}`, and is the
  image of the single summand at `i = k` as soon as that one dominates the summands above it —
  the summands below `k` vanish.
* `AlgebraicGeometry.SheafOfModules.ιMapBifunctor_comp_wedgeAlong_f` and
  `AlgebraicGeometry.SheafOfModules.imageSubobject_ιMapBifunctor_wedgeAlongBrutal_eq_of_le`: on the
  `(i, j)` summand the wedge map is `ι` in degree `i` tensored with `Ω^j`, followed by the wedge
  multiplication `Ω^i ⊗_A Ω^j ⟶ Ω^{i+j}`; above the cut the brutal truncation does not change the
  image of that summand.
* `AlgebraicGeometry.SheafOfModules.imageSubobject_wedgeAlongBrutal_eq_of_le_summand`: the
  dominance hypothesis read on those summand maps, with no total complex left in it.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.Tensor (sheafTensor ringSheaf)

universe v u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

/-- Evaluation in a fixed degree preserves pushouts of complexes of `A`-modules. The instance is
supplied explicitly: the generic search, which goes through `HasColimit` for each degree of the
diagram separately, exceeds the default instance-synthesis budget at these binders. -/
local instance preservesColimitSpanEval (n : ℤ)
    {K L M : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf A)) ℤ}
    (f : K ⟶ L) (g : K ⟶ M) :
    PreservesColimit (span f g) (HomologicalComplex.eval
      (_root_.SheafOfModules.{u} (ringSheaf A)) (ComplexShape.up ℤ) n) :=
  PreservesColimitsOfShape.preservesColimit

/-- **The `k`-th step of the wedge filtration vanishes below `k`**, for `k ≥ 1`. -/
theorem isZero_wedgeFiltrationStep_X
    (P : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf A)) ℕ)
    (ι : P ⟶ deRhamComplex B D) (k : ℤ) (hk : 0 < k) (n : ℤ) (h : n < k) :
    IsZero ((Subobject.underlying.obj (wedgeFiltrationStep B D P ι k)).X n) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = (j : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
  exact (wedgeImageSystem B D P ι).isZero_filtrationStep_X_of_isZero j n
    (CochainComplex.isZero_wedgeSourceInt_X (sheafTensor.{u,u,u,u,u} A) (deRhamComplex B D) P
      (by push_cast; omega))

/-- **The wedge filtration is concentrated in degrees `≥ k` at its `k`-th step**, for `k ≥ 1`,
read on the filtered complex. -/
theorem isZero_wedgeFiltered_filtration_obj_X
    (P : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf A)) ℕ)
    (ι : P ⟶ deRhamComplex B D) (k : ℤ) (hk : 0 < k) (n : ℤ) (h : n < k) :
    IsZero (((wedgeFiltered B D P ι).filtration.obj (op k)).X n) :=
  isZero_wedgeFiltrationStep_X B D P ι k hk n h

/-- The degree-`n` term of the image of a morphism of complexes is the image of its degree-`n`
component. -/
theorem mapSubobjects_imageSubobject
    {K L : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf A)) ℤ}
    (ψ : K ⟶ L) (n : ℤ) :
    (mapSubobjects (HomologicalComplex.eval
          (_root_.SheafOfModules.{u} (ringSheaf A)) (ComplexShape.up ℤ) n) L).obj
        (imageSubobject ψ) = imageSubobject (ψ.f n) := by
  change (mapSubobjects _ L).obj (Subobject.mk (image.ι ψ)) = _
  rw [mapSubobjects_mk, map_imageSubobject_eq]
  rfl

/-- **The degree-`n` term of the `k`-th step of the wedge filtration**, for `k ≥ 1`: the image of
the degree-`n` component of the wedge map on the `k`-th brutal truncation of `P`. -/
theorem mapSubobjects_wedgeFiltrationStep
    (P : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf A)) ℕ)
    (ι : P ⟶ deRhamComplex B D) (k : ℤ) (hk : 0 < k) (n : ℤ) :
    (mapSubobjects (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)
        (deRhamComplexInt B D)).obj (wedgeFiltrationStep B D P ι k) =
      imageSubobject ((CochainComplex.wedgeAlongBrutalInt (sheafTensor.{u,u,u,u,u} A)
        (wedgeProduct B D) P ι k.toNat).f n) := by
  change (mapSubobjects (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)
      (deRhamComplexInt B D)).obj ((wedgeImageSystem B D P ι).filtrationStep k) = _
  rw [(wedgeImageSystem B D P ι).filtrationStep_of_pos hk]
  exact mapSubobjects_imageSubobject (A := A) _ n

/-- The index of the summand `P^k ⊗_A Ω^{m-k}` of the total complex in total degree `m`. -/
theorem piNat_add_sub_mem (k m : ℕ) (h : k ≤ m) :
    ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (k, m - k)
      ∈ ({m} : Set ℕ) := by
  change k + (m - k) = m
  omega

/-- **The degree-`m` image of the wedge map is the least upper bound of the images of its
summands** `P^i ⊗_A Ω^j` with `i + j = m`. -/
theorem isLUB_imageSubobject_ιMapBifunctor_wedgeAlong
    (P : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf A)) ℕ)
    (ι : P ⟶ deRhamComplex B D) (m : ℕ) :
    IsLUB (Set.range (fun ij : (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
          (ComplexShape.up ℕ)) ⁻¹' {m} =>
        imageSubobject (HomologicalComplex.ιMapBifunctor P (deRhamComplex B D)
            (sheafTensor.{u,u,u,u,u} A) (ComplexShape.up ℕ) ij.1.1 ij.1.2 m ij.2 ≫
          (CochainComplex.wedgeAlong (sheafTensor.{u,u,u,u,u} A) (wedgeProduct B D) P ι).f m)))
      (imageSubobject
        ((CochainComplex.wedgeAlong (sheafTensor.{u,u,u,u,u} A) (wedgeProduct B D) P ι).f m)) :=
  HomologicalComplex₂.isLUB_imageSubobject_ιTotal_comp _ _

/-- **The summands of `Tot(σ^{≥k}P ⊗_A Ω^•)` below the cut contribute nothing**: on a summand
`(σ^{≥k}P)^i ⊗_A Ω^j` with `i < k` the image of the wedge map is `⊥`. -/
theorem imageSubobject_ιMapBifunctor_wedgeAlongBrutal_eq_bot
    (P : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf A)) ℕ)
    (ι : P ⟶ deRhamComplex B D) (k m : ℕ)
    (ij : (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ)) ⁻¹' {m}) (hij : ij.1.1 < k) :
    imageSubobject (HomologicalComplex.ιMapBifunctor (CochainComplex.brutal P k)
          (deRhamComplex B D) (sheafTensor.{u,u,u,u,u} A) (ComplexShape.up ℕ) ij.1.1 ij.1.2 m ij.2 ≫
        (CochainComplex.wedgeAlong (sheafTensor.{u,u,u,u,u} A) (wedgeProduct B D)
          (CochainComplex.brutal P k) (CochainComplex.ιBrutal P k ≫ ι)).f m) = ⊥ := by
  have hz : IsZero (((sheafTensor.{u,u,u,u,u} A).obj ((CochainComplex.brutal P k).X ij.1.1)).obj
      ((deRhamComplex B D).X ij.1.2)) :=
    ((sheafTensor.{u,u,u,u,u} A).flip.obj ((deRhamComplex B D).X ij.1.2)).map_isZero
      (CochainComplex.isZero_brutal_X P (by omega))
  have h0 : HomologicalComplex.ιMapBifunctor (CochainComplex.brutal P k)
        (deRhamComplex B D) (sheafTensor.{u,u,u,u,u} A) (ComplexShape.up ℕ) ij.1.1 ij.1.2 m ij.2 ≫
      (CochainComplex.wedgeAlong (sheafTensor.{u,u,u,u,u} A) (wedgeProduct B D)
        (CochainComplex.brutal P k) (CochainComplex.ιBrutal P k ≫ ι)).f m = 0 :=
    hz.eq_of_src _ _
  rw [h0, imageSubobject_zero]

/-- **The wedge map on a single summand of the total complex**: on the `(i, j)` summand it is the
degree-`i` component of `ι` tensored with the identity of `Ω^j`, followed by the wedge
multiplication `Ω^i ⊗_A Ω^j ⟶ Ω^{i+j}`. -/
theorem ιMapBifunctor_comp_wedgeAlong_f
    (P : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf A)) ℕ)
    (ι : P ⟶ deRhamComplex B D) (i j m : ℕ) (h : i + j = m) :
    HomologicalComplex.ιMapBifunctor P (deRhamComplex B D) (sheafTensor.{u,u,u,u,u} A)
          (ComplexShape.up ℕ) i j m h ≫
        (CochainComplex.wedgeAlong (sheafTensor.{u,u,u,u,u} A) (wedgeProduct B D) P ι).f m =
      ((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫
        exteriorProductComponent B i j ≫ ((deRhamComplex B D).XIsoOfEq h).hom := by
  refine Eq.trans (Category.assoc
      (HomologicalComplex.ιMapBifunctor P (deRhamComplex B D) (sheafTensor.{u,u,u,u,u} A)
        (ComplexShape.up ℕ) i j m h)
      ((HomologicalComplex.mapBifunctorMap ι (𝟙 (deRhamComplex B D)) (sheafTensor.{u,u,u,u,u} A)
        (ComplexShape.up ℕ)).f m) ((wedgeProduct B D).f m)).symm ?_
  refine Eq.trans (congrArg (· ≫ (wedgeProduct B D).f m)
    (HomologicalComplex.ι_mapBifunctorMap ι (𝟙 (deRhamComplex B D)) (sheafTensor.{u,u,u,u,u} A)
      (ComplexShape.up ℕ) i j m h)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg (((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫ ·) ?_
  refine Eq.trans (congrArg (· ≫ (wedgeProduct B D).f m)
    (congrArg (· ≫ HomologicalComplex.ιMapBifunctor (deRhamComplex B D) (deRhamComplex B D)
        (sheafTensor.{u,u,u,u,u} A) (ComplexShape.up ℕ) i j m h)
      (CategoryTheory.Functor.map_id ((sheafTensor.{u,u,u,u,u} A).obj ((deRhamComplex B D).X i))
        ((deRhamComplex B D).X j)))) ?_
  refine Eq.trans (congrArg (· ≫ (wedgeProduct B D).f m) (Category.id_comp _)) ?_
  exact ι_wedgeProductDesc B D i j m h

/-- **Above the cut the brutal truncation does not change the summand image**: for `k ≤ i` the
image of the `(i, j)` summand of the wedge map on `σ^{≥k}P` is the image of the degree-`i`
component of `ι` tensored with `Ω^j`, followed by the wedge multiplication. -/
theorem imageSubobject_ιMapBifunctor_wedgeAlongBrutal_eq_of_le
    (P : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf A)) ℕ)
    (ι : P ⟶ deRhamComplex B D) (k i j m : ℕ) (hk : k ≤ i) (h : i + j = m) :
    imageSubobject (HomologicalComplex.ιMapBifunctor (CochainComplex.brutal P k)
          (deRhamComplex B D) (sheafTensor.{u,u,u,u,u} A) (ComplexShape.up ℕ) i j m h ≫
        (CochainComplex.wedgeAlong (sheafTensor.{u,u,u,u,u} A) (wedgeProduct B D)
          (CochainComplex.brutal P k) (CochainComplex.ιBrutal P k ≫ ι)).f m) =
      imageSubobject (((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫
        exteriorProductComponent B i j ≫ ((deRhamComplex B D).XIsoOfEq h).hom) := by
  have htop : CochainComplex.brutalStep P k i = ⊤ := by
    simp [CochainComplex.brutalStep, hk]
  have hiso : IsIso ((CochainComplex.brutalStep P k i).arrow) :=
    (Subobject.isIso_arrow_iff_eq_top _).2 htop
  have : IsIso (((sheafTensor.{u,u,u,u,u} A).map ((CochainComplex.brutalStep P k i).arrow)).app
      ((deRhamComplex B D).X j)) :=
    NatIso.isIso_app_of_isIso
      ((sheafTensor.{u,u,u,u,u} A).map ((CochainComplex.brutalStep P k i).arrow)) _
  have harrow : (CochainComplex.ιBrutal P k ≫ ι).f i =
      (CochainComplex.brutalStep P k i).arrow ≫ ι.f i :=
    congrArg (· ≫ ι.f i)
      (HomologicalComplex.subcomplexOfSubobjectsι_f P (CochainComplex.brutalStep P k)
        (CochainComplex.brutalStep_factors P k) i)
  have hfac : HomologicalComplex.ιMapBifunctor (CochainComplex.brutal P k) (deRhamComplex B D)
          (sheafTensor.{u,u,u,u,u} A) (ComplexShape.up ℕ) i j m h ≫
        (CochainComplex.wedgeAlong (sheafTensor.{u,u,u,u,u} A) (wedgeProduct B D)
          (CochainComplex.brutal P k) (CochainComplex.ιBrutal P k ≫ ι)).f m =
      ((sheafTensor.{u,u,u,u,u} A).map ((CochainComplex.brutalStep P k i).arrow)).app
          ((deRhamComplex B D).X j) ≫
        (((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫
          exteriorProductComponent B i j ≫ ((deRhamComplex B D).XIsoOfEq h).hom) := by
    refine (ιMapBifunctor_comp_wedgeAlong_f B D _ _ i j m h).trans ?_
    refine Eq.trans (congrArg (· ≫ (exteriorProductComponent B i j ≫
        ((deRhamComplex B D).XIsoOfEq h).hom))
      (Eq.trans
        (congrArg (fun t => ((sheafTensor.{u,u,u,u,u} A).map t).app ((deRhamComplex B D).X j))
          harrow)
        (congrArg (fun t => NatTrans.app t ((deRhamComplex B D).X j))
          ((sheafTensor.{u,u,u,u,u} A).map_comp (CochainComplex.brutalStep P k i).arrow
            (ι.f i))))) ?_
    exact Category.assoc _ _ _
  exact (CategoryTheory.Abelian.SpectralObject.imageSubobject_congr hfac).trans
    (imageSubobject_iso_comp
      (((sheafTensor.{u,u,u,u,u} A).map ((CochainComplex.brutalStep P k i).arrow)).app
        ((deRhamComplex B D).X j))
      (((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫
        exteriorProductComponent B i j ≫ ((deRhamComplex B D).XIsoOfEq h).hom))

/-- **A dominating summand carries the whole degree-`m` term of the `k`-th step**: if the image of
the wedge map on the summand `(σ^{≥k}P)^k ⊗_A Ω^{m-k}` contains the image on every summand
`(σ^{≥k}P)^i ⊗_A Ω^{m-i}` with `i ≥ k`, then it is the whole degree-`m` image. -/
theorem imageSubobject_wedgeAlongBrutal_eq_of_le
    (P : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf A)) ℕ)
    (ι : P ⟶ deRhamComplex B D) (k m : ℕ) (hk : k ≤ m)
    (hdom : ∀ ij : (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ)) ⁻¹' {m}, k ≤ ij.1.1 →
      imageSubobject (HomologicalComplex.ιMapBifunctor (CochainComplex.brutal P k)
            (deRhamComplex B D) (sheafTensor.{u,u,u,u,u} A) (ComplexShape.up ℕ) ij.1.1 ij.1.2 m
              ij.2 ≫
          (CochainComplex.wedgeAlong (sheafTensor.{u,u,u,u,u} A) (wedgeProduct B D)
            (CochainComplex.brutal P k) (CochainComplex.ιBrutal P k ≫ ι)).f m) ≤
        imageSubobject (HomologicalComplex.ιMapBifunctor (CochainComplex.brutal P k)
            (deRhamComplex B D) (sheafTensor.{u,u,u,u,u} A) (ComplexShape.up ℕ) k (m - k) m
              (piNat_add_sub_mem k m hk) ≫
          (CochainComplex.wedgeAlong (sheafTensor.{u,u,u,u,u} A) (wedgeProduct B D)
            (CochainComplex.brutal P k) (CochainComplex.ιBrutal P k ≫ ι)).f m)) :
    imageSubobject ((CochainComplex.wedgeAlong (sheafTensor.{u,u,u,u,u} A) (wedgeProduct B D)
          (CochainComplex.brutal P k) (CochainComplex.ιBrutal P k ≫ ι)).f m) =
      imageSubobject (HomologicalComplex.ιMapBifunctor (CochainComplex.brutal P k)
          (deRhamComplex B D) (sheafTensor.{u,u,u,u,u} A) (ComplexShape.up ℕ) k (m - k) m
            (piNat_add_sub_mem k m hk) ≫
        (CochainComplex.wedgeAlong (sheafTensor.{u,u,u,u,u} A) (wedgeProduct B D)
          (CochainComplex.brutal P k) (CochainComplex.ιBrutal P k ≫ ι)).f m) :=
  HomologicalComplex₂.imageSubobject_eq_of_isGreatest _ _
    ⟨(k, m - k), piNat_add_sub_mem k m hk⟩
    (fun ij => by
      by_cases hik : k ≤ ij.1.1
      · exact hdom ij hik
      · exact (imageSubobject_ιMapBifunctor_wedgeAlongBrutal_eq_bot B D P ι k m ij
          (by omega)).trans_le bot_le)

/-- **The dominance hypothesis read on the summand maps.** The degree-`m` term of the `k`-th step
is the image of the single summand at `i = k` as soon as, for every `i ≥ k` with `i + j = m`, the
image of `ι` in degree `i` tensored with `Ω^j` followed by the wedge multiplication is contained
in the one at `i = k`. -/
theorem imageSubobject_wedgeAlongBrutal_eq_of_le_summand
    (P : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf A)) ℕ)
    (ι : P ⟶ deRhamComplex B D) (k m : ℕ) (hk : k ≤ m)
    (hdom : ∀ (i j : ℕ), k ≤ i → ∀ h : i + j = m,
      imageSubobject (((sheafTensor.{u,u,u,u,u} A).map (ι.f i)).app ((deRhamComplex B D).X j) ≫
          exteriorProductComponent B i j ≫ ((deRhamComplex B D).XIsoOfEq h).hom) ≤
        imageSubobject (((sheafTensor.{u,u,u,u,u} A).map (ι.f k)).app
            ((deRhamComplex B D).X (m - k)) ≫
          exteriorProductComponent B k (m - k) ≫
          ((deRhamComplex B D).XIsoOfEq (show k + (m - k) = m by omega)).hom)) :
    imageSubobject ((CochainComplex.wedgeAlong (sheafTensor.{u,u,u,u,u} A) (wedgeProduct B D)
          (CochainComplex.brutal P k) (CochainComplex.ιBrutal P k ≫ ι)).f m) =
      imageSubobject (HomologicalComplex.ιMapBifunctor (CochainComplex.brutal P k)
          (deRhamComplex B D) (sheafTensor.{u,u,u,u,u} A) (ComplexShape.up ℕ) k (m - k) m
            (piNat_add_sub_mem k m hk) ≫
        (CochainComplex.wedgeAlong (sheafTensor.{u,u,u,u,u} A) (wedgeProduct B D)
          (CochainComplex.brutal P k) (CochainComplex.ιBrutal P k ≫ ι)).f m) :=
  imageSubobject_wedgeAlongBrutal_eq_of_le B D P ι k m hk fun ij hik =>
    ((imageSubobject_ιMapBifunctor_wedgeAlongBrutal_eq_of_le B D P ι k ij.1.1 ij.1.2 m hik
        ij.2).trans_le (hdom ij.1.1 ij.1.2 hik ij.2)).trans_eq
      (imageSubobject_ιMapBifunctor_wedgeAlongBrutal_eq_of_le B D P ι k k (m - k) m le_rfl
        (show k + (m - k) = m by omega)).symm

end AlgebraicGeometry.SheafOfModules

end
