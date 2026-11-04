module

public import StacksFrontier.Homology.DerivedTensor.KFlatDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.KFlatComplexesDefinition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.KFlatResolutionInstances
public import StacksFrontier.Homology.KFlat.BifunctorLocalization
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Shift.CommShiftTwo
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product on a ringed site

Let `(C, O)` be a ringed site and `Mod(O)` the category of sheaves of `O`-modules. For a cochain
complex `G` of `O`-modules, the functor `K ↦ Tot(K ⊗_O G)` on the homotopy category `K(O)` is an
exact functor of triangulated categories. When `G` is **K-flat** it sends quasi-isomorphisms to
quasi-isomorphisms, so it descends to an exact functor `- ⊗_O^{L} G : D(O) ⥤ D(O)` on the derived
category, the derived tensor product with `G`. Here the tensor product of sheaves of modules is
the sheafification of `U ↦ F(U) ⊗_{O(U)} G(U)`.

The file also records the derived tensor product of sheaves of modules on a ringed site as a
bifunctor on the unbounded derived category, together with the comparisons that identify it with
the total tensor product on K-flat complexes.

## Main definitions

* `Stacks.DerivedTensor.SheafMod R`: the category `Mod(O)` of sheaves of `O`-modules.
* `Stacks.DerivedTensor.KFlat R G`: K-flatness of a complex of `O`-modules: `Tot(K ⊗_O G)` is
  acyclic for every acyclic complex `K` of `O`-modules.
* `Stacks.DerivedTensor.derivedTensorSheaf R G`: the functor `- ⊗_O^{L} G : D(O) ⥤ D(O)` for a
  K-flat `G`.
* `Stacks.DerivedTensor.derivedTensorSheafQIso R G`: the identification of `- ⊗_O^{L} G` with the
  total tensor complex `Tot(- ⊗_O G)`, naturally in the complex.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`: a bifunctor on `D(Mod(O))` with its
  two-sided and one-sided K-flat comparisons with the total tensor product, its canonical map to
  that total tensor product for arbitrary complexes, and exactness in each variable.

## Main results

* `Stacks.DerivedTensor.kFlat_iff`: K-flatness unfolded against the total tensor complex.
* `Stacks.DerivedTensor.derivedTensorSheafUniq`: `- ⊗_O^{L} G` is determined up to canonical
  isomorphism by its identification with `Tot(- ⊗_O G)`.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.toTensor_eq_of_resolutions`: the canonical
  map to the total tensor product is computed by any pair of K-flat resolutions.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparisonRight_eq_of_resolution` and
  `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparisonLeft_eq_of_resolution`: each
  one-sided comparison is determined by one K-flat resolution and the two-sided comparison.
* `Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso`: every complex of `O`-modules receives
  a quasi-isomorphism from a K-flat complex.
* `Stacks.DerivedTensor.RingedSite.kFlatQ_isLocalization`: `D(Mod(O))` is the localization of the
  K-flat complexes of `O`-modules at the quasi-isomorphisms.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN)
* [Stacks Project, Tag 06YP](https://stacks.math.columbia.edu/tag/06YP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe d w v u

/-! ### The one-variable derived tensor product `- ⊗_O^{L} G` with a K-flat complex -/

namespace Stacks.DerivedTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v w})
  [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-- `Mod(O)`, the category of sheaves of `O`-modules on the ringed site `(C, O)`, where the sheaf
of commutative rings `O = R` is regarded as a sheaf of rings by
`Stacks.SheafOfModules.Tensor.ringSheaf`. -/
abbrev SheafMod := SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R)

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, max u v w, max u v w} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, max u v w, max u v w} R).obj
    M).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafMod R) (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, max u v w, max u v w} R)
        (ComplexShape.up ℤ)]

/-- A cochain complex `G` of `O`-modules is **K-flat** when `Tot(K ⊗_O G)` is acyclic for every
acyclic cochain complex `K` of `O`-modules. This is `Stacks.DerivedTensor.IsKFlat` at the tensor
product of sheaves of modules. -/
abbrev KFlat (G : CochainComplex (SheafMod R) ℤ) : Prop :=
  IsKFlat (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, max u v w, max u v w} R) G

/-- K-flatness unfolded against the total tensor complex `Tot(- ⊗_O -)`. -/
theorem kFlat_iff (G : CochainComplex (SheafMod R) ℤ) :
    KFlat R G ↔ ∀ K : CochainComplex (SheafMod R) ℤ, K.Acyclic →
      (((Stacks.SheafOfModules.Tensor.tensorComplex R).obj K).obj G).Acyclic :=
  ⟨fun h => h.acyclic_totRight, fun h => ⟨h⟩⟩

/-- A zero complex of `O`-modules is K-flat. -/
theorem kFlat_of_isZero {G : CochainComplex (SheafMod R) ℤ} (hG : IsZero G) : KFlat R G :=
  isKFlat_of_isZero
    (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, max u v w, max u v w} R) G hG

variable [HasDerivedCategory.{d} (SheafMod R)] (G : CochainComplex (SheafMod R) ℤ) [KFlat R G]

/-- The derived tensor product `- ⊗_O^{L} G : D(O) ⥤ D(O)` with a K-flat complex `G` of
`O`-modules: the functor induced on derived categories by the total tensor complex
`Tot(- ⊗_O G)`. -/
@[stacks 06YU "the derived tensor product with a K-flat complex",
  sga "4½ Etat_0 6.2" "⊗^L via K-flat"]
abbrev derivedTensorSheaf : DerivedCategory (SheafMod R) ⥤ DerivedCategory (SheafMod R) :=
  derivedTensor (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, max u v w, max u v w} R) G

/-- `- ⊗_O^{L} G` is the functor described by the total tensor complex: on the image of a
complex `K` of `O`-modules in `D(O)` it is `Tot(K ⊗_O G)`, naturally in `K`. -/
@[stacks 06YU "computed by the total tensor complex"]
abbrev derivedTensorSheafQIso :
    DerivedCategory.Q ⋙ derivedTensorSheaf R G ≅
      totRight (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, max u v w, max u v w} R) G ⋙
        DerivedCategory.Q :=
  derivedTensorQIso (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, max u v w, max u v w} R) G

/-- The derived tensor product is unique: any functor on `D(O)` lifting `Tot(- ⊗_O G)` through
the localisation is canonically isomorphic to `- ⊗_O^{L} G`. -/
def derivedTensorSheafUniq (L : DerivedCategory (SheafMod R) ⥤ DerivedCategory (SheafMod R))
    [Localization.Lifting DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafMod R) (ComplexShape.up ℤ))
      (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, max u v w, max u v w} R) G ⋙
        DerivedCategory.Qh) L] :
    L ≅ derivedTensorSheaf R G :=
  derivedTensorUniq (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, max u v w, max u v w} R) G L

end Stacks.DerivedTensor

/-! ### The derived tensor product as a bifunctor on `D(Mod(O))` -/

namespace Stacks.DerivedTensor.RingedSite

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The category of sheaves of modules over the structure sheaf. -/
abbrev Modules := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)

variable [HasDerivedCategory.{d} (Modules R)]

/-- The unbounded derived category of sheaves of modules. -/
abbrev DerivedModules := DerivedCategory (Modules R)

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctorReg K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R) (ComplexShape.up ℤ)]

/-- Data characterizing the derived tensor product. -/
structure DerivedTensorProduct where
  /-- The derived tensor bifunctor. -/
  tensor : DerivedModules R ⥤ DerivedModules R ⥤ DerivedModules R
  /-- K-flat representatives compute the derived tensor product. -/
  comparison (K L : CochainComplex (Modules R) ℤ)
      (hK : Stacks.SheafOfModules.KFlat.KFlat R K) (hL : Stacks.SheafOfModules.KFlat.KFlat R L) :
    (tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj ((Stacks.SheafOfModules.Tensor.tensorComplex R).obj K |>.obj L)
  /-- The K-flat comparison is natural in both complexes. -/
  comparison_naturality
      {K K' L L' : CochainComplex (Modules R) ℤ}
      (f : K ⟶ K') (g : L ⟶ L')
      (hK : Stacks.SheafOfModules.KFlat.KFlat R K) (hK' : Stacks.SheafOfModules.KFlat.KFlat R K')
      (hL : Stacks.SheafOfModules.KFlat.KFlat R L) (hL' : Stacks.SheafOfModules.KFlat.KFlat R L') :
    (tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        (tensor.obj (DerivedCategory.Q.obj K')).map (DerivedCategory.Q.map g) ≫
        (comparison K' L' hK' hL').hom =
      (comparison K L hK hL).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg f g
            (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R) (ComplexShape.up ℤ))
  /-- A K-flat right factor computes the tensor product with any left complex. -/
  comparisonRight (K L : CochainComplex (Modules R) ℤ)
      (hL : Stacks.SheafOfModules.KFlat.KFlat R L) :
    (tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj ((Stacks.SheafOfModules.Tensor.tensorComplex R).obj K |>.obj L)
  /-- The right K-flat comparison is natural without flatness on the left. -/
  comparisonRight_naturality
      {K K' L L' : CochainComplex (Modules R) ℤ}
      (f : K ⟶ K') (g : L ⟶ L')
      (hL : Stacks.SheafOfModules.KFlat.KFlat R L) (hL' : Stacks.SheafOfModules.KFlat.KFlat R L') :
    (tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        (tensor.obj (DerivedCategory.Q.obj K')).map (DerivedCategory.Q.map g) ≫
        (comparisonRight K' L' hL').hom =
      (comparisonRight K L hL).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg f g
            (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R) (ComplexShape.up ℤ))
  /-- On two K-flat complexes the right comparison is the existing comparison. -/
  comparisonRight_eq_comparison
      (K L : CochainComplex (Modules R) ℤ)
      (hK : Stacks.SheafOfModules.KFlat.KFlat R K) (hL : Stacks.SheafOfModules.KFlat.KFlat R L) :
    comparisonRight K L hL = comparison K L hK hL
  /-- A K-flat left factor computes the tensor product with any right complex. -/
  comparisonLeft (K L : CochainComplex (Modules R) ℤ)
      (hK : Stacks.SheafOfModules.KFlat.KFlat R K) :
    (tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj ((Stacks.SheafOfModules.Tensor.tensorComplex R).obj K |>.obj L)
  /-- The left K-flat comparison is natural without flatness on the right. -/
  comparisonLeft_naturality
      {K K' L L' : CochainComplex (Modules R) ℤ}
      (f : K ⟶ K') (g : L ⟶ L')
      (hK : Stacks.SheafOfModules.KFlat.KFlat R K) (hK' : Stacks.SheafOfModules.KFlat.KFlat R K') :
    (tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        (tensor.obj (DerivedCategory.Q.obj K')).map (DerivedCategory.Q.map g) ≫
        (comparisonLeft K' L' hK').hom =
      (comparisonLeft K L hK).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg f g
            (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R) (ComplexShape.up ℤ))
  /-- On two K-flat complexes the left comparison is the existing comparison. -/
  comparisonLeft_eq_comparison
      (K L : CochainComplex (Modules R) ℤ)
      (hK : Stacks.SheafOfModules.KFlat.KFlat R K) (hL : Stacks.SheafOfModules.KFlat.KFlat R L) :
    comparisonLeft K L hK = comparison K L hK hL
  /-- The canonical map from derived tensor to ordinary total tensor. -/
  toTensor (K L : CochainComplex (Modules R) ℤ) :
    (tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj ((Stacks.SheafOfModules.Tensor.tensorComplex R).obj K |>.obj L)
  /-- The derived-to-ordinary comparison is natural in both complexes. -/
  toTensor_naturality
      {K K' L L' : CochainComplex (Modules R) ℤ}
      (f : K ⟶ K') (g : L ⟶ L') :
    (tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        (tensor.obj (DerivedCategory.Q.obj K')).map (DerivedCategory.Q.map g) ≫
        toTensor K' L' =
      toTensor K L ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg f g
            (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R) (ComplexShape.up ℤ))
  /-- If the right factor is K-flat, the canonical map is the right comparison. -/
  toTensor_eq_comparisonRight
      (K L : CochainComplex (Modules R) ℤ)
      (hL : Stacks.SheafOfModules.KFlat.KFlat R L) :
    toTensor K L = (comparisonRight K L hL).hom
  /-- If the left factor is K-flat, the canonical map is the left comparison. -/
  toTensor_eq_comparisonLeft
      (K L : CochainComplex (Modules R) ℤ)
      (hK : Stacks.SheafOfModules.KFlat.KFlat R K) :
    toTensor K L = (comparisonLeft K L hK).hom
  /-- The derived tensor product commutes with the shifts in both variables, with Mathlib's
  sign `(-1) ^ (p * q)`: fixing either argument gives a shift-compatible functor, those
  commutation isomorphisms are natural in the other argument, and the two of them commute with
  each other up to that sign. -/
  commShift₂ : tensor.CommShift₂Int
  /-- Tensoring in the left variable is exact. -/
  exact_left : ∀ L, letI := commShift₂.commShiftFlipObj L;
    (tensor.flip.obj L).IsTriangulated
  /-- Tensoring in the right variable is exact. -/
  exact_right : ∀ K, letI := commShift₂.commShiftObj K; (tensor.obj K).IsTriangulated

namespace DerivedTensorProduct

variable {R}

variable (T : DerivedTensorProduct R)

/-- Fixing the right argument gives a shift-compatible functor: the `commShiftFlipObj` half of
the two-variable coherence `commShift₂`. -/
abbrev commShift_left (L : DerivedModules R) : (T.tensor.flip.obj L).CommShift ℤ :=
  T.commShift₂.commShiftFlipObj L

/-- Fixing the left argument gives a shift-compatible functor: the `commShiftObj` half of the
two-variable coherence `commShift₂`. -/
abbrev commShift_right (K : DerivedModules R) : (T.tensor.obj K).CommShift ℤ :=
  T.commShift₂.commShiftObj K

end DerivedTensorProduct

attribute [instance] DerivedTensorProduct.commShift₂ DerivedTensorProduct.exact_left
  DerivedTensorProduct.exact_right

namespace DerivedTensorProduct

variable {R}

variable (T : DerivedTensorProduct R)

/-- On two K-flat complexes the canonical map is the two-sided comparison. -/
theorem toTensor_eq_comparison
    (K L : CochainComplex (Modules R) ℤ)
    (hK : Stacks.SheafOfModules.KFlat.KFlat R K) (hL : Stacks.SheafOfModules.KFlat.KFlat R L) :
    T.toTensor K L = (T.comparison K L hK hL).hom := by
  rw [T.toTensor_eq_comparisonRight K L hL,
    T.comparisonRight_eq_comparison K L hK hL]

/-- The canonical comparison intertwines augmentations with the ordinary total tensor of
those augmentations. -/
theorem toTensor_comp_augmentations
    {P Q K L : CochainComplex (Modules R) ℤ}
    (p : P ⟶ K) (q : Q ⟶ L)
    (hP : Stacks.SheafOfModules.KFlat.KFlat R P) (hQ : Stacks.SheafOfModules.KFlat.KFlat R Q) :
    (T.tensor.map (DerivedCategory.Q.map p)).app (DerivedCategory.Q.obj Q) ≫
        (T.tensor.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map q) ≫
        T.toTensor K L =
      (T.comparison P Q hP hQ).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg p q
            (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R) (ComplexShape.up ℤ)) := by
  rw [T.toTensor_naturality p q, T.toTensor_eq_comparison P Q hP hQ]

/-- Any pair of K-flat resolutions computes the canonical derived-to-ordinary map. -/
theorem toTensor_eq_of_resolutions
    {P Q K L : CochainComplex (Modules R) ℤ}
    (p : P ⟶ K) (q : Q ⟶ L) [QuasiIso p] [QuasiIso q]
    (hP : Stacks.SheafOfModules.KFlat.KFlat R P) (hQ : Stacks.SheafOfModules.KFlat.KFlat R Q) :
    T.toTensor K L =
      inv ((T.tensor.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map q)) ≫
        inv ((T.tensor.map (DerivedCategory.Q.map p)).app (DerivedCategory.Q.obj Q)) ≫
        (T.comparison P Q hP hQ).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg p q
            (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R) (ComplexShape.up ℤ)) :=
  (IsIso.eq_inv_comp _).2
    ((IsIso.eq_inv_comp _).2 (T.toTensor_comp_augmentations p q hP hQ))

/-- The right K-flat comparison agrees with the two-sided comparison along an augmentation
of the arbitrary left complex. -/
theorem comparisonRight_comp_augmentation
    {P K L : CochainComplex (Modules R) ℤ}
    (p : P ⟶ K) (hP : Stacks.SheafOfModules.KFlat.KFlat R P)
    (hL : Stacks.SheafOfModules.KFlat.KFlat R L) :
    (T.tensor.map (DerivedCategory.Q.map p)).app (DerivedCategory.Q.obj L) ≫
        (T.comparisonRight K L hL).hom =
      (T.comparison P L hP hL).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg p (𝟙 L)
            (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R) (ComplexShape.up ℤ)) := by
  simpa [T.toTensor_eq_comparisonRight K L hL] using
    T.toTensor_comp_augmentations p (𝟙 L) hP hL

/-- The left K-flat comparison agrees with the two-sided comparison along an augmentation
of the arbitrary right complex. -/
theorem comparisonLeft_comp_augmentation
    {K P L : CochainComplex (Modules R) ℤ}
    (p : P ⟶ L) (hK : Stacks.SheafOfModules.KFlat.KFlat R K)
    (hP : Stacks.SheafOfModules.KFlat.KFlat R P) :
    (T.tensor.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map p) ≫
        (T.comparisonLeft K L hK).hom =
      (T.comparison K P hK hP).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg (𝟙 K) p
            (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R) (ComplexShape.up ℤ)) := by
  simpa [T.toTensor_eq_comparisonLeft K L hK] using
    T.toTensor_comp_augmentations (𝟙 K) p hK hP

/-- A K-flat resolution of the left factor determines the right K-flat comparison,
including its normalization, from the two-sided comparison. -/
theorem comparisonRight_eq_of_resolution
    {P K L : CochainComplex (Modules R) ℤ}
    (p : P ⟶ K) [QuasiIso p]
    (hP : Stacks.SheafOfModules.KFlat.KFlat R P) (hL : Stacks.SheafOfModules.KFlat.KFlat R L) :
    (T.comparisonRight K L hL).hom =
      inv ((T.tensor.map (DerivedCategory.Q.map p)).app (DerivedCategory.Q.obj L)) ≫
        (T.comparison P L hP hL).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg p (𝟙 L)
            (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R) (ComplexShape.up ℤ)) :=
  (IsIso.eq_inv_comp _).2 (T.comparisonRight_comp_augmentation p hP hL)

/-- A K-flat resolution of the right factor determines the left K-flat comparison from the
two-sided comparison and the augmentation. -/
theorem comparisonLeft_eq_of_resolution
    {K P L : CochainComplex (Modules R) ℤ}
    (p : P ⟶ L) [QuasiIso p]
    (hK : Stacks.SheafOfModules.KFlat.KFlat R K) (hP : Stacks.SheafOfModules.KFlat.KFlat R P) :
    (T.comparisonLeft K L hK).hom =
      inv ((T.tensor.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map p)) ≫
        (T.comparison K P hK hP).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg (𝟙 K) p
            (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R) (ComplexShape.up ℤ)) :=
  (IsIso.eq_inv_comp _).2 (T.comparisonLeft_comp_augmentation p hK hP)

end DerivedTensorProduct

/-! ### The K-flat complexes of `O`-modules localize to `D(Mod(O))` -/

omit [HasDerivedCategory.{d} (Modules R)] in
/-- Every complex of `O`-modules receives a quasi-isomorphism from a K-flat complex. -/
theorem exists_kFlat_quasiIso
    (G : CochainComplex (Modules R) ℤ) :
    ∃ (P : CochainComplex (Modules R) ℤ) (f : P ⟶ G),
      CochainComplex.KFlatBifunctor.KFlat
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R) P ∧ QuasiIso f := by
  obtain ⟨P, f, hP, _, hf, _⟩ := Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution R G
  exact ⟨P, f, hP, hf⟩

/-- `D(Mod(O))` is the localization of the K-flat complexes of `O`-modules at the
quasi-isomorphisms. -/
theorem kFlatQ_isLocalization :
    (CochainComplex.KFlatBifunctor.kFlatQ
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R)).IsLocalization
      (CochainComplex.KFlatBifunctor.kFlatQuasiIso
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R)) :=
  inferInstance

end Stacks.DerivedTensor.RingedSite

end
