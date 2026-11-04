module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Shift.CommShiftTwo
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product on a ringed site: the interface

Let `(C, O)` be a ringed site. The derived tensor product is a bifunctor on the derived
category `D(O)` of sheaves of `O`-modules which is exact in each variable and which, on
K-flat representatives, is computed by the ordinary total tensor product. This file states
what that data is, as the structure `Stacks.SheafOfModules.DerivedTensorProduct`, and derives
the consequences of the structure's fields; the construction of an element of it is Stacks
06YU and lives elsewhere, so that a client needing only the bifunctor and its comparisons
does not import the existence proof.

## Main definitions

* `AlgebraicGeometry.RingedSite.Modules`: the sheaves of modules on a ringed site.
* `AlgebraicGeometry.RingedSite.DerivedModules`: their unbounded derived category.
* `Stacks.SheafOfModules.DerivedTensorProduct`: a derived tensor bifunctor on
  `D(O)`, packaged with its two one-sided K-flat comparison isomorphisms, its canonical
  map to the ordinary total tensor product, the naturality of all three, and exactness in
  each variable.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.toTensor_eq_comparison`: on two K-flat
  complexes the canonical map is the two-sided comparison.
* `Stacks.SheafOfModules.DerivedTensorProduct.toTensor_eq_of_resolutions`: any pair of
  K-flat resolutions computes the canonical map, so naturality together with the K-flat
  normalisation determines its value; it is not an uncharacterised choice of a morphism.
* `Stacks.SheafOfModules.DerivedTensorProduct.comparisonRight_eq_of_resolution` and
  `comparisonLeft_eq_of_resolution`: likewise for the two one-sided comparisons.
* `Stacks.SheafOfModules.DerivedTensorProduct.unitIso`: the structure sheaf in degree zero is a
  unit, `E ⊗^L_O O[0] ≅ E`.

## Implementation notes

The source states, for each fixed object of `D(O)`, an exact functor of triangulated
categories; the structure states all of those at once, as a bifunctor. The construction
preceding Tag 06YU tensors an arbitrary complex with a K-flat resolution of the fixed right
factor, so the right K-flat comparison `comparisonRight` does not assume that the left factor
is K-flat; the symmetric construction gives `comparisonLeft`. Both agree with the two-sided
comparison when both factors are K-flat, and naturality then fixes their values along
resolution augmentations. The map `toTensor` is natural for arbitrary maps of complexes and
agrees with these comparisons as soon as either factor is K-flat;
`toTensor_eq_of_resolutions` characterises it using any pair of K-flat resolution
augmentations, as in the proof of Tag 0FPH. These comparisons with the total tensor product
are what identify the bifunctor as the *derived* tensor product rather than an arbitrary
exact bifunctor.

The ordinary tensor product is `Stacks.SheafOfModules.Tensor.sheafTensor`, the sheafification of
the sectionwise tensor product, and its total complex with the Koszul-sign differential is
`Stacks.SheafOfModules.Tensor.tensorComplex`; K-flatness is `Stacks.SheafOfModules.IsKFlat`. The
  typeclass
arguments are the sheafification and totalisation infrastructure those use. The site
universes `u` and `v` and the universe `d` of the localisation are independent; the sections
of the structure sheaf and of the modules live in a further independent universe `w`, which
is the generality in which `Stacks.SheafOfModules.Tensor.sheafTensor` is available.

The unit law `unitIso` is a *theorem about* the structure and not a field of it, so that the
producers of a `DerivedTensorProduct` owe nothing extra: `comparisonRight` asks flatness of the
right factor only, and the structure sheaf in degree zero is K-flat
(`Stacks.SheafOfModules.isKFlat_single_unit`), so the unit law for the ordinary tensor product
transports to the derived one along the essential surjectivity of `DerivedCategory.Q`. The
sections universe `w` is free there too: the ordinary unit law it reads off is
`Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections`, which goes through the right unitor of
*presheaves* of modules and the sheafification counit rather than through the monoidal structure
on `Mod(O)`, the latter being the only thing in sight that needs `w = max u v`.

**The other structure of this shape.**
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.OnARingedSite` has the same
sixteen fields in the same order, at a *small* site with all four universes tied to one `u`
and with K-flatness spelled `Stacks.SheafOfModules.KFlat.KFlat` rather than
`Stacks.SheafOfModules.IsKFlat`. The structure here is the more general statement; the other is
not a redundant copy of it, because the narrowing there is what makes K-flat resolutions exist
(`Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution`, which needs the ring universe
pinned to the site's hom universe) and hence what makes an element of that structure
constructible at all. The two are distinct Lean types parameterised differently — a bundled
`RingedSite` here, a bare sheaf of commutative rings there — so collapsing them rewrites the
statement of every declaration mentioning either, over a hundred modules for this one and about
thirty for the other. Recorded, not merged.

The `HasMapBifunctor` hypothesis and the total complexes of maps in the fields are spelled with
`HomologicalComplex.HasMapBifunctorReg` and `HomologicalComplex.mapBifunctorMapReg`, the copies
of Mathlib's `abbrev`s with regular kernel reducibility hints, as `tensorComplex` and
`Stacks.SheafOfModules.IsKFlat` are. The kernel then compares the differently spelled total
complexes in the field types argument by argument instead of evaluating `sheafTensor`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace AlgebraicGeometry.RingedSite

/-- The category of sheaves of modules over the structure sheaf of a ringed site. -/
abbrev Modules (X : RingedSite.{u, v, w}) :=
  SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)

/-- The unbounded derived category of sheaves of modules on a ringed site. -/
abbrev DerivedModules (X : RingedSite.{u, v, w})
    [HasSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasDerivedCategory.{d} (Modules.{u, v, w} X)] :=
  DerivedCategory (Modules.{u, v, w} X)

end AlgebraicGeometry.RingedSite

namespace Stacks.SheafOfModules

open AlgebraicGeometry.RingedSite

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (Modules.{u, v, w} X)]
variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctorReg K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

-- The four naturality fields are the whole elaboration cost of this structure (the
-- `commShift`/`exact` block is negligible): each forces the type of
-- `Q.map (mapBifunctorMapReg f g (sheafTensor X.O) _)` to be unified with the codomain of
-- `toTensor`, i.e. `mapBifunctorReg K L (sheafTensor X.O) _` with
-- `((tensorComplex X.O).obj K).obj L`, which descends through `sheafTensor` into
-- `SheafOfModules.forget` and the sectionwise tensor product. Keeping `sheafTensor`
-- opaque does not help: it makes the unification fail outright rather than cost less, so
-- the unfolding is needed. The declaration elaborates under the default budget of 200,000
-- heartbeats; `#count_heartbeats` reports a larger serial total because it disables
-- asynchronous elaboration, whereas the build elaborates several independently budgeted tasks.
/-- Data characterizing the derived tensor product: if either representative
is K-flat its value is the total tensor product, naturally in both arguments,
compatibly with the canonical natural map to the total tensor product for
arbitrary representatives, and each partial functor is exact. -/
structure DerivedTensorProduct where
  /-- The derived tensor bifunctor. -/
  tensor : DerivedModules.{u, v, w, d} X ⥤ DerivedModules.{u, v, w, d} X ⥤
    DerivedModules.{u, v, w, d} X
  /-- K-flat representatives compute the derived tensor product. -/
  comparison (K L : CochainComplex (Modules.{u, v, w} X) ℤ)
      (hK : IsKFlat X.O K) (hL : IsKFlat X.O L) :
    (tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K |>.obj L)
  /-- The K-flat comparison is natural in both complexes. -/
  comparison_naturality
      {K K' L L' : CochainComplex (Modules.{u, v, w} X) ℤ}
      (f : K ⟶ K') (g : L ⟶ L')
      (hK : IsKFlat X.O K) (hK' : IsKFlat X.O K')
      (hL : IsKFlat X.O L) (hL' : IsKFlat X.O L') :
    (tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        (tensor.obj (DerivedCategory.Q.obj K')).map (DerivedCategory.Q.map g) ≫
        (comparison K' L' hK' hL').hom =
      (comparison K L hK hL).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg f g
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))
  /-- A K-flat right factor computes the tensor product with any left complex. -/
  comparisonRight (K L : CochainComplex (Modules.{u, v, w} X) ℤ)
      (hL : IsKFlat X.O L) :
    (tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K |>.obj L)
  /-- The right K-flat comparison is natural without flatness on the left. -/
  comparisonRight_naturality
      {K K' L L' : CochainComplex (Modules.{u, v, w} X) ℤ}
      (f : K ⟶ K') (g : L ⟶ L')
      (hL : IsKFlat X.O L) (hL' : IsKFlat X.O L') :
    (tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        (tensor.obj (DerivedCategory.Q.obj K')).map (DerivedCategory.Q.map g) ≫
        (comparisonRight K' L' hL').hom =
      (comparisonRight K L hL).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg f g
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))
  /-- On two K-flat complexes the right comparison is the existing comparison. -/
  comparisonRight_eq_comparison
      (K L : CochainComplex (Modules.{u, v, w} X) ℤ)
      (hK : IsKFlat X.O K) (hL : IsKFlat X.O L) :
    comparisonRight K L hL = comparison K L hK hL
  /-- A K-flat left factor computes the tensor product with any right complex. -/
  comparisonLeft (K L : CochainComplex (Modules.{u, v, w} X) ℤ)
      (hK : IsKFlat X.O K) :
    (tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K |>.obj L)
  /-- The left K-flat comparison is natural without flatness on the right. -/
  comparisonLeft_naturality
      {K K' L L' : CochainComplex (Modules.{u, v, w} X) ℤ}
      (f : K ⟶ K') (g : L ⟶ L')
      (hK : IsKFlat X.O K) (hK' : IsKFlat X.O K') :
    (tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        (tensor.obj (DerivedCategory.Q.obj K')).map (DerivedCategory.Q.map g) ≫
        (comparisonLeft K' L' hK').hom =
      (comparisonLeft K L hK).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg f g
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))
  /-- On two K-flat complexes the left comparison is the existing comparison. -/
  comparisonLeft_eq_comparison
      (K L : CochainComplex (Modules.{u, v, w} X) ℤ)
      (hK : IsKFlat X.O K) (hL : IsKFlat X.O L) :
    comparisonLeft K L hK = comparison K L hK hL
  /-- The canonical map from derived tensor to ordinary total tensor, for
  arbitrary complexes. It is induced by K-flat resolution augmentations. -/
  toTensor (K L : CochainComplex (Modules.{u, v, w} X) ℤ) :
    (tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K |>.obj L)
  /-- The derived-to-ordinary comparison is natural in both complexes,
  without a K-flatness hypothesis. -/
  toTensor_naturality
      {K K' L L' : CochainComplex (Modules.{u, v, w} X) ℤ}
      (f : K ⟶ K') (g : L ⟶ L') :
    (tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        (tensor.obj (DerivedCategory.Q.obj K')).map (DerivedCategory.Q.map g) ≫
        toTensor K' L' =
      toTensor K L ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg f g
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))
  /-- If the right factor is K-flat, the canonical map is the right K-flat
  comparison isomorphism. -/
  toTensor_eq_comparisonRight
      (K L : CochainComplex (Modules.{u, v, w} X) ℤ)
      (hL : IsKFlat X.O L) :
    toTensor K L = (comparisonRight K L hL).hom
  /-- If the left factor is K-flat, the canonical map is the left K-flat
  comparison isomorphism. -/
  toTensor_eq_comparisonLeft
      (K L : CochainComplex (Modules.{u, v, w} X) ℤ)
      (hK : IsKFlat X.O K) :
    toTensor K L = (comparisonLeft K L hK).hom
  /-- **The derived tensor product commutes with the shifts in both variables**, with Mathlib's
  sign `(-1) ^ (p * q)`: fixing either argument gives a shift-compatible functor, those
  commutation isomorphisms are natural in the other argument, and the two of them commute with
  each other up to that sign.

  Carrying the two-variable coherence here, rather than the two one-variable structures
  separately, is what makes the sign coherence available at all. Fixing the two variables
  independently determines no relation between the resulting commutation isomorphisms, so an
  interface recording only those two cannot state — let alone prove — the equation relating
  them. -/
  commShift₂ : tensor.CommShift₂Int
  /-- Tensoring in the left variable is exact. -/
  exact_left : ∀ L, letI := commShift₂.commShiftFlipObj L;
    (tensor.flip.obj L).IsTriangulated
  /-- Tensoring in the right variable is exact. -/
  exact_right : ∀ K, letI := commShift₂.commShiftObj K; (tensor.obj K).IsTriangulated

namespace DerivedTensorProduct

variable {X}

variable (T : DerivedTensorProduct.{u, v, w, d} X)

/-- **Fixing the right argument gives a shift-compatible functor.** This is the
`commShiftFlipObj` half of the two-variable coherence `commShift₂`.

This was a field of its own until the two-variable coherence replaced it, and it keeps that
field's name and type exactly, so that consumers are unaffected. It is an `abbrev` on purpose:
the projection is then definitionally transparent, which is what lets the `exact_left` field
above — whose type is now spelled through `commShift₂` — continue to be used at this spelling.
It is not registered as an instance: Mathlib's `CategoryTheory.Functor.CommShift₂.commShiftFlipObj`
instance already produces it from `commShift₂`. -/
abbrev commShift_left (L : DerivedModules.{u, v, w, d} X) :
    (T.tensor.flip.obj L).CommShift ℤ :=
  T.commShift₂.commShiftFlipObj L

/-- **Fixing the left argument gives a shift-compatible functor.** This is the `commShiftObj`
half of the two-variable coherence `commShift₂`, and the mirror of `commShift_left`. -/
abbrev commShift_right (K : DerivedModules.{u, v, w, d} X) :
    (T.tensor.obj K).CommShift ℤ :=
  T.commShift₂.commShiftObj K

end DerivedTensorProduct

attribute [instance] DerivedTensorProduct.commShift₂ DerivedTensorProduct.exact_left
  DerivedTensorProduct.exact_right

namespace DerivedTensorProduct

variable {X} (T : DerivedTensorProduct.{u, v, w, d} X)

/-- On two K-flat complexes the canonical map is the two-sided comparison. -/
theorem toTensor_eq_comparison
    (K L : CochainComplex (Modules.{u, v, w} X) ℤ)
    (hK : IsKFlat X.O K) (hL : IsKFlat X.O L) :
    T.toTensor K L = (T.comparison K L hK hL).hom := by
  rw [T.toTensor_eq_comparisonRight K L hL,
    T.comparisonRight_eq_comparison K L hK hL]

/-- The canonical comparison intertwines augmentations with the ordinary
total tensor of those augmentations. -/
theorem toTensor_comp_augmentations
    {P Q K L : CochainComplex (Modules.{u, v, w} X) ℤ}
    (p : P ⟶ K) (q : Q ⟶ L)
    (hP : IsKFlat X.O P) (hQ : IsKFlat X.O Q) :
    (T.tensor.map (DerivedCategory.Q.map p)).app (DerivedCategory.Q.obj Q) ≫
        (T.tensor.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map q) ≫
        T.toTensor K L =
      (T.comparison P Q hP hQ).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg p q
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) := by
  rw [T.toTensor_naturality p q, T.toTensor_eq_comparison P Q hP hQ]

/-- Any pair of K-flat resolutions computes the canonical derived-to-ordinary
map. Thus naturality and the K-flat normalization determine its value. -/
theorem toTensor_eq_of_resolutions
    {P Q K L : CochainComplex (Modules.{u, v, w} X) ℤ}
    (p : P ⟶ K) (q : Q ⟶ L) [QuasiIso p] [QuasiIso q]
    (hP : IsKFlat X.O P) (hQ : IsKFlat X.O Q) :
    T.toTensor K L =
      inv ((T.tensor.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map q)) ≫
        inv ((T.tensor.map (DerivedCategory.Q.map p)).app (DerivedCategory.Q.obj Q)) ≫
        (T.comparison P Q hP hQ).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg p q
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) :=
  (IsIso.eq_inv_comp _).2 ((IsIso.eq_inv_comp _).2 (T.toTensor_comp_augmentations p q hP hQ))

/-- The right K-flat comparison agrees with the two-sided comparison along
an augmentation of the arbitrary left complex. In particular this applies
to every K-flat resolution of that complex. -/
theorem comparisonRight_comp_augmentation
    {P K L : CochainComplex (Modules.{u, v, w} X) ℤ}
    (p : P ⟶ K) (hP : IsKFlat X.O P) (hL : IsKFlat X.O L) :
    (T.tensor.map (DerivedCategory.Q.map p)).app (DerivedCategory.Q.obj L) ≫
        (T.comparisonRight K L hL).hom =
      (T.comparison P L hP hL).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg p (𝟙 L)
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) := by
  simpa only [(DerivedCategory.Q (C := Modules.{u, v, w} X)).map_id L,
    (T.tensor.obj (DerivedCategory.Q.obj K)).map_id (DerivedCategory.Q.obj L),
    Category.id_comp,
    T.comparisonRight_eq_comparison P L hP hL] using
    T.comparisonRight_naturality p (𝟙 L) hL hL

/-- The left K-flat comparison agrees with the two-sided comparison along
an augmentation of the arbitrary right complex. -/
theorem comparisonLeft_comp_augmentation
    {K P L : CochainComplex (Modules.{u, v, w} X) ℤ}
    (p : P ⟶ L) (hK : IsKFlat X.O K) (hP : IsKFlat X.O P) :
    (T.tensor.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map p) ≫
        (T.comparisonLeft K L hK).hom =
      (T.comparison K P hK hP).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg (𝟙 K) p
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) := by
  simpa only [(DerivedCategory.Q (C := Modules.{u, v, w} X)).map_id K,
    T.tensor.map_id (DerivedCategory.Q.obj K), NatTrans.id_app, Category.id_comp,
    T.comparisonLeft_eq_comparison K P hK hP] using
    T.comparisonLeft_naturality (𝟙 K) p hK hK

/-- A K-flat resolution of the left factor determines the right K-flat
comparison, including its normalization, from the two-sided comparison. -/
theorem comparisonRight_eq_of_resolution
    {P K L : CochainComplex (Modules.{u, v, w} X) ℤ}
    (p : P ⟶ K) [QuasiIso p]
    (hP : IsKFlat X.O P) (hL : IsKFlat X.O L) :
    (T.comparisonRight K L hL).hom =
      inv ((T.tensor.map (DerivedCategory.Q.map p)).app (DerivedCategory.Q.obj L)) ≫
        (T.comparison P L hP hL).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg p (𝟙 L)
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) :=
  (IsIso.eq_inv_comp _).2 (T.comparisonRight_comp_augmentation p hP hL)

/-- A K-flat resolution of the right factor determines the left K-flat
comparison from the two-sided comparison and the augmentation. -/
theorem comparisonLeft_eq_of_resolution
    {K P L : CochainComplex (Modules.{u, v, w} X) ℤ}
    (p : P ⟶ L) [QuasiIso p]
    (hK : IsKFlat X.O K) (hP : IsKFlat X.O P) :
    (T.comparisonLeft K L hK).hom =
      inv ((T.tensor.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map p)) ≫
        (T.comparison K P hK hP).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMapReg (𝟙 K) p
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) :=
  (IsIso.eq_inv_comp _).2 (T.comparisonLeft_comp_augmentation p hK hP)

section Unit

variable {Y : AlgebraicGeometry.RingedSite.{u, v, w}}
  [HasSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (Modules.{u, v, w} Y)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Y.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, v, w} Y) ℤ),
    HomologicalComplex.HasMapBifunctorReg K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **The structure sheaf in degree zero is a unit for the derived tensor product**:
`E ⊗^L_O O[0]` is `E`, for every object `E` of `D(O)`.

`DerivedTensorProduct` carries no unit datum, and needs none. Every object of `D(O)` is `Q K`
for some complex `K`, the localization functor being essentially surjective; the right K-flat
comparison `comparisonRight`, which asks flatness of the right factor only, then computes
`Q K ⊗^L_O O[0]` as `Q Tot(K ⊗_O O[0])`; and that is `Q K` by the ordinary unit law
`Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections`. -/
def unitIso (T : DerivedTensorProduct.{u, v, w, d} Y)
    (E : DerivedModules.{u, v, w, d} Y) :
    (T.tensor.obj E).obj
        ((DerivedCategory.singleFunctor (Modules.{u, v, w} Y) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≅ E :=
  let U := (HomologicalComplex.single (Modules.{u, v, w} Y) (ComplexShape.up ℤ) 0).obj
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  let K := DerivedCategory.Q.objPreimage E
  let eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  ((T.tensor.mapIso eK).app (DerivedCategory.Q.obj U)).symm ≪≫
    T.comparisonRight K U (Stacks.SheafOfModules.isKFlat_single_unit Y.O) ≪≫
    DerivedCategory.Q.mapIso
      (Stacks.SheafOfModules.tensorComplexUnitIsoFreeSections Y.O K) ≪≫ eK

end Unit

end DerivedTensorProduct

end Stacks.SheafOfModules

end
