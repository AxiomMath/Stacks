module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.AlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.FppfSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.SeparatedClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Open
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMapDomainOfDefinition
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable

/-!
# The finite part of a separated flat morphism locally of finite presentation

Let `f : X ⟶ Y` be a separated, flat morphism of algebraic spaces over a scheme `S` which is
locally of finite presentation. The projection `(X/Y)_fin ⟶ Y` from the finite part of `f` is
then separated, representable and étale, and when `Y` is a scheme so is `(X/Y)_fin`.

Separatedness is the substance. The relative diagonal of the projection is an open immersion by
Stacks 04PK, so by the criterion of Stacks 04CD the assertion is that the set of points where
two pairs `(a, Z₁)` and `(a, Z₂)` of Stacks 04PC agree is closed. The complement of that set is
the union of the images of `Z₁ ∖ Z₂` and `Z₂ ∖ Z₁` under the projection to the base, and each is
open: the subtracted subspace is closed by Stacks 04PH, and the projection is flat and locally
of finite presentation, hence open by Stacks 042S.

Étaleness is already Stacks 04QH, which asks only that `f` be separated and locally of finite
type. Representability of the projection then follows from Stacks 0418, since an étale morphism
is locally quasi-finite by Stacks 03XU; and representability of `(X/Y)_fin` itself over a
representable base is Stacks 03XX.

## Main results

* `AlgebraicGeometry.Space.isSeparated_baseMap_finiteOpenSubspacePresheaf` — Stacks 04RI,
  part (1): the projection `(X/Y)_fin ⟶ Y` is separated.
* `AlgebraicGeometry.Space.isEtale_baseMap_finiteOpenSubspacePresheaf_of_isFlat` — Stacks 04RI,
  part (1): that projection is étale.
* `AlgebraicGeometry.Space.relativelyRepresentable_baseMap_finiteOpenSubspacePresheaf` — Stacks
  04RI, part (1): that projection is representable.
* `AlgebraicGeometry.Space.isRepresentable_finiteOpenSubspacePresheaf_of_isRepresentable` —
  Stacks 04RI, part (2): if `Y` is a scheme then `(X/Y)_fin` is a scheme.

## References

* [Stacks Project, Tag 04RI](https://stacks.math.columbia.edu/tag/04RI)
* [Stacks Project, Tag 04QH](https://stacks.math.columbia.edu/tag/04QH)
* [Stacks Project, Tag 04PK](https://stacks.math.columbia.edu/tag/04PK)
* [Stacks Project, Tag 04PH](https://stacks.math.columbia.edu/tag/04PH)
* [Stacks Project, Tag 042S](https://stacks.math.columbia.edu/tag/042S)
* [Stacks Project, Tag 0418](https://stacks.math.columbia.edu/tag/0418)
* [Stacks Project, Tag 03XU](https://stacks.math.columbia.edu/tag/03XU)
* [Stacks Project, Tag 03XX](https://stacks.math.columbia.edu/tag/03XX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- The maps on points of the two sides of a commutative square agree. -/
private theorem pointsMap_comm_of_comp_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A C D E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : A ⟶ C) (i : C ⟶ E) (q : A ⟶ D) (g : D ⟶ E)
    (h : p ≫ i = q ≫ g) (w : points B S hS A) :
    pointsMap B S hS C i (pointsMap B S hS A p w) =
      pointsMap B S hS D g (pointsMap B S hS A q w) :=
  (congrFun (pointsMap_comp B S hS A p i) w).symm.trans
    ((congrArg (fun k => pointsMap B S hS A k w) h).trans
      (congrFun (pointsMap_comp B S hS A q g) w))

/-! ### Intersections of open subspaces -/

section Inf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The intersection of two open subspaces of an algebraic space over `S` is the subspace cut
out by the intersection of their point sets. -/
private theorem inf_eq_openSubspaceOfPoints_inter (hF : IsAlgebraicSpace B S hS F)
    (V W : Subfunctor F) (hV : IsOpenSubspace B S hS V) (hW : IsOpenSubspace B S hS W) :
    V ⊓ W = openSubspaceOfPoints B S hS F
      (Set.range (pointsMap B S hS V.toFunctor V.ι) ∩
        Set.range (pointsMap B S hS W.toFunctor W.ι)) := by
  set P := openSubspaceOfPoints B S hS F
    (Set.range (pointsMap B S hS V.toFunctor V.ι) ∩
      Set.range (pointsMap B S hS W.toFunctor W.ι)) with hPdef
  have hPopen : IsOpenSubspace B S hS P :=
    isOpenSubspace_openSubspaceOfPoints B S hS hF _
      ((isOpen_range_pointsMap_of_isOpenImmersion B S hS V.ι hV.2).inter
        (isOpen_range_pointsMap_of_isOpenImmersion B S hS W.ι hW.2))
  have hrange : Set.range (pointsMap B S hS P.toFunctor P.ι) =
      Set.range (pointsMap B S hS V.toFunctor V.ι) ∩
        Set.range (pointsMap B S hS W.toFunctor W.ι) := by
    rw [hPdef, range_pointsMap_ι_openSubspaceOfPoints]
  have hPV : P ≤ V :=
    le_of_range_pointsMap_ι_subset B S hS hV (hrange ▸ Set.inter_subset_left)
  have hPW : P ≤ W :=
    le_of_range_pointsMap_ι_subset B S hS hW (hrange ▸ Set.inter_subset_right)
  have hcomp (E : Subfunctor F) (h : V ⊓ W ≤ E) (p) :
      pointsMap B S hS E.toFunctor E.ι (pointsMap B S hS _ (Subfunctor.homOfLe h) p) =
        pointsMap B S hS (V ⊓ W).toFunctor (V ⊓ W).ι p := by
    have h' := congrFun (pointsMap_comp B S hS (V ⊓ W).toFunctor (Subfunctor.homOfLe h) E.ι) p
    rw [Subfunctor.homOfLe_ι] at h'
    exact h'.symm
  have hle : V ⊓ W ≤ P := by
    refine le_of_range_pointsMap_ι_subset B S hS hPopen ?_
    rw [hrange]
    rintro x ⟨p, rfl⟩
    exact ⟨⟨_, hcomp V inf_le_left p⟩, ⟨_, hcomp W inf_le_right p⟩⟩
  exact le_antisymm hle (le_inf hPV hPW)

/-- The point set of the intersection of two open subspaces is the intersection of their point
sets. -/
private theorem range_pointsMap_ι_inf (hF : IsAlgebraicSpace B S hS F)
    (V W : Subfunctor F) (hV : IsOpenSubspace B S hS V) (hW : IsOpenSubspace B S hS W) :
    Set.range (pointsMap B S hS (V ⊓ W).toFunctor (V ⊓ W).ι) =
      Set.range (pointsMap B S hS V.toFunctor V.ι) ∩
        Set.range (pointsMap B S hS W.toFunctor W.ι) := by
  rw [inf_eq_openSubspaceOfPoints_inter B S hS hF V W hV hW,
    range_pointsMap_ι_openSubspaceOfPoints]

/-- The part of an open subspace lying outside a closed subspace is an open subspace. -/
private theorem isOpenSubspace_inf_openComplement (hF : IsAlgebraicSpace B S hS F)
    (V W : Subfunctor F) (hV : IsOpenSubspace B S hS V) (hW : IsClosedSubspace B S hS W) :
    IsOpenSubspace B S hS (V ⊓ openComplement B S hS W) :=
  isOpenSubspace_inf B S hS hF V _ hV (isOpenSubspace_openComplement B S hS hF W hW)

/-- The point set of the part of an open subspace lying outside a closed subspace is the
set-theoretic difference of their point sets. -/
private theorem range_pointsMap_ι_inf_openComplement (hF : IsAlgebraicSpace B S hS F)
    (V W : Subfunctor F) (hV : IsOpenSubspace B S hS V) (hW : IsClosedSubspace B S hS W) :
    Set.range (pointsMap B S hS (V ⊓ openComplement B S hS W).toFunctor
        (V ⊓ openComplement B S hS W).ι) =
      Set.range (pointsMap B S hS V.toFunctor V.ι) \
        Set.range (pointsMap B S hS W.toFunctor W.ι) := by
  rw [range_pointsMap_ι_inf B S hS hF V _ hV
    (isOpenSubspace_openComplement B S hS hF W hW), range_pointsMap_ι_openComplement]
  rfl

end Inf

/-! ### Point sets of base changes -/

section Points

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- In a cartesian square of algebraic spaces over `S`, the point set of one projection is the
preimage of the point set of the opposite side. -/
private theorem range_pointsMap_eq_preimage_of_isPullback
    {Z X W U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hW : IsAlgebraicSpace B S hS W) (hU : IsAlgebraicSpace B S hS U)
    (i : Z ⟶ X) (g : U ⟶ X) (p : W ⟶ Z) (q : W ⟶ U) (sq : IsPullback p q i g) :
    Set.range (pointsMap B S hS W q) =
      pointsMap B S hS U g ⁻¹' Set.range (pointsMap B S hS Z i) := by
  let A : AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let V : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let R : AlgebraicSpaces B S hS := ⟨W, hW⟩
  let T : AlgebraicSpaces B S hS := ⟨U, hU⟩
  let aa : A ⟶ V := ObjectProperty.homMk i
  let gg : T ⟶ V := ObjectProperty.homMk g
  let pp : R ⟶ A := ObjectProperty.homMk p
  let qq : R ⟶ T := ObjectProperty.homMk q
  have sq' : IsPullback pp qq aa gg :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS G)) sq
  ext x
  simp only [Set.mem_range, Set.mem_preimage]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨pointsMap B S hS W p w,
      pointsMap_comm_of_comp_eq B S hS p i q g sq.w w⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, -, hqw⟩ := exists_point_of_isPullback B S hS sq' z x hz
    exact ⟨w, hqw⟩

end Points

/-! ### The agreement criterion on points -/

/-- A point lying over a point outside the two difference images belongs to one subset exactly
when it belongs to the other. -/
private theorem mem_range_iff_mem_range_of_notMem_union
    {A₁ A₂ M N : Type*} (i : A₁ → M) (j : A₂ → M)
    (r : A₁ → N) (s : A₂ → N) (q : M → N)
    (hri : ∀ a, q (i a) = r a) (hsj : ∀ b, q (j b) = s b)
    (t : N) (ht : t ∉ (r '' (i ⁻¹' (Set.range j)ᶜ) ∪ s '' (j ⁻¹' (Set.range i)ᶜ)))
    (z : M) (hz : q z = t) : z ∈ Set.range i ↔ z ∈ Set.range j := by
  constructor
  · rintro ⟨a, rfl⟩
    by_contra hnot
    exact ht (Or.inl ⟨a, hnot, by rw [← hri, hz]⟩)
  · rintro ⟨b, rfl⟩
    by_contra hnot
    exact ht (Or.inr ⟨b, hnot, by rw [← hsj, hz]⟩)

section Agreement

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two open subspaces of a base change agree as soon as the subspaces they are pulled back
from agree over the image of that base change. -/
private theorem eq_of_base_change_of_pointsInAgreement
    {M M' N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : M' ⟶ M) (q : M ⟶ N)
    {V W : Subfunctor M} {V' W' : Subfunctor M'}
    (hV' : IsOpenSubspace B S hS V') (hW' : IsOpenSubspace B S hS W')
    (hVimage : Set.range (pointsMap B S hS V'.toFunctor V'.ι) =
      pointsMap B S hS M' k ⁻¹' Set.range (pointsMap B S hS V.toFunctor V.ι))
    (hWimage : Set.range (pointsMap B S hS W'.toFunctor W'.ι) =
      pointsMap B S hS M' k ⁻¹' Set.range (pointsMap B S hS W.toFunctor W.ι))
    (O : Set (points B S hS N))
    (hpoints : ∀ z : points B S hS M',
      pointsMap B S hS M q (pointsMap B S hS M' k z) ∈ O)
    (haway : ∀ t : points B S hS N, t ∈ O →
      t ∉ (pointsMap B S hS V.toFunctor (V.ι ≫ q) ''
            ((pointsMap B S hS V.toFunctor V.ι) ⁻¹'
              (Set.range (pointsMap B S hS W.toFunctor W.ι))ᶜ) ∪
          pointsMap B S hS W.toFunctor (W.ι ≫ q) ''
            ((pointsMap B S hS W.toFunctor W.ι) ⁻¹'
              (Set.range (pointsMap B S hS V.toFunctor V.ι))ᶜ))) :
    V' = W' := by
  refine eq_of_range_pointsMap_ι_eq B S hS hV' hW' (Set.ext fun z => ?_)
  rw [hVimage, hWimage]
  have hcomp (E : Subfunctor M) (x) : pointsMap B S hS M q (pointsMap B S hS E.toFunctor E.ι x) =
      pointsMap B S hS E.toFunctor (E.ι ≫ q) x :=
    (congrFun (pointsMap_comp B S hS E.toFunctor E.ι q) x).symm
  exact mem_range_iff_mem_range_of_notMem_union
    (pointsMap B S hS V.toFunctor V.ι) (pointsMap B S hS W.toFunctor W.ι)
    (pointsMap B S hS V.toFunctor (V.ι ≫ q)) (pointsMap B S hS W.toFunctor (W.ι ≫ q))
    (pointsMap B S hS M q) (hcomp V) (hcomp W) _ (haway _ (hpoints z)) _ rfl

end Agreement

/-! ### Base change of a fibre product along a morphism of the base -/

section BaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A fibre product over a presheaf is the base change along the base of a fibre product taken
further down the base. -/
private theorem exists_isPullback_of_comp
    {T' T Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : T' ⟶ T) (b : T ⟶ Z) (b' : T' ⟶ Z) (w : W ⟶ Z) (hbase : b' = g ≫ b) :
    ∃ k : pullback b' w ⟶ pullback b w,
      IsPullback k (pullback.fst b' w) (pullback.fst b w) g ∧
        k ≫ pullback.snd b w = pullback.snd b' w := by
  have hcond : (pullback.fst b' w ≫ g) ≫ b = pullback.snd b' w ≫ w := by
    rw [Category.assoc, ← hbase]
    exact pullback.condition
  refine ⟨pullback.lift (pullback.fst b' w ≫ g) (pullback.snd b' w) hcond, ?_,
    pullback.lift_snd _ _ _⟩
  have hkFst : pullback.lift (pullback.fst b' w ≫ g) (pullback.snd b' w) hcond ≫
      pullback.fst b w = pullback.fst b' w ≫ g := pullback.lift_fst _ _ _
  have hBig : IsPullback
      (pullback.lift (pullback.fst b' w ≫ g) (pullback.snd b' w) hcond ≫ pullback.snd b w)
      (pullback.fst b' w) w (g ≫ b) := by
    rw [pullback.lift_snd]
    convert (IsPullback.of_hasPullback b' w).flip using 1
    exact hbase.symm
  exact (IsPullback.paste_horiz_iff (IsPullback.of_hasPullback b w).flip hkFst).mp hBig

/-- In the situation of `AlgebraicGeometry.Space.exists_isPullback_of_comp`, a subspace pulled
back from a subspace further down is the base change of it. -/
private theorem isPullback_ι_of_baseChange
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {T T' : AlgebraicSpaces B S hS}
    (b : T ⟶ Y) (b' : T' ⟶ Y) (g : T'.obj ⟶ T.obj)
    {Z : Subfunctor (pullback b.hom f.hom)} {Z' : Subfunctor (pullback b'.hom f.hom)}
    (k : pullback b'.hom f.hom ⟶ pullback b.hom f.hom)
    (hk : IsPullback k (pullback.fst b'.hom f.hom) (pullback.fst b.hom f.hom) g)
    (hksnd : k ≫ pullback.snd b.hom f.hom = pullback.snd b'.hom f.hom)
    (j : Z'.toFunctor ⟶ Z.toFunctor)
    (hj : IsPullback (Z'.ι ≫ pullback.fst b'.hom f.hom) j g
      (Z.ι ≫ pullback.fst b.hom f.hom))
    (hsnd : j ≫ Z.ι ≫ pullback.snd b.hom f.hom = Z'.ι ≫ pullback.snd b'.hom f.hom) :
    IsPullback Z'.ι j k Z.ι := by
  have hcomm : j ≫ Z.ι = Z'.ι ≫ k := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hk.w, ← Category.assoc]
      exact hj.w.symm
    · rw [Category.assoc, Category.assoc, hksnd]
      exact hsnd
  exact ((hk.paste_vert_iff hcomm).mp hj.flip).flip

/-- In the situation of `AlgebraicGeometry.Space.exists_isPullback_of_comp`, the point set of a
subspace pulled back from a subspace further down is the preimage of the latter's point set. -/
private theorem range_pointsMap_ι_of_baseChange
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {T T' : AlgebraicSpaces B S hS}
    (b : T ⟶ Y) (b' : T' ⟶ Y) (g : T'.obj ⟶ T.obj)
    {Z : Subfunctor (pullback b.hom f.hom)} {Z' : Subfunctor (pullback b'.hom f.hom)}
    (hZ : IsOpenSubspace B S hS Z) (hZ' : IsOpenSubspace B S hS Z')
    (k : pullback b'.hom f.hom ⟶ pullback b.hom f.hom)
    (hk : IsPullback k (pullback.fst b'.hom f.hom) (pullback.fst b.hom f.hom) g)
    (hksnd : k ≫ pullback.snd b.hom f.hom = pullback.snd b'.hom f.hom)
    (j : Z'.toFunctor ⟶ Z.toFunctor)
    (hj : IsPullback (Z'.ι ≫ pullback.fst b'.hom f.hom) j g
      (Z.ι ≫ pullback.fst b.hom f.hom))
    (hsnd : j ≫ Z.ι ≫ pullback.snd b.hom f.hom = Z'.ι ≫ pullback.snd b'.hom f.hom) :
    Set.range (pointsMap B S hS Z'.toFunctor Z'.ι) =
      pointsMap B S hS (pullback b'.hom f.hom) k ⁻¹'
        Set.range (pointsMap B S hS Z.toFunctor Z.ι) :=
  range_pointsMap_eq_preimage_of_isPullback B S hS hZ.1
    (isAlgebraicSpace_pullback B S hS b.hom f.hom T.property X.property Y.property) hZ'.1
    (isAlgebraicSpace_pullback B S hS b'.hom f.hom T'.property X.property Y.property)
    Z.ι k j Z'.ι
    (isPullback_ι_of_baseChange B S hS f b b' g k hk hksnd j hj hsnd).flip

/-- The base-change datum of `AlgebraicGeometry.Space.finiteOpenSubspaceEquiv` transported
along equalities of the two finite open pairs it relates. -/
private theorem exists_baseChange_datum_of_eq
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {T T' : AlgebraicSpaces B S hS}
    (q q' : FiniteOpenSubspace B S hS f T) (hq : q = q')
    (R R' : FiniteOpenSubspace B S hS f T') (hR : R = R')
    (g : T'.obj ⟶ T.obj)
    (j : R.subspace.toFunctor ⟶ q.subspace.toFunctor)
    (hj : IsPullback (R.subspace.ι ≫ pullback.fst R.toBase.hom f.hom) j g
      (q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom))
    (hsnd : j ≫ q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom =
      R.subspace.ι ≫ pullback.snd R.toBase.hom f.hom) :
    ∃ j' : R'.subspace.toFunctor ⟶ q'.subspace.toFunctor,
      IsPullback (R'.subspace.ι ≫ pullback.fst R'.toBase.hom f.hom) j' g
          (q'.subspace.ι ≫ pullback.fst q'.toBase.hom f.hom) ∧
        j' ≫ q'.subspace.ι ≫ pullback.snd q'.toBase.hom f.hom =
          R'.subspace.ι ≫ pullback.snd R'.toBase.hom f.hom := by
  cases hq
  cases hR
  exact ⟨j, hj, hsnd⟩

/-- A point of a fibre product lying over the image of a scheme of the site belongs to one of
two subspaces exactly when it belongs to the other, as soon as the two subspaces pull back to
one and the same subspace of the base change. -/
private theorem mem_range_iff_mem_range_of_baseChange
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {T : AlgebraicSpaces B S hS}
    {Usite : BigFppfOver B S hS} (g : yoneda.obj Usite ⟶ T.obj)
    (b : T ⟶ Y) (Z₁ Z₂ : Subfunctor (pullback b.hom f.hom))
    (hZ₁ : IsOpenSubspace B S hS Z₁) (hZ₂ : IsOpenSubspace B S hS Z₂)
    (rb : schemeSpace Usite ⟶ Y) (hrb : rb.hom = g ≫ b.hom)
    (W : Subfunctor (pullback rb.hom f.hom)) (hW : IsOpenSubspace B S hS W)
    (j₁ : W.toFunctor ⟶ Z₁.toFunctor)
    (hj₁ : IsPullback (W.ι ≫ pullback.fst rb.hom f.hom) j₁ g
      (Z₁.ι ≫ pullback.fst b.hom f.hom))
    (hsnd₁ : j₁ ≫ Z₁.ι ≫ pullback.snd b.hom f.hom = W.ι ≫ pullback.snd rb.hom f.hom)
    (j₂ : W.toFunctor ⟶ Z₂.toFunctor)
    (hj₂ : IsPullback (W.ι ≫ pullback.fst rb.hom f.hom) j₂ g
      (Z₂.ι ≫ pullback.fst b.hom f.hom))
    (hsnd₂ : j₂ ≫ Z₂.ι ≫ pullback.snd b.hom f.hom = W.ι ≫ pullback.snd rb.hom f.hom)
    (t : points B S hS (yoneda.obj Usite)) (a : points B S hS (pullback b.hom f.hom))
    (ha : pointsMap B S hS (pullback b.hom f.hom) (pullback.fst b.hom f.hom) a =
      pointsMap B S hS (yoneda.obj Usite) g t) :
    a ∈ Set.range (pointsMap B S hS Z₁.toFunctor Z₁.ι) ↔
      a ∈ Set.range (pointsMap B S hS Z₂.toFunctor Z₂.ι) := by
  obtain ⟨k, hk, hksnd⟩ := exists_isPullback_of_comp B S hS g b.hom rb.hom f.hom hrb
  have h₁ := range_pointsMap_ι_of_baseChange B S hS f b rb g hZ₁ hW k hk hksnd j₁ hj₁ hsnd₁
  have h₂ := range_pointsMap_ι_of_baseChange B S hS f b rb g hZ₂ hW k hk hksnd j₂ hj₂ hsnd₂
  let Aspace : AlgebraicSpaces B S hS := ⟨pullback b.hom f.hom,
    isAlgebraicSpace_pullback B S hS b.hom f.hom T.property X.property Y.property⟩
  let Mspace : AlgebraicSpaces B S hS := ⟨pullback rb.hom f.hom,
    isAlgebraicSpace_pullback B S hS rb.hom f.hom
      (schemeSpace Usite).property X.property Y.property⟩
  have hsq : IsPullback (ObjectProperty.homMk k : Mspace ⟶ Aspace)
      (ObjectProperty.homMk (pullback.fst rb.hom f.hom) :
        Mspace ⟶ schemeSpace Usite)
      (ObjectProperty.homMk (pullback.fst b.hom f.hom) : Aspace ⟶ T)
      (ObjectProperty.homMk g : schemeSpace Usite ⟶ T) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS G)) hk
  obtain ⟨z, hz, -⟩ := exists_point_of_isPullback B S hS hsq a t ha
  have hz' : pointsMap B S hS (pullback rb.hom f.hom) k z = a := hz
  rw [← hz', ← Set.mem_preimage, ← Set.mem_preimage, ← h₁, ← h₂]

end BaseChange

/-! ### Openness of the difference images -/

section Difference

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The image in the base of the part of an open subspace lying outside a closed subspace is
open, provided the projection of the fibre product to the base is open. -/
private theorem isOpen_range_pointsMap_comp_fst_inf_openComplement
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {T : AlgebraicSpaces B S hS} (a : T ⟶ Y)
    (hopen : UniversallyOpen B S hS f.hom)
    (Z₁ Z₂ : Subfunctor (pullback a.hom f.hom))
    (hZ₁ : IsOpenSubspace B S hS Z₁) (hZ₂ : IsClosedSubspace B S hS Z₂) :
    IsOpen (Set.range (pointsMap B S hS (Z₁ ⊓ openComplement B S hS Z₂).toFunctor
      ((Z₁ ⊓ openComplement B S hS Z₂).ι ≫ pullback.fst a.hom f.hom))) := by
  have hA : IsAlgebraicSpace B S hS (pullback a.hom f.hom) :=
    isAlgebraicSpace_pullback B S hS a.hom f.hom T.property X.property Y.property
  have hπ : IsOpenMap (pointsMap B S hS (pullback a.hom f.hom) (pullback.fst a.hom f.hom)) :=
    hopen T.obj T.property a.hom
  have hD : IsOpen (Set.range (pointsMap B S hS (Z₁ ⊓ openComplement B S hS Z₂).toFunctor
      (Z₁ ⊓ openComplement B S hS Z₂).ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS _
      (isOpenSubspace_inf_openComplement B S hS hA Z₁ Z₂ hZ₁ hZ₂).2
  rw [pointsMap_comp B S hS _ (Z₁ ⊓ openComplement B S hS Z₂).ι (pullback.fst a.hom f.hom),
    Set.range_comp]
  exact hπ _ hD

end Difference

/-! ### Field-valued points of a represented presheaf -/

section SitePoints

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The tautological field-valued point of the presheaf represented by the site object of a
field-valued point. -/
private def tautologicalPoint (p : FieldValuedPoint B S hS F) :
    FieldValuedPoint B S hS (yoneda.obj (p.siteObject B S hS F)) where
  carrier := p.carrier
  contained := p.contained
  toBase := p.toBase
  value := 𝟙 (p.siteObject B S hS F)

/-- The tautological field-valued point maps to the point it was built from. -/
private theorem map_tautologicalPoint (p : FieldValuedPoint B S hS F) :
    FieldValuedPoint.map B S hS (yoneda.obj (p.siteObject B S hS F))
      (yonedaEquiv.symm p.value) (tautologicalPoint B S hS p) = p := by
  cases p with
  | mk carrier contained toBase value =>
    exact congrArg
      (fun v => (⟨carrier, contained, toBase, v⟩ : FieldValuedPoint B S hS F))
      (yonedaEquiv.apply_symm_apply value)

/-- Every field-valued point of the presheaf represented by the site object of a field-valued
point is the tautological one. -/
private theorem class_eq_class_tautologicalPoint (p : FieldValuedPoint B S hS F)
    (z : FieldValuedPoint B S hS (yoneda.obj (p.siteObject B S hS F))) :
    z.class B S hS (yoneda.obj (p.siteObject B S hS F)) =
      (tautologicalPoint B S hS p).class B S hS (yoneda.obj (p.siteObject B S hS F)) :=
  FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS _
    ⟨z, FieldValuedPoint.dominates_refl B S hS _ z, z.value, rfl⟩

/-- Every point of the presheaf represented by the site object of a field-valued point is the
class of the tautological one. -/
private theorem eq_class_tautologicalPoint (p : FieldValuedPoint B S hS F)
    (t : points B S hS (yoneda.obj (p.siteObject B S hS F))) :
    t = (tautologicalPoint B S hS p).class B S hS _ := by
  induction t using Quot.inductionOn with
  | _ t₀ => exact class_eq_class_tautologicalPoint B S hS p t₀

/-- The class of the tautological point maps to the class of the point it was built from. -/
private theorem pointsMap_class_tautologicalPoint (p : FieldValuedPoint B S hS F) :
    pointsMap B S hS (yoneda.obj (p.siteObject B S hS F)) (yonedaEquiv.symm p.value)
      ((tautologicalPoint B S hS p).class B S hS _) = p.class B S hS F := by
  rw [pointsMap_class]
  exact congrArg (FieldValuedPoint.class B S hS F) (map_tautologicalPoint B S hS p)

end SitePoints

/-! ### The base morphism of a section of the finite part -/

section FinitePart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two sections of the finite part with the same image under the projection to `Y` name the
same morphism to `Y`. -/
private theorem finiteOpenSubspaceEquiv_toBase_hom_eq
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (T : AlgebraicSpaces B S hS)
    (v₁ v₂ : T.obj ⟶ (finiteOpenSubspacePresheaf B S hS f).toFunctor)
    (h : v₁ ≫ (finiteOpenSubspacePresheaf B S hS f).baseMap =
      v₂ ≫ (finiteOpenSubspacePresheaf B S hS f).baseMap) :
    ((finiteOpenSubspaceEquiv B S hS f T).1 v₁).toBase.hom =
      ((finiteOpenSubspaceEquiv B S hS f T).1 v₂).toBase.hom := by
  let P := finiteOpenSubspacePresheaf B S hS f
  let e := (finiteOpenSubspaceEquiv B S hS f T).1
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  let g : yoneda.obj U.unop ⟶ T.obj := yonedaEquiv.symm x
  have hx : yonedaEquiv g = x := Equiv.apply_symm_apply _ _
  have hpoint : P.baseMap.app U (v₁.app U x) = P.baseMap.app U (v₂.app U x) :=
    congrArg (fun n => n.app U x) h
  have hpairBase : (P.sections U.unop (v₁.app U x)).toBase.hom =
      (P.sections U.unop (v₂.app U x)).toBase.hom :=
    (P.baseMap_spec U.unop (v₁.app U x)).symm.trans
      ((congrArg yonedaEquiv.symm hpoint).trans (P.baseMap_spec U.unop (v₂.app U x)))
  have h₁' := ((finiteOpenSubspaceEquiv B S hS f T).2 v₁ U.unop g).1
  have h₂' := ((finiteOpenSubspaceEquiv B S hS f T).2 v₂ U.unop g).1
  rw [hx] at h₁' h₂'
  calc
    _ = (e v₁).toBase.hom.app U (yonedaEquiv g) := congrArg _ hx.symm
    _ = yonedaEquiv (g ≫ (e v₁).toBase.hom) := (yonedaEquiv_comp g (e v₁).toBase.hom).symm
    _ = yonedaEquiv (g ≫ (e v₂).toBase.hom) :=
      congrArg yonedaEquiv (h₁'.symm.trans (hpairBase.trans h₂'))
    _ = (e v₂).toBase.hom.app U (yonedaEquiv g) := yonedaEquiv_comp g (e v₂).toBase.hom
    _ = _ := congrArg _ hx

/-- Two finite open pairs over a scheme of the site, restricted from two pairs over an
algebraic space with the same morphism to `Y`, agree as soon as the restriction lands away
from the two difference images. -/
private theorem sections_eq_of_pointsInAgreement
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {T : AlgebraicSpaces B S hS}
    {Usite : BigFppfOver B S hS} (g : yoneda.obj Usite ⟶ T.obj)
    (b : T ⟶ Y) (Z₁ Z₂ : Subfunctor (pullback b.hom f.hom))
    (hZ₁ : IsOpenSubspace B S hS Z₁) (hZ₂ : IsOpenSubspace B S hS Z₂)
    (R₁ R₂ : FiniteOpenSubspace B S hS f (schemeSpace Usite))
    (hRbase : R₂.toBase = R₁.toBase) (hrb : R₁.toBase.hom = g ≫ b.hom)
    (j₁ : R₁.subspace.toFunctor ⟶ Z₁.toFunctor)
    (hj₁ : IsPullback (R₁.subspace.ι ≫ pullback.fst R₁.toBase.hom f.hom) j₁ g
      (Z₁.ι ≫ pullback.fst b.hom f.hom))
    (hsnd₁ : j₁ ≫ Z₁.ι ≫ pullback.snd b.hom f.hom =
      R₁.subspace.ι ≫ pullback.snd R₁.toBase.hom f.hom)
    (j₂ : R₂.subspace.toFunctor ⟶ Z₂.toFunctor)
    (hj₂ : IsPullback (R₂.subspace.ι ≫ pullback.fst R₂.toBase.hom f.hom) j₂ g
      (Z₂.ι ≫ pullback.fst b.hom f.hom))
    (hsnd₂ : j₂ ≫ Z₂.ι ≫ pullback.snd b.hom f.hom =
      R₂.subspace.ι ≫ pullback.snd R₂.toBase.hom f.hom)
    (O : Set (points B S hS T.obj))
    (hO : ∀ t : points B S hS (yoneda.obj Usite),
      pointsMap B S hS (yoneda.obj Usite) g t ∈ O)
    (haway : ∀ t : points B S hS T.obj, t ∈ O →
      t ∉ (pointsMap B S hS Z₁.toFunctor (Z₁.ι ≫ pullback.fst b.hom f.hom) ''
            ((pointsMap B S hS Z₁.toFunctor Z₁.ι) ⁻¹'
              (Set.range (pointsMap B S hS Z₂.toFunctor Z₂.ι))ᶜ) ∪
          pointsMap B S hS Z₂.toFunctor (Z₂.ι ≫ pullback.fst b.hom f.hom) ''
            ((pointsMap B S hS Z₂.toFunctor Z₂.ι) ⁻¹'
              (Set.range (pointsMap B S hS Z₁.toFunctor Z₁.ι))ᶜ))) :
    R₁ = R₂ := by
  obtain ⟨rb, W₁, hW₁, hfin₁⟩ := R₁
  obtain ⟨rb₂, W₂, hW₂, hfin₂⟩ := R₂
  cases hRbase
  obtain ⟨k, hk, hksnd⟩ := exists_isPullback_of_comp B S hS g b.hom rb.hom f.hom hrb
  have h₁ := range_pointsMap_ι_of_baseChange B S hS f b rb g hZ₁ hW₁ k hk hksnd j₁ hj₁ hsnd₁
  have h₂ := range_pointsMap_ι_of_baseChange B S hS f b rb g hZ₂ hW₂ k hk hksnd j₂ hj₂ hsnd₂
  have hpoints : ∀ z : points B S hS (pullback rb.hom f.hom),
      pointsMap B S hS (pullback b.hom f.hom) (pullback.fst b.hom f.hom)
        (pointsMap B S hS (pullback rb.hom f.hom) k z) ∈ O := by
    intro z
    have hfac := pointsMap_comm_of_comp_eq B S hS k (pullback.fst b.hom f.hom)
      (pullback.fst rb.hom f.hom) g hk.w z
    exact hfac ▸ hO _
  have hWeq : W₁ = W₂ :=
    eq_of_base_change_of_pointsInAgreement B S hS k (pullback.fst b.hom f.hom)
      hW₁ hW₂ h₁ h₂ O hpoints haway
  cases hWeq
  rfl

end FinitePart

/-! ### Separatedness of the projection -/

/-- A morphism to `pullback h h` whose two projections agree factors through the diagonal. -/
private lemma eq_comp_diagonal_of_comp_fst_eq_comp_snd {C : Type*} [Category C] {X Y Z : C}
    {h : X ⟶ Y} [HasPullback h h] (g : Z ⟶ pullback h h)
    (hg : g ≫ pullback.fst h h = g ≫ pullback.snd h h) :
    g = (g ≫ pullback.fst h h) ≫ pullback.diagonal h :=
  pullback.hom_ext (by simp) (by simp [hg])

/-- The union of the images in `T` of `Z₁ ∖ Z₂` and `Z₂ ∖ Z₁`, for two subspaces `Z₁, Z₂` of
`T ×_Y X`. -/
private def differenceImage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T : AlgebraicSpaces B S hS} (b : T ⟶ Y) (Z₁ Z₂ : Subfunctor (pullback b.hom f.hom)) :
    Set (points B S hS T.obj) :=
  Set.range (pointsMap B S hS (Z₁ ⊓ openComplement B S hS Z₂).toFunctor
      ((Z₁ ⊓ openComplement B S hS Z₂).ι ≫ pullback.fst b.hom f.hom)) ∪
    Set.range (pointsMap B S hS (Z₂ ⊓ openComplement B S hS Z₁).toFunctor
      ((Z₂ ⊓ openComplement B S hS Z₁).ι ≫ pullback.fst b.hom f.hom))

/-- For open and closed `Z₁, Z₂`, the difference image is the union of the images of the
set-theoretic differences of their point sets. -/
private theorem differenceImage_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T : AlgebraicSpaces B S hS} (b : T ⟶ Y) (Z₁ Z₂ : Subfunctor (pullback b.hom f.hom))
    (hZ₁ : IsOpenSubspace B S hS Z₁) (hZ₂ : IsOpenSubspace B S hS Z₂)
    (hZ₁c : IsClosedSubspace B S hS Z₁) (hZ₂c : IsClosedSubspace B S hS Z₂) :
    differenceImage B S hS f b Z₁ Z₂ =
      pointsMap B S hS _ (pullback.fst b.hom f.hom) ''
          (Set.range (pointsMap B S hS Z₁.toFunctor Z₁.ι) \
            Set.range (pointsMap B S hS Z₂.toFunctor Z₂.ι)) ∪
        pointsMap B S hS _ (pullback.fst b.hom f.hom) ''
          (Set.range (pointsMap B S hS Z₂.toFunctor Z₂.ι) \
            Set.range (pointsMap B S hS Z₁.toFunctor Z₁.ι)) := by
  have hA := isAlgebraicSpace_pullback B S hS b.hom f.hom T.property X.property Y.property
  rw [differenceImage, pointsMap_comp B S hS _ (Z₁ ⊓ openComplement B S hS Z₂).ι,
    pointsMap_comp B S hS _ (Z₂ ⊓ openComplement B S hS Z₁).ι, Set.range_comp, Set.range_comp,
    range_pointsMap_ι_inf_openComplement B S hS hA Z₁ Z₂ hZ₁ hZ₂c,
    range_pointsMap_ι_inf_openComplement B S hS hA Z₂ Z₁ hZ₂ hZ₁c]

/-- A point of `T` outside the difference image is the image of no point of `Z₁ ∖ Z₂` nor of
`Z₂ ∖ Z₁`. -/
private theorem notMem_image_of_notMem_differenceImage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) {T : AlgebraicSpaces B S hS} (b : T ⟶ Y)
    (Z₁ Z₂ : Subfunctor (pullback b.hom f.hom))
    (hZ₁ : IsOpenSubspace B S hS Z₁) (hZ₂ : IsOpenSubspace B S hS Z₂)
    (hZ₁c : IsClosedSubspace B S hS Z₁) (hZ₂c : IsClosedSubspace B S hS Z₂)
    (t : points B S hS T.obj) (ht : t ∈ (differenceImage B S hS f b Z₁ Z₂)ᶜ) :
    t ∉ (pointsMap B S hS Z₁.toFunctor (Z₁.ι ≫ pullback.fst b.hom f.hom) ''
          ((pointsMap B S hS Z₁.toFunctor Z₁.ι) ⁻¹'
            (Set.range (pointsMap B S hS Z₂.toFunctor Z₂.ι))ᶜ) ∪
        pointsMap B S hS Z₂.toFunctor (Z₂.ι ≫ pullback.fst b.hom f.hom) ''
          ((pointsMap B S hS Z₂.toFunctor Z₂.ι) ⁻¹'
            (Set.range (pointsMap B S hS Z₁.toFunctor Z₁.ι))ᶜ)) := by
  rw [Set.mem_compl_iff, differenceImage_eq B S hS f b Z₁ Z₂ hZ₁ hZ₂ hZ₁c hZ₂c] at ht
  rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
  · exact ht (Set.mem_union_left _ ⟨_, ⟨⟨z, rfl⟩, hz⟩,
      (congrFun (pointsMap_comp B S hS _ Z₁.ι (pullback.fst b.hom f.hom)) z).symm⟩)
  · exact ht (Set.mem_union_right _ ⟨_, ⟨⟨z, rfl⟩, hz⟩,
      (congrFun (pointsMap_comp B S hS _ Z₂.ι (pullback.fst b.hom f.hom)) z).symm⟩)

/-- A point of `T` over which `Z₁` and `Z₂` have the same points lies outside the difference
image. -/
private theorem notMem_differenceImage_of_forall_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) {T : AlgebraicSpaces B S hS} (b : T ⟶ Y)
    (Z₁ Z₂ : Subfunctor (pullback b.hom f.hom))
    (hZ₁ : IsOpenSubspace B S hS Z₁) (hZ₂ : IsOpenSubspace B S hS Z₂)
    (hZ₁c : IsClosedSubspace B S hS Z₁) (hZ₂c : IsClosedSubspace B S hS Z₂)
    (x : points B S hS T.obj)
    (h : ∀ a, pointsMap B S hS (pullback b.hom f.hom) (pullback.fst b.hom f.hom) a = x →
      (a ∈ Set.range (pointsMap B S hS Z₁.toFunctor Z₁.ι) ↔
        a ∈ Set.range (pointsMap B S hS Z₂.toFunctor Z₂.ι))) :
    x ∉ differenceImage B S hS f b Z₁ Z₂ := by
  rw [differenceImage_eq B S hS f b Z₁ Z₂ hZ₁ hZ₂ hZ₁c hZ₂c]
  rintro (⟨a, ha, hax⟩ | ⟨a, ha, hax⟩)
  · exact ha.2 ((h a hax).mp ha.1)
  · exact ha.2 ((h a hax).mpr ha.1)

/-- A section of the finite part over a scheme of the site, pulled back from a section naming
the finite open pair `(b, Z)`, lies over `b` and carries the base-change datum of `Z`. -/
private theorem baseChange_datum_of_section
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {T : AlgebraicSpaces B S hS} (b : T ⟶ Y)
    (Z : Subfunctor (pullback b.hom f.hom))
    (hZ : IsOpenSubspace B S hS Z) (fin : IsFinite B S hS (Z.ι ≫ pullback.fst b.hom f.hom))
    (v : T.obj ⟶ (finiteOpenSubspacePresheaf B S hS f).toFunctor)
    (hv : (finiteOpenSubspaceEquiv B S hS f T).1 v = ⟨b, Z, hZ, fin⟩)
    {Usite : BigFppfOver B S hS} (g : yoneda.obj Usite ⟶ T.obj)
    (R : FiniteOpenSubspace B S hS f (schemeSpace Usite))
    (hR : (finiteOpenSubspacePresheaf B S hS f).sections Usite
      (v.app (op Usite) (yonedaEquiv g)) = R) :
    R.toBase.hom = g ≫ b.hom ∧ ∃ j : R.subspace.toFunctor ⟶ Z.toFunctor,
      IsPullback (R.subspace.ι ≫ pullback.fst R.toBase.hom f.hom) j g
          (Z.ι ≫ pullback.fst b.hom f.hom) ∧
        j ≫ Z.ι ≫ pullback.snd b.hom f.hom = R.subspace.ι ≫ pullback.snd R.toBase.hom f.hom := by
  subst hR
  have hPE := (finiteOpenSubspaceEquiv B S hS f T).2 v Usite g
  refine ⟨hPE.1.trans (congrArg (fun a => g ≫ a.toBase.hom) hv), ?_⟩
  obtain ⟨j, hj, hX⟩ := hPE.2
  exact exists_baseChange_datum_of_eq B S hS f _ _ hv _ _ rfl g j hj hX

/-- Two sections `v₁, v₂` of the finite part over `T`, naming finite open pairs `(b, Z₁)` and
`(b, Z₂)` with the same base, take a field-valued point where they agree outside the difference
image of `Z₁, Z₂`. -/
private theorem notMem_differenceImage_of_app_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) {T : AlgebraicSpaces B S hS} (b : T ⟶ Y)
    (Z₁ Z₂ : Subfunctor (pullback b.hom f.hom))
    (hZ₁ : IsOpenSubspace B S hS Z₁) (hZ₂ : IsOpenSubspace B S hS Z₂)
    (hZ₁c : IsClosedSubspace B S hS Z₁) (hZ₂c : IsClosedSubspace B S hS Z₂)
    (fin₁ : IsFinite B S hS (Z₁.ι ≫ pullback.fst b.hom f.hom))
    (fin₂ : IsFinite B S hS (Z₂.ι ≫ pullback.fst b.hom f.hom))
    (v₁ v₂ : T.obj ⟶ (finiteOpenSubspacePresheaf B S hS f).toFunctor)
    (hv₁ : (finiteOpenSubspaceEquiv B S hS f T).1 v₁ = ⟨b, Z₁, hZ₁, fin₁⟩)
    (hv₂ : (finiteOpenSubspaceEquiv B S hS f T).1 v₂ = ⟨b, Z₂, hZ₂, fin₂⟩)
    (p : FieldValuedPoint B S hS T.obj)
    (hp : v₁.app (op (p.siteObject B S hS T.obj)) p.value =
      v₂.app (op (p.siteObject B S hS T.obj)) p.value) :
    p.class B S hS T.obj ∉ differenceImage B S hS f b Z₁ Z₂ := by
  let P := finiteOpenSubspacePresheaf B S hS f
  let Usite := p.siteObject B S hS T.obj
  let g : yoneda.obj Usite ⟶ T.obj := yonedaEquiv.symm p.value
  have hξη : v₁.app (op Usite) (yonedaEquiv g) = v₂.app (op Usite) (yonedaEquiv g) := by
    rw [show yonedaEquiv g = p.value from Equiv.apply_symm_apply _ _]
    exact hp
  let R₁ := P.sections Usite (v₁.app (op Usite) (yonedaEquiv g))
  let R₂ := P.sections Usite (v₂.app (op Usite) (yonedaEquiv g))
  obtain ⟨hbase₁, j₁', hj₁', hX₁'⟩ :=
    baseChange_datum_of_section B S hS f b Z₁ hZ₁ fin₁ v₁ hv₁ g R₁ rfl
  obtain ⟨-, j₂', hj₂', hX₂'⟩ := baseChange_datum_of_section B S hS f b Z₂ hZ₂ fin₂ v₂ hv₂ g R₁
    (congrArg (P.sections Usite) hξη).symm
  refine notMem_differenceImage_of_forall_iff B S hS f b Z₁ Z₂ hZ₁ hZ₂ hZ₁c hZ₂c _
    fun a ha => mem_range_iff_mem_range_of_baseChange B S hS f g b Z₁ Z₂ hZ₁ hZ₂ R₁.toBase
      hbase₁ R₁.subspace R₁.isOpen j₁' hj₁' hX₁' j₂' hj₂' hX₂'
      ((tautologicalPoint B S hS p).class B S hS (yoneda.obj Usite)) a ?_
  rw [ha]
  exact (pointsMap_class_tautologicalPoint B S hS p).symm

/-- Two sections `v₁, v₂` of the finite part over `T`, naming finite open pairs `(b, Z₁)` and
`(b, Z₂)` with the same base, agree at a field-valued point lying outside the difference image
of `Z₁, Z₂`. -/
private theorem app_eq_of_notMem_differenceImage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) {T : AlgebraicSpaces B S hS} (b : T ⟶ Y)
    (Z₁ Z₂ : Subfunctor (pullback b.hom f.hom))
    (hZ₁ : IsOpenSubspace B S hS Z₁) (hZ₂ : IsOpenSubspace B S hS Z₂)
    (hZ₁c : IsClosedSubspace B S hS Z₁) (hZ₂c : IsClosedSubspace B S hS Z₂)
    (fin₁ : IsFinite B S hS (Z₁.ι ≫ pullback.fst b.hom f.hom))
    (fin₂ : IsFinite B S hS (Z₂.ι ≫ pullback.fst b.hom f.hom))
    (v₁ v₂ : T.obj ⟶ (finiteOpenSubspacePresheaf B S hS f).toFunctor)
    (hv₁ : (finiteOpenSubspaceEquiv B S hS f T).1 v₁ = ⟨b, Z₁, hZ₁, fin₁⟩)
    (hv₂ : (finiteOpenSubspaceEquiv B S hS f T).1 v₂ = ⟨b, Z₂, hZ₂, fin₂⟩)
    (p : FieldValuedPoint B S hS T.obj)
    (hx : p.class B S hS T.obj ∈ (differenceImage B S hS f b Z₁ Z₂)ᶜ) :
    v₁.app (op (p.siteObject B S hS T.obj)) (yonedaEquiv (yonedaEquiv.symm p.value)) =
      v₂.app (op (p.siteObject B S hS T.obj)) (yonedaEquiv (yonedaEquiv.symm p.value)) := by
  let P := finiteOpenSubspacePresheaf B S hS f
  let Usite := p.siteObject B S hS T.obj
  let g : yoneda.obj Usite ⟶ T.obj := yonedaEquiv.symm p.value
  let R₁ := P.sections Usite (v₁.app (op Usite) (yonedaEquiv g))
  let R₂ := P.sections Usite (v₂.app (op Usite) (yonedaEquiv g))
  obtain ⟨hbase₁, j₁', hj₁', hX₁'⟩ :=
    baseChange_datum_of_section B S hS f b Z₁ hZ₁ fin₁ v₁ hv₁ g R₁ rfl
  obtain ⟨hbase₂, j₂', hj₂', hX₂'⟩ :=
    baseChange_datum_of_section B S hS f b Z₂ hZ₂ fin₂ v₂ hv₂ g R₂ rfl
  have hO : ∀ t : points B S hS (yoneda.obj Usite),
      pointsMap B S hS (yoneda.obj Usite) g t ∈ (differenceImage B S hS f b Z₁ Z₂)ᶜ :=
    fun t => by
      rw [eq_class_tautologicalPoint B S hS p t, pointsMap_class_tautologicalPoint]
      exact hx
  exact (P.sections Usite).injective
    (sections_eq_of_pointsInAgreement B S hS f g b Z₁ Z₂ hZ₁ hZ₂ R₁ R₂
      (ObjectProperty.hom_ext _ (hbase₂.trans hbase₁.symm)) hbase₁ j₁' hj₁' hX₁' j₂' hj₂' hX₂'
      _ hO (notMem_image_of_notMem_differenceImage B S hS f b Z₁ Z₂ hZ₁ hZ₂ hZ₁c hZ₂c))

/-- **Stacks 04RI, part (1).** For a separated, flat morphism `f : X ⟶ Y` of algebraic spaces
over `S` which is locally of finite presentation, the projection `(X/Y)_fin ⟶ Y` from the
finite part of `f` is separated. -/
@[stacks 04RI "part (1): separatedness"]
theorem isSeparated_baseMap_finiteOpenSubspacePresheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hsep : IsSeparated B S hS f.hom)
    (hflat : IsFlat B S hS f.hom)
    (hfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    IsSeparated B S hS (finiteOpenSubspacePresheaf B S hS f).baseMap := by
  let P := finiteOpenSubspacePresheaf B S hS f
  have hP : IsAlgebraicSpace B S hS P.toFunctor := isAlgebraicSpace_finiteOpenSubspacePresheaf
    B S hS f hsep (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp)
  have hTarget : IsAlgebraicSpace B S hS (pullback P.baseMap P.baseMap) :=
    isAlgebraicSpace_pullback B S hS P.baseMap P.baseMap hP hP Y.property
  let d := pullback.diagonal P.baseMap
  have hdImm : IsImmersion B S hS d :=
    isImmersion_of_isOpenImmersion B S hS
      (isOpenImmersion_diagonal_finiteOpenSubspacePresheaf B S hS f)
  have hopen : UniversallyOpen B S hS f.hom :=
    universallyOpen_of_isFlat_of_isLocallyOfFinitePresentation B S hS X.property Y.property
      f.hom hflat hfp
  let Q : AlgebraicSpaces B S hS := ⟨pullback P.baseMap P.baseMap, hTarget⟩
  let e := (finiteOpenSubspaceEquiv B S hS f Q).1
  have hqbase : (e (pullback.snd P.baseMap P.baseMap)).toBase.hom =
      (e (pullback.fst P.baseMap P.baseMap)).toBase.hom := (finiteOpenSubspaceEquiv_toBase_hom_eq
    B S hS f Q (pullback.fst P.baseMap P.baseMap) _ pullback.condition).symm
  cases hq₁ : e (pullback.fst P.baseMap P.baseMap) with
  | mk base₁ sub₁ open₁ finite₁ =>
    cases hq₂ : e (pullback.snd P.baseMap P.baseMap) with
    | mk base₂ sub₂ open₂ finite₂ =>
      cases (ObjectProperty.hom_ext _ (by simpa [hq₁, hq₂] using hqbase) : base₂ = base₁)
      have hc₁ := FiniteOpenSubspace.isClosedSubspace B S hS f Q ⟨base₁, sub₁, open₁, finite₁⟩ hsep
      have hc₂ := FiniteOpenSubspace.isClosedSubspace B S hS f Q ⟨base₁, sub₂, open₂, finite₂⟩ hsep
      have hrange : Set.range (pointsMap B S hS P.toFunctor d) =
          (differenceImage B S hS f base₁ sub₁ sub₂)ᶜ := by
        refine Set.ext fun x => ⟨?_, fun hx => ?_⟩
        · rintro ⟨y, rfl⟩
          induction y using Quot.inductionOn with
          | _ p₀ =>
            exact notMem_differenceImage_of_app_eq B S hS f base₁ sub₁ sub₂ open₁ open₂ hc₁
              hc₂ finite₁ finite₂ _ _ hq₁ hq₂ (FieldValuedPoint.map B S hS P.toFunctor d p₀)
              (congrArg (fun α => α.app _ p₀.value)
                ((pullback.diagonal_fst P.baseMap).trans (pullback.diagonal_snd P.baseMap).symm))
        · obtain ⟨p, rfl⟩ := Quot.exists_rep x
          have hg := eq_comp_diagonal_of_comp_fst_eq_comp_snd (yonedaEquiv.symm p.value)
            (yonedaEquiv.injective (by
              rw [yonedaEquiv_comp, yonedaEquiv_comp]
              exact app_eq_of_notMem_differenceImage B S hS f base₁ sub₁ sub₂ open₁ open₂
                hc₁ hc₂ finite₁ finite₂ _ _ hq₁ hq₂ p hx))
          refine ⟨pointsMap B S hS _ (yonedaEquiv.symm p.value ≫
              pullback.fst P.baseMap P.baseMap) ((tautologicalPoint B S hS p).class B S hS _),
            (congrFun (pointsMap_comp B S hS _ _ d) _).symm.trans ?_⟩
          rw [← hg]
          exact pointsMap_class_tautologicalPoint B S hS p
      refine (isClosedImmersion_iff_isClosed_range_pointsMap B S hS hTarget d hdImm).2 ?_
      rw [hrange]
      exact ((isOpen_range_pointsMap_comp_fst_inf_openComplement B S hS f base₁ hopen
        sub₁ sub₂ open₁ hc₂).union (isOpen_range_pointsMap_comp_fst_inf_openComplement
          B S hS f base₁ hopen sub₂ sub₁ open₂ hc₁)).isClosed_compl

/-! ### Étaleness of the projection -/

/-- For a separated, flat morphism `f : X ⟶ Y` of algebraic spaces over `S` which is locally of
finite presentation, the projection `(X/Y)_fin ⟶ Y` from the finite part of `f` is étale: such
a morphism is in particular locally of finite type. -/
@[stacks 04RI "part (1): étaleness"]
theorem isEtale_baseMap_finiteOpenSubspacePresheaf_of_isFlat
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hsep : IsSeparated B S hS f.hom)
    (_hflat : IsFlat B S hS f.hom)
    (hfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    IsEtale B S hS (finiteOpenSubspacePresheaf B S hS f).baseMap :=
  isEtale_baseMap_finiteOpenSubspacePresheaf B S hS f hsep
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp)

/-! ### Representability of the projection and of the finite part -/

/-- **Stacks 04RI, part (1).** For a separated, flat morphism `f : X ⟶ Y` of algebraic spaces
over `S` which is locally of finite presentation, the projection `(X/Y)_fin ⟶ Y` from the finite
part of `f` is representable: it is étale, hence locally quasi-finite, and separated. -/
@[stacks 04RI "part (1): representability"]
theorem relativelyRepresentable_baseMap_finiteOpenSubspacePresheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hsep : IsSeparated B S hS f.hom)
    (hflat : IsFlat B S hS f.hom)
    (hfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    yoneda.relativelyRepresentable (finiteOpenSubspacePresheaf B S hS f).baseMap := by
  have hlft := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp
  exact relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS _
    (isAlgebraicSpace_finiteOpenSubspacePresheaf B S hS f hsep hlft) Y.property
    (isLocallyQuasiFinite_of_isEtale B S hS Y.property
      (isEtale_baseMap_finiteOpenSubspacePresheaf B S hS f hsep hlft))
    (isSeparated_baseMap_finiteOpenSubspacePresheaf B S hS f hsep hflat hfp)

/-- **Stacks 04RI, part (2).** If moreover `Y` is a scheme, then the finite part `(X/Y)_fin` of
a separated, flat morphism locally of finite presentation is a scheme: it is separated and
locally quasi-finite over the representable `Y`, so Stacks 03XX applies. -/
@[stacks 04RI "part (2): the finite part over a scheme is a scheme"]
theorem isRepresentable_finiteOpenSubspacePresheaf_of_isRepresentable
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hsep : IsSeparated B S hS f.hom)
    (hflat : IsFlat B S hS f.hom)
    (hfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (hY : Y.obj.IsRepresentable) :
    (finiteOpenSubspacePresheaf B S hS f).toFunctor.IsRepresentable := by
  have hlft := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp
  exact isRepresentable_of_locallyQuasiFinite_separated B S hS _ _
    (isAlgebraicSpace_finiteOpenSubspacePresheaf B S hS f hsep hlft) Y.property
    (finiteOpenSubspacePresheaf B S hS f).baseMap hY
    (isLocallyQuasiFinite_of_isEtale B S hS Y.property
      (isEtale_baseMap_finiteOpenSubspacePresheaf B S hS f hsep hlft))
    (isSeparated_baseMap_finiteOpenSubspacePresheaf B S hS f hsep hflat hfp)

end AlgebraicGeometry.Space

end
