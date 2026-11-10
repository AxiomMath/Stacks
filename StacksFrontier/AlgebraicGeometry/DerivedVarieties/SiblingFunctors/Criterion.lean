module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Support.BoundedTriangle
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.Basic
public import StacksFrontier.CategoryTheory.Triangulated.PostnikovSystems
public import StacksCore.Tactic.StacksAttribute

/-!
# A criterion for two exact functors to be siblings

Two exact functors out of the bounded derived category of an abelian category `A` are siblings as
soon as their restrictions to `A` are naturally isomorphic and all negative shifted Hom groups
between the images of objects of `A` under the first functor vanish. The proof writes a bounded
object as the top stage of the Postnikov system attached to its brutal truncations, compares the
two Postnikov systems obtained by applying the two functors, and uses the vanishing to show that
the comparison on the single-degree pieces extends to the whole system.

## Main results

* `AlgebraicGeometry.areSiblings_of_restrictionIso_of_negative_ext`: the sibling criterion.

## Implementation notes

The negative Ext group in the target triangulated category is expressed as the corresponding
shifted morphism type, and its vanishing by that type being a subsingleton. The degree-zero
inclusion of the abelian category and the sibling relation are those of
`AlgebraicGeometry.boundedSingleFunctor` and `AlgebraicGeometry.AreSiblings`.

## References

* [Stacks Project, Tag 0FZU](https://stacks.math.columbia.edu/tag/0FZU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v v' u u'

namespace AlgebraicGeometry

/-- A morphism `A⟦a⟧ ⟶ B⟦b⟧` vanishes whenever all negative shifted Hom groups
from `A` to `B` vanish and `b - a < 0`. -/
private lemma shifted_hom_eq_zero
    {D : Type*} [Category* D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] {A B : D} {a b : ℤ}
    (h : ∀ (q : ℤ), q < 0 → Subsingleton (A ⟶ B⟦q⟧))
    (hab : b - a < 0) (f : A⟦a⟧ ⟶ B⟦b⟧) : f = 0 := by
  let eA := shiftFunctorCompIsoId D a (-a) (add_neg_cancel a)
  let eB := shiftFunctorAdd' D b (-a) (b - a) (by ring)
  have : Subsingleton (A ⟶ B⟦b - a⟧) := h (b - a) hab
  have hz : eA.inv.app A ≫ f⟦(-a : ℤ)⟧' ≫ (eB.inv.app B) = 0 := by
    dsimp [eA, eB, shiftFunctorCompIsoId, shiftFunctorAdd']
    exact Subsingleton.elim _ _
  have hz' : f⟦(-a : ℤ)⟧' = 0 := by
    apply (cancel_mono (eB.inv.app B)).1
    apply (cancel_epi (eA.inv.app A)).1
    simpa [Category.assoc] using hz
  exact (shiftFunctor D (-a)).map_injective (by simpa using hz')

/-- The image of a Postnikov system under an exact functor. -/
private def mapPostnikovSystem
    {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (G : C ⥤ D) [G.CommShift ℤ] [G.IsTriangulated]
    {n : ℕ} {X : Fin (n + 1) → C} {d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc}
    (S : CategoryTheory.Triangulated.PostnikovSystem X d) :
    CategoryTheory.Triangulated.PostnikovSystem (fun i => G.obj (X i))
      (fun i => G.map (d i)) where
  obj i := G.obj (S.obj i)
  π i := G.map (S.π i)
  isIso_π_zero := by infer_instance
  p i := G.map (S.p i)
  δ i := G.map (S.δ i) ≫ (G.commShiftIso (1 : ℤ)).hom.app (S.obj i.succ)
  distinguished i := by
    convert G.map_distinguished _ (S.distinguished i) using 1
    rfl
  p_comp_π i := by
    rw [← G.map_comp, S.p_comp_π]

/-- A natural isomorphism between the restrictions of two functors along `ι`, transported to
the shift of an object in the image of `ι`. -/
private def restrictionIsoOnShifted
    {A C D : Type*} [Category* A] [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ]
    (ι : A ⥤ C) (F F' : C ⥤ D) [F.CommShift ℤ] [F'.CommShift ℤ]
    (e : ι ⋙ F ≅ ι ⋙ F') (X : A) (n : ℤ) :
    F.obj ((ι.obj X)⟦n⟧) ≅ F'.obj ((ι.obj X)⟦n⟧) :=
  (F.commShiftIso n).app (ι.obj X) ≪≫
      (shiftFunctor D n).mapIso (e.app X) ≪≫
      (F'.commShiftIso n).symm.app (ι.obj X)

/-- The transported comparison commutes with morphisms between shifts of objects in the image
of a full functor `ι`. -/
private lemma restrictionIsoOnShifted_naturality
    {A C D : Type*} [Category* A] [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ]
    (ι : A ⥤ C) [ι.Full] (F F' : C ⥤ D) [F.CommShift ℤ] [F'.CommShift ℤ]
    (e : ι ⋙ F ≅ ι ⋙ F') (X Y : A) (n : ℤ)
    (f : (ι.obj X)⟦n⟧ ⟶ (ι.obj Y)⟦n⟧) :
    F.map f ≫ (restrictionIsoOnShifted ι F F' e Y n).hom =
      (restrictionIsoOnShifted ι F F' e X n).hom ≫ F'.map f := by
  obtain ⟨g, rfl⟩ := (shiftFunctor C n).map_surjective f
  obtain ⟨g₀, rfl⟩ := ι.map_surjective g
  dsimp [restrictionIsoOnShifted]
  rw [F.commShiftIso_hom_naturality_assoc]
  have hE : F.map (ι.map g₀) ≫ e.hom.app Y =
      e.hom.app X ≫ F'.map (ι.map g₀) := by
    simpa only [Functor.comp_map] using e.hom.naturality g₀
  rw [← Functor.map_comp_assoc, hE, Functor.map_comp_assoc]
  simp only [Category.assoc, F'.commShiftIso_inv_naturality]

/-- A morphism `(A⟦c⟧)⟦gap⟧ ⟶ B⟦c⟧` with `gap > 0` vanishes whenever all negative shifted Hom
groups from `A` to `B` vanish. -/
private lemma shifted_offset_hom_eq_zero
    {D : Type*} [Category* D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    {A B : D} (h : ∀ (q : ℤ), q < 0 → Subsingleton (A ⟶ B⟦q⟧))
    (c gap : ℤ) (hgap : 0 < gap)
    (u : (A⟦c⟧)⟦gap⟧ ⟶ B⟦c⟧) : u = 0 := by
  let e := shiftFunctorAdd' D c gap (c + gap) rfl
  have hz := shifted_hom_eq_zero h (by omega) (e.hom.app A ≫ u)
  apply (cancel_epi (e.hom.app A)).1
  simpa using hz

/-- For a complex that is strictly bounded below by `lo`, the inclusion of its brutal truncation
in degrees `≥ lo` is an isomorphism. -/
private lemma brutalTail_inclusion_isIso_of_strictlyGE
    {A : Type u} [Category.{v} A] [Abelian A]
    (C : CochainComplex A ℤ) (lo : ℤ) (hlo : C.IsStrictlyGE lo) :
    IsIso (HomologicalComplex.ιStupidTrunc C (ComplexShape.embeddingUpIntGE lo)) := by
  have hcomp : ∀ n, IsIso
      ((HomologicalComplex.ιStupidTrunc C
        (ComplexShape.embeddingUpIntGE lo)).f n) := by
    intro n
    by_cases hn : lo ≤ n
    · rw [StacksDraft.StupidTruncation.ιStupidTruncGE_f C lo n hn]
      infer_instance
    · have hn' : n < lo := by omega
      have hC : IsZero (C.X n) := CochainComplex.isZero_of_isStrictlyGE C lo n hn'
      have hT : IsZero ((C.stupidTrunc (ComplexShape.embeddingUpIntGE lo)).X n) :=
        CochainComplex.isZero_of_isStrictlyGE
          (C.stupidTrunc (ComplexShape.embeddingUpIntGE lo)) lo n hn'
      exact IsZero.isIso hT hC _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Every object of the bounded derived category is represented by a strictly bounded complex. -/
private lemma exists_truncatedRepresentative
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory.Bounded A) :
    ∃ (lo hi : ℤ) (C : CochainComplex A ℤ), C.IsStrictlyGE lo ∧ C.IsStrictlyLE hi ∧
      Nonempty (DerivedCategory.Q.obj C ≅ K.obj) := by
  rcases K.property with ⟨⟨lo, hlo⟩, ⟨hi, hhi⟩⟩
  let t := DerivedCategory.TStructure.t (C := A)
  let C₀ := DerivedCategory.Q.objPreimage K.obj
  have : t.IsGE K.obj lo := hlo
  have : t.IsLE K.obj hi := hhi
  have hge₀ : (DerivedCategory.Q.obj C₀).IsGE lo :=
    t.isGE_of_iso (DerivedCategory.Q.objObjPreimageIso K.obj).symm lo
  have hle₀ : (DerivedCategory.Q.obj C₀).IsLE hi :=
    t.isLE_of_iso (DerivedCategory.Q.objObjPreimageIso K.obj).symm hi
  let C₁ := C₀.truncGE lo
  have h₁ : IsIso (DerivedCategory.Q.map (C₀.πTruncGE lo)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_πTruncGE_iff]
    exact (DerivedCategory.isGE_Q_obj_iff C₀ lo).1 hge₀
  let e₁ : DerivedCategory.Q.obj C₀ ≅ DerivedCategory.Q.obj C₁ :=
    asIso (DerivedCategory.Q.map (C₀.πTruncGE lo))
  have hle₁ : (DerivedCategory.Q.obj C₁).IsLE hi := t.isLE_of_iso e₁ hi
  let C₂ := C₁.truncLE hi
  have h₂ : IsIso (DerivedCategory.Q.map (C₁.ιTruncLE hi)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_ιTruncLE_iff]
    exact (DerivedCategory.isLE_Q_obj_iff C₁ hi).1 hle₁
  let e₂ : DerivedCategory.Q.obj C₂ ≅ DerivedCategory.Q.obj C₁ :=
    asIso (DerivedCategory.Q.map (C₁.ιTruncLE hi))
  refine ⟨lo, hi, C₂, inferInstance, inferInstance, ⟨e₂ ≪≫ e₁.symm ≪≫
    DerivedCategory.Q.objObjPreimageIso K.obj⟩⟩

/-- A strictly bounded complex, regarded as an object of the bounded derived category. -/
private noncomputable def boundedQObj
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi : ℤ)
    (hlo : C.IsStrictlyGE lo) (hhi : C.IsStrictlyLE hi) : DerivedCategory.Bounded A := by
  letI := hlo
  letI := hhi
  have hge : (DerivedCategory.Q.obj C).IsGE lo :=
    (DerivedCategory.isGE_Q_obj_iff C lo).2 (by infer_instance)
  have hle : (DerivedCategory.Q.obj C).IsLE hi :=
    (DerivedCategory.isLE_Q_obj_iff C hi).2 (by infer_instance)
  exact ⟨DerivedCategory.Q.obj C, ⟨⟨lo, hge⟩, ⟨hi, hle⟩⟩⟩

/-- The brutal (stupid) truncation of a complex in degrees `≥ p`. -/
private noncomputable abbrev brutalTail
    {A : Type u} [Category.{v} A] [Abelian A] (C : CochainComplex A ℤ) (p : ℤ) :=
  C.stupidTrunc (ComplexShape.embeddingUpIntGE p)

/-- The brutal truncation in degrees `≥ p` of a strictly bounded complex, as a bounded derived
object. -/
private noncomputable def boundedTailObj
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi p : ℤ) (_hlo : C.IsStrictlyGE lo)
    (hhi : C.IsStrictlyLE hi) (_hp : lo ≤ p) : DerivedCategory.Bounded A := by
  have hge : CochainComplex.IsStrictlyGE (brutalTail C p) p := by infer_instance
  have hle : CochainComplex.IsStrictlyLE (brutalTail C p) hi := by
    have := hhi
    infer_instance
  exact boundedQObj (brutalTail C p) p hi hge hle

/-- An object of the abelian category placed in degree `p`, as a bounded derived object. -/
private noncomputable def boundedSingleObj
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (X : A) (p : ℤ) : DerivedCategory.Bounded A :=
  boundedQObj ((CochainComplex.singleFunctor A p).obj X) p p (by infer_instance)
    (by infer_instance)

/-- The triangle of the bounded derived category coming from the short exact sequence relating
consecutive brutal truncations of a complex. -/
private noncomputable def boundedTailSESTriangle
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi p : ℤ)
    (hlo : C.IsStrictlyGE lo) (hhi : C.IsStrictlyLE hi)
    (hp : lo ≤ p) (_hp' : p + 1 ≤ hi) : Triangle (DerivedCategory.Bounded A) := by
  let S := StacksDraft.StupidTruncation.stupidTruncGEShortComplex C p
  have hS : S.ShortExact := StacksDraft.StupidTruncation.stupidTruncGEShortComplex_shortExact C p
  let T := DerivedCategory.triangleOfSES hS
  let T₁ := boundedTailObj C lo hi (p + 1) hlo hhi (by omega)
  let T₂ := boundedTailObj C lo hi p hlo hhi hp
  let T₃ := boundedSingleObj (C.X p) p
  exact liftBoundedTriangle T T₁.property T₂.property T₃.property

/-- The triangle relating consecutive brutal truncations is distinguished. -/
private lemma boundedTailSESTriangle_distinguished
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi p : ℤ)
    (hlo : C.IsStrictlyGE lo) (hhi : C.IsStrictlyLE hi)
    (hp : lo ≤ p) (hp' : p + 1 ≤ hi) :
    boundedTailSESTriangle C lo hi p hlo hhi hp hp' ∈
      distTriang (DerivedCategory.Bounded A) :=
  liftBoundedTriangle_distinguished _ _ _ _ (DerivedCategory.triangleOfSES_distinguished
    (StacksDraft.StupidTruncation.stupidTruncGEShortComplex_shortExact C p))

/-- A shift of a degree-`p` object, normalised to the shift by `c` of the corresponding
degree-zero object. -/
private noncomputable def factorNormalizeIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (X : A) (p s c : ℤ) (h : -p + s = c) :
    (boundedSingleObj X p)⟦s⟧ ≅ ((boundedSingleFunctor A).obj X)⟦c⟧ :=
  ObjectProperty.isoMk _ <|
    (DerivedCategory.Bounded.ι.commShiftIso s).app (boundedSingleObj X p) ≪≫
      ((shiftFunctor (DerivedCategory A) s).mapIso
        (((DerivedCategory.singleFunctors A).shiftIso (-p) p 0 (by omega)).app X).symm ≪≫
        ((shiftFunctorAdd' (DerivedCategory A) (-p) s c h).app
          ((DerivedCategory.singleFunctor A 0).obj X)).symm) ≪≫
      (DerivedCategory.Bounded.ι.commShiftIso c).symm.app
        ((boundedSingleFunctor A).obj X)

/-- The `k`-fold iterate of the shift by one. -/
private noncomputable def iterShift
    {D : Type*} [Category* D] [HasShift D ℤ] (k : ℕ) (X : D) : D :=
  Nat.rec X (fun _ Y => Y⟦(1 : ℤ)⟧) k

/-- The `k`-fold iterate of the shift by one, applied to a morphism. -/
private def iterShiftMap
    {D : Type*} [Category* D] [HasShift D ℤ] (k : ℕ) {X Y : D} (f : X ⟶ Y) :
    iterShift k X ⟶ iterShift k Y :=
  Nat.rec f (fun _ g => g⟦(1 : ℤ)⟧') k

/-- The `k`-fold iterate of the shift by one, applied to an isomorphism. -/
private noncomputable def iterShiftIso
    {D : Type*} [Category* D] [HasShift D ℤ] (k : ℕ) {X Y : D} (e : X ≅ Y) :
    iterShift k X ≅ iterShift k Y :=
  Nat.rec e (fun _ i => (shiftFunctor D (1 : ℤ)).mapIso i) k

/-- The iterated shift of an isomorphism is an isomorphism. -/
private lemma iterShiftMap_isIso
    {D : Type*} [Category* D] [HasShift D ℤ] (k : ℕ) {X Y : D}
    (f : X ⟶ Y) [IsIso f] : IsIso (iterShiftMap k f) := by
  induction k with
  | zero => simpa [iterShiftMap]
  | succ k ih =>
    change IsIso ((iterShiftMap k f)⟦(1 : ℤ)⟧')
    infer_instance

/-- Iterating the shift `k` times on `X⟦1⟧` is iterating it `k + 1` times on `X`. -/
private lemma iterShift_shift
    {D : Type*} [Category* D] [HasShift D ℤ] (k : ℕ) (X : D) :
    iterShift k (X⟦(1 : ℤ)⟧) = iterShift (k + 1) X := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (iterShift k (X⟦(1 : ℤ)⟧))⟦(1 : ℤ)⟧ =
      (iterShift (k + 1) X)⟦(1 : ℤ)⟧
    exact congrArg (fun Y : D => Y⟦(1 : ℤ)⟧) ih

/-- The `k`-fold iterate of the shift by one agrees with the shift by `k`. -/
private noncomputable def iterShiftToShiftIso
    {D : Type*} [Category* D] [HasShift D ℤ] (k : ℕ) (X : D) :
  iterShift k X ≅ X⟦(k : ℤ)⟧ := by
  induction k with
  | zero => simpa [iterShift] using ((shiftFunctorZero D ℤ).app X).symm
  | succ k ih =>
    change (iterShift k X)⟦(1 : ℤ)⟧ ≅ X⟦((k : ℤ) + 1)⟧
    exact (shiftFunctor D (1 : ℤ)).mapIso ih ≪≫
      ((shiftFunctorAdd' D (k : ℤ) 1 ((k : ℤ) + 1) rfl).app X).symm

/-- The `k`-fold iterate of the shift by one, applied to a triangle. -/
private noncomputable def iterShiftTriangle
    {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    (k : ℕ) (T : Triangle D) : Triangle D :=
  Nat.rec T (fun _ U => (Triangle.shiftFunctor D (1 : ℤ)).obj U) k

/-- The first vertex of an iterated shift of a triangle is the iterated shift of its
first vertex. -/
private lemma iterShiftTriangle_obj₁
    {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    (k : ℕ) (T : Triangle D) :
    (iterShiftTriangle k T).obj₁ = iterShift k T.obj₁ := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun Y : D => Y⟦(1 : ℤ)⟧) ih

/-- The second vertex of an iterated shift of a triangle is the iterated shift of its
second vertex. -/
private lemma iterShiftTriangle_obj₂
    {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    (k : ℕ) (T : Triangle D) :
    (iterShiftTriangle k T).obj₂ = iterShift k T.obj₂ := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun Y : D => Y⟦(1 : ℤ)⟧) ih

/-- The third vertex of an iterated shift of a triangle is the iterated shift of its
third vertex. -/
private lemma iterShiftTriangle_obj₃
    {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    (k : ℕ) (T : Triangle D) :
    (iterShiftTriangle k T).obj₃ = iterShift k T.obj₃ := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun Y : D => Y⟦(1 : ℤ)⟧) ih

/-- The degree `hi - i` indexed in reverse by `i : Fin (n + 1)`. -/
private def revDegree (hi : ℤ) {n : ℕ} (i : Fin (n + 1)) : ℤ := hi - (i.val : ℤ)

/-- The number `n - i` of shifts applied at the reverse index `i : Fin (n + 1)`. -/
private def revShift {n : ℕ} (i : Fin (n + 1)) : ℕ := n - i.val

/-- The projection of a brutal truncation onto its top term, as a map of bounded derived
objects. -/
private noncomputable def boundedTailProjection
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi p : ℤ)
    (hlo : C.IsStrictlyGE lo) (hhi : C.IsStrictlyLE hi) (hp : lo ≤ p) :
    boundedTailObj C lo hi p hlo hhi hp ⟶ boundedSingleObj (C.X p) p :=
  ObjectProperty.homMk (DerivedCategory.Q.map (StacksDraft.StupidTruncation.stupidTruncGEπ C p))

/-- For a complex strictly bounded above by `hi`, the projection of its brutal truncation in
degrees `≥ hi` onto its degree-`hi` term is an isomorphism. -/
private lemma stupidTruncGEπ_isIso_at_top
    {A : Type u} [Category.{v} A] [Abelian A]
    (C : CochainComplex A ℤ) (hi : ℤ) (hhi : C.IsStrictlyLE hi) :
    IsIso (StacksDraft.StupidTruncation.stupidTruncGEπ C hi) := by
  have hcomp : ∀ n, IsIso ((StacksDraft.StupidTruncation.stupidTruncGEπ C hi).f n) := by
    intro n
    by_cases hn : n = hi
    · subst n
      rw [StacksDraft.StupidTruncation.stupidTruncGEπ_f]
      infer_instance
    · have hs : IsZero ((brutalTail C hi).X n) := by
        by_cases hlt : n < hi
        · exact CochainComplex.isZero_of_isStrictlyGE
            (brutalTail C hi) hi n (by omega)
        · have := hhi
          exact CochainComplex.isZero_of_isStrictlyLE (brutalTail C hi) hi n (by omega)
      have ht : IsZero (((CochainComplex.singleFunctor A hi).obj (C.X hi)).X n) :=
        HomologicalComplex.isZero_single_obj_X (.up ℤ) hi (C.X hi) n (by omega)
      exact IsZero.isIso hs ht _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- At the top degree, the projection of a brutal truncation onto its top term is an
isomorphism of bounded derived objects. -/
private lemma boundedTailProjection_isIso_at_top
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi : ℤ)
    (hlo : C.IsStrictlyGE lo) (hhi : C.IsStrictlyLE hi)
    (hp : lo ≤ hi) : IsIso (boundedTailProjection C lo hi hi hlo hhi hp) := by
  have : IsIso (StacksDraft.StupidTruncation.stupidTruncGEπ C hi) :=
    stupidTruncGEπ_isIso_at_top C hi hhi
  apply (ObjectProperty.isIso_hom_iff (boundedTailProjection C lo hi hi hlo hhi hp)).1
  change IsIso (DerivedCategory.Q.map
    (StacksDraft.StupidTruncation.stupidTruncGEπ C hi))
  infer_instance

/-- The projection of a brutal truncation onto its top term is an isomorphism whenever the
truncation degree equals the top degree. -/
private lemma boundedTailProjection_isIso_of_eq_top
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi p : ℤ)
    (hlo : C.IsStrictlyGE lo) (hhi : C.IsStrictlyLE hi)
    (hp : lo ≤ p) (hpi : p = hi) :
    IsIso (boundedTailProjection C lo hi p hlo hhi hp) := by
  cases hpi
  exact boundedTailProjection_isIso_at_top C lo hi hlo hhi hp

/-- The second vertex of the rotation of the truncation triangle is the degree-`p` term of the
complex. -/
private noncomputable def boundedTailSESRotSecondIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi p : ℤ)
    (hlo : C.IsStrictlyGE lo) (hhi : C.IsStrictlyLE hi)
    (hp : lo ≤ p) (hp' : p + 1 ≤ hi) :
    (boundedTailSESTriangle C lo hi p hlo hhi hp hp').rotate.obj₂ ≅
      boundedSingleObj (C.X p) p := by
  apply ObjectProperty.isoMk
  dsimp [boundedTailSESTriangle, liftBoundedTriangle, DerivedCategory.triangleOfSES,
    boundedSingleObj, boundedQObj, StacksDraft.StupidTruncation.stupidTruncGEShortComplex]
  rfl

/-- The rotated truncation triangle at the reverse index `i`, shifted so that its vertices match
the Postnikov system being built. -/
private noncomputable def boundedTailRotShiftTriangle
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi : ℤ) (n : ℕ)
    (hlo : C.IsStrictlyGE lo) (hhi : C.IsStrictlyLE hi)
    (hlen : (n : ℤ) = hi - lo) (i : Fin n) : Triangle (DerivedCategory.Bounded A) := by
  let p := revDegree hi i.succ
  have hp : lo ≤ p := by dsimp [p, revDegree]; omega
  have hp' : p + 1 ≤ hi := by dsimp [p, revDegree]; omega
  exact iterShiftTriangle (revShift i.succ)
    (boundedTailSESTriangle C lo hi p hlo hhi hp hp').rotate

/-- An iterated shift of a distinguished triangle is distinguished. -/
private lemma iterShiftTriangle_distinguished
    {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (k : ℕ) (T : Triangle D) (hT : T ∈ distTriang D) :
    iterShiftTriangle k T ∈ distTriang D := by
  induction k with
  | zero => exact hT
  | succ k ih =>
    change (Triangle.shiftFunctor D 1).obj (iterShiftTriangle k T) ∈ _
    exact Triangle.shift_distinguished _ ih 1

/-- The shifted rotated truncation triangle is distinguished. -/
private lemma boundedTailRotShiftTriangle_distinguished
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi : ℤ) (n : ℕ)
    (hlo : C.IsStrictlyGE lo) (hhi : C.IsStrictlyLE hi)
    (hlen : (n : ℤ) = hi - lo) (i : Fin n) :
    boundedTailRotShiftTriangle C lo hi n hlo hhi hlen i ∈
      distTriang (DerivedCategory.Bounded A) := by
  dsimp [boundedTailRotShiftTriangle]
  let p := revDegree hi i.succ
  have hp : lo ≤ p := by dsimp [p, revDegree]; omega
  have hp' : p + 1 ≤ hi := by dsimp [p, revDegree]; omega
  exact iterShiftTriangle_distinguished _ _
    (rot_of_distTriang _ (boundedTailSESTriangle_distinguished C lo hi p hlo hhi hp hp'))

/-- Identifications of the three vertices of the shifted rotated truncation triangle with the
iterated shifts of the truncations and of the single-degree terms. -/
private noncomputable def boundedTailComplexDifferential
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi : ℤ) (n : ℕ)
    (hlo : C.IsStrictlyGE lo) (hhi : C.IsStrictlyLE hi)
    (hlen : (n : ℤ) = hi - lo) :
    ∀ i : Fin n,
      ((boundedTailRotShiftTriangle C lo hi n hlo hhi hlen i).obj₁ ≅
        iterShift (revShift i.succ)
          (boundedTailObj C lo hi (revDegree hi i.succ) hlo hhi (by dsimp [revDegree]; omega))) ×
      ((boundedTailRotShiftTriangle C lo hi n hlo hhi hlen i).obj₂ ≅
        iterShift (revShift i.succ)
          (boundedSingleObj (C.X (revDegree hi i.succ)) (revDegree hi i.succ))) ×
      ((boundedTailRotShiftTriangle C lo hi n hlo hhi hlen i).obj₃ ≅
        iterShift (revShift i.castSucc)
          (boundedTailObj C lo hi (revDegree hi i.castSucc) hlo hhi
            (by dsimp [revDegree]; omega))) := by
  intro i
  let T := boundedTailRotShiftTriangle C lo hi n hlo hhi hlen i
  let p := revDegree hi i.succ
  let k := revShift i.succ
  let T₀ := (boundedTailSESTriangle C lo hi p hlo hhi
    (by dsimp [p, revDegree]; omega) (by dsimp [p, revDegree]; omega)).rotate
  have e₁ : T.obj₁ ≅ iterShift (revShift i.succ)
      (boundedTailObj C lo hi (revDegree hi i.succ) hlo hhi (by dsimp [revDegree]; omega)) := by
    change (iterShiftTriangle k T₀).obj₁ ≅ _
    rw [iterShiftTriangle_obj₁, Triangle.rotate_obj₁]
    rfl
  have e₂ : T.obj₂ ≅ iterShift (revShift i.succ)
      (boundedSingleObj (C.X (revDegree hi i.succ)) (revDegree hi i.succ)) := by
    change (iterShiftTriangle k T₀).obj₂ ≅ _
    rw [iterShiftTriangle_obj₂, Triangle.rotate_obj₂]
    exact iterShiftIso k (boundedTailSESRotSecondIso C lo hi p hlo hhi
      (by dsimp [p, revDegree]; omega) (by dsimp [p, revDegree]; omega))
  have e₃ : T.obj₃ ≅ iterShift (revShift i.castSucc)
      (boundedTailObj C lo hi (revDegree hi i.castSucc) hlo hhi (by
        dsimp [revDegree]; omega)) := by
    have hp : p + 1 = revDegree hi i.castSucc := by
      change (hi - ((i.val : ℤ) + 1)) + 1 = hi - (i.val : ℤ)
      omega
    have hk : k + 1 = revShift i.castSucc := by
      change n - (i.val + 1) + 1 = n - i.val
      omega
    have hlow : lo ≤ p + 1 := by
      dsimp [p, revDegree]
      omega
    have ebase : T₀.obj₃ ≅
        (boundedTailObj C lo hi (p + 1) hlo hhi hlow)⟦(1 : ℤ)⟧ := by
      dsimp [T₀]
      rw [Triangle.rotate_obj₃]
      rfl
    have heq : iterShift k ((boundedTailObj C lo hi (p + 1) hlo hhi hlow)⟦(1 : ℤ)⟧) =
        iterShift (revShift i.castSucc)
          (boundedTailObj C lo hi (revDegree hi i.castSucc) hlo hhi (by
            dsimp [revDegree]; omega)) := by
      rw [iterShift_shift, hk]
      simp only [hp]
    change (iterShiftTriangle k T₀).obj₃ ≅ _
    rw [iterShiftTriangle_obj₃]
    exact iterShiftIso k ebase ≪≫ eqToIso heq
  exact ⟨e₁, e₂, e₃⟩

/-- The map `pᵢ` of the Postnikov system, read off the shifted rotated truncation triangle. -/
private noncomputable def boundedTailStageP
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi : ℤ) (n : ℕ)
    (hlo : C.IsStrictlyGE lo) (hhi : C.IsStrictlyLE hi)
    (hlen : (n : ℤ) = hi - lo) (i : Fin n) :
    iterShift (revShift i.succ)
      (boundedSingleObj (C.X (revDegree hi i.succ)) (revDegree hi i.succ)) ⟶
    iterShift (revShift i.castSucc)
      (boundedTailObj C lo hi (revDegree hi i.castSucc) hlo hhi (by dsimp [revDegree]; omega)) := by
  let T := boundedTailRotShiftTriangle C lo hi n hlo hhi hlen i
  let E := boundedTailComplexDifferential C lo hi n hlo hhi hlen i
  exact E.2.1.inv ≫ T.mor₂ ≫ E.2.2.hom

/-- The map `πᵢ` of the Postnikov system at a successor index, read off the shifted rotated
truncation triangle. -/
private noncomputable def boundedTailStagePi
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi : ℤ) (n : ℕ)
    (hlo : C.IsStrictlyGE lo) (hhi : C.IsStrictlyLE hi)
    (hlen : (n : ℤ) = hi - lo) (i : Fin n) :
    iterShift (revShift i.succ)
      (boundedTailObj C lo hi (revDegree hi i.succ) hlo hhi (by dsimp [revDegree]; omega)) ⟶
    iterShift (revShift i.succ)
      (boundedSingleObj (C.X (revDegree hi i.succ)) (revDegree hi i.succ)) := by
  let T := boundedTailRotShiftTriangle C lo hi n hlo hhi hlen i
  let E := boundedTailComplexDifferential C lo hi n hlo hhi hlen i
  exact E.1.inv ≫ T.mor₁ ≫ E.2.1.hom

/-- The connecting map `δᵢ` of the Postnikov system, read off the shifted rotated truncation
triangle. -/
private noncomputable def boundedTailStageDelta
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi : ℤ) (n : ℕ)
    (hlo : C.IsStrictlyGE lo) (hhi : C.IsStrictlyLE hi)
    (hlen : (n : ℤ) = hi - lo) (i : Fin n) :
    iterShift (revShift i.castSucc)
      (boundedTailObj C lo hi (revDegree hi i.castSucc) hlo hhi (by dsimp [revDegree]; omega)) ⟶
    (iterShift (revShift i.succ)
      (boundedTailObj C lo hi (revDegree hi i.succ) hlo hhi
        (by dsimp [revDegree]; omega)))⟦(1 : ℤ)⟧ := by
  let T := boundedTailRotShiftTriangle C lo hi n hlo hhi hlen i
  let E := boundedTailComplexDifferential C lo hi n hlo hhi hlen i
  exact E.2.2.inv ≫ T.mor₃ ≫ (shiftFunctor (DerivedCategory.Bounded A) 1).map E.1.hom

/-- The maps `πᵢ` of the Postnikov system at every index, the zeroth one being the shifted top
projection. -/
private noncomputable def boundedTailSystemPi
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi : ℤ) (n : ℕ)
    (hlo : C.IsStrictlyGE lo) (hhi : C.IsStrictlyLE hi)
    (hlen : (n : ℤ) = hi - lo) :
    ∀ i : Fin (n + 1),
      iterShift (revShift i)
        (boundedTailObj C lo hi (revDegree hi i) hlo hhi (by dsimp [revDegree]; omega)) ⟶
      iterShift (revShift i)
        (boundedSingleObj (C.X (revDegree hi i)) (revDegree hi i)) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · exact iterShiftMap (revShift (0 : Fin (n + 1)))
      (boundedTailProjection C lo hi (revDegree hi (n := n) 0) hlo hhi
        (by dsimp [revDegree]; omega))
  · exact boundedTailStagePi C lo hi n hlo hhi hlen

/-- The differential of the complex of single-degree terms whose Postnikov system computes the
bounded object. -/
private noncomputable def boundedTailComplexDifferentialMap
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi : ℤ) (n : ℕ)
    (hlo : C.IsStrictlyGE lo) (hhi : C.IsStrictlyLE hi)
    (hlen : (n : ℤ) = hi - lo) :
    ∀ i : Fin n,
      iterShift (revShift i.succ)
        (boundedSingleObj (C.X (revDegree hi i.succ)) (revDegree hi i.succ)) ⟶
      iterShift (revShift i.castSucc)
        (boundedSingleObj (C.X (revDegree hi i.castSucc)) (revDegree hi i.castSucc)) :=
  fun i => boundedTailStageP C lo hi n hlo hhi hlen i ≫
    boundedTailSystemPi C lo hi n hlo hhi hlen i.castSucc

/-- The Postnikov system of a strictly bounded complex, with the iterated shifts of its
single-degree terms as the graded pieces and its brutal truncations as the stages. -/
private noncomputable def boundedTailPostnikov
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi : ℤ) (n : ℕ)
    (hlo : C.IsStrictlyGE lo) (hhi : C.IsStrictlyLE hi)
    (hlen : (n : ℤ) = hi - lo) :
    CategoryTheory.Triangulated.PostnikovSystem
      (fun i : Fin (n + 1) =>
        iterShift (revShift i) (boundedSingleObj (C.X (revDegree hi i)) (revDegree hi i)))
      (boundedTailComplexDifferentialMap C lo hi n hlo hhi hlen) := by
  let X := fun i : Fin (n + 1) =>
    iterShift (revShift i) (boundedSingleObj (C.X (revDegree hi i)) (revDegree hi i))
  let d := boundedTailComplexDifferentialMap C lo hi n hlo hhi hlen
  change CategoryTheory.Triangulated.PostnikovSystem X d
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact iterShift (revShift i)
      (boundedTailObj C lo hi (revDegree hi i) hlo hhi (by dsimp [revDegree]; omega))
  · exact boundedTailSystemPi C lo hi n hlo hhi hlen
  · let p := revDegree hi (0 : Fin (n + 1))
    have hp : lo ≤ p := by dsimp [p, revDegree]; omega
    have := boundedTailProjection_isIso_of_eq_top C lo hi p hlo hhi hp
      (by dsimp [p, revDegree]; simp)
    exact iterShiftMap_isIso (revShift (0 : Fin (n + 1)))
      (boundedTailProjection C lo hi p hlo hhi hp)
  · exact boundedTailStageP C lo hi n hlo hhi hlen
  · exact boundedTailStageDelta C lo hi n hlo hhi hlen
  · intro i
    let T := boundedTailRotShiftTriangle C lo hi n hlo hhi hlen i
    let E := boundedTailComplexDifferential C lo hi n hlo hhi hlen i
    let T' := Triangle.mk (boundedTailSystemPi C lo hi n hlo hhi hlen i.succ)
      (boundedTailStageP C lo hi n hlo hhi hlen i)
      (boundedTailStageDelta C lo hi n hlo hhi hlen i)
    refine isomorphic_distinguished T
      (boundedTailRotShiftTriangle_distinguished C lo hi n hlo hhi hlen i) T'
      (Triangle.isoMk T T' E.1 E.2.1 E.2.2 ?_ ?_ ?_).symm
    · simp [T', boundedTailSystemPi, boundedTailStagePi, E]
      rfl
    · simp [T', boundedTailStageP, E]
      rfl
    · simp [T', boundedTailStageDelta, E]
      rfl
  · exact fun _ => rfl

/-- The `i`-th graded piece of the Postnikov system of a bounded complex, identified with the
shift by `-lo` of a degree-zero object. -/
private noncomputable def boundedTailPieceIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi : ℤ) (n : ℕ) (hlen : (n : ℤ) = hi - lo) (i : Fin (n + 1)) :
    iterShift (revShift i) (boundedSingleObj (C.X (revDegree hi i)) (revDegree hi i)) ≅
      ((boundedSingleFunctor A).obj (C.X (revDegree hi i)))⟦(-lo : ℤ)⟧ :=
  iterShiftToShiftIso (revShift i) (boundedSingleObj (C.X (revDegree hi i)) (revDegree hi i)) ≪≫
    factorNormalizeIso (C.X (revDegree hi i)) (revDegree hi i) (revShift i) (-lo)
      (by dsimp [revDegree, revShift]; omega)

/-- Under the vanishing of negative Ext groups, the morphisms between the images of the graded
pieces of the Postnikov system of a bounded complex that obstruct comparing systems vanish. -/
private lemma boundedTailPiece_hom_eq_zero
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {D : Type*} [Category* D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (F : DerivedCategory.Bounded A ⥤ D) [F.CommShift ℤ]
    (h_negative : ∀ (X Y : A) (q : ℤ), q < 0 →
      Subsingleton
        (F.obj ((boundedSingleFunctor A).obj X) ⟶
          (F.obj ((boundedSingleFunctor A).obj Y))⟦q⟧))
    (C : CochainComplex A ℤ) (lo hi : ℤ) (n : ℕ) (hlen : (n : ℤ) = hi - lo)
    (i j : Fin (n + 1)) (hij : (j : ℕ) + 1 < (i : ℕ))
    (u : (F.obj (iterShift (revShift i)
        (boundedSingleObj (C.X (revDegree hi i)) (revDegree hi i))))⟦((i : ℕ) : ℤ) -
          ((j : ℕ) : ℤ) - 1⟧ ⟶
      F.obj (iterShift (revShift j) (boundedSingleObj (C.X (revDegree hi j)) (revDegree hi j)))) :
    u = 0 := by
  let gap : ℤ := (i : ℕ) - (j : ℕ) - 1
  have hgap : 0 < gap := by dsimp [gap]; omega
  let β (k : Fin (n + 1)) : F.obj (iterShift (revShift k)
      (boundedSingleObj (C.X (revDegree hi k)) (revDegree hi k))) ≅
      (F.obj ((boundedSingleFunctor A).obj (C.X (revDegree hi k))))⟦(-lo : ℤ)⟧ :=
    F.mapIso (boundedTailPieceIso C lo hi n hlen k) ≪≫
      (F.commShiftIso (-lo)).app ((boundedSingleFunctor A).obj (C.X (revDegree hi k)))
  apply (cancel_epi ((shiftFunctor D gap).map (β i).inv)).1
  apply (cancel_mono (β j).hom).1
  simpa [Category.assoc] using shifted_offset_hom_eq_zero
    (h_negative _ _) (-lo) gap hgap ((shiftFunctor D gap).map (β i).inv ≫ u ≫ (β j).hom)

/-- The comparison between the images under `F` and `F'` of the graded pieces of the Postnikov
system of a bounded complex, induced by an isomorphism of their restrictions. -/
private noncomputable def boundedTailPieceComparison
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {D : Type*} [Category* D] [HasShift D ℤ]
    (F F' : DerivedCategory.Bounded A ⥤ D) [F.CommShift ℤ] [F'.CommShift ℤ]
    (e : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ F')
    (C : CochainComplex A ℤ) (lo hi : ℤ) (n : ℕ) (hlen : (n : ℤ) = hi - lo) (i : Fin (n + 1)) :
    F.obj (iterShift (revShift i) (boundedSingleObj (C.X (revDegree hi i)) (revDegree hi i))) ≅
      F'.obj (iterShift (revShift i) (boundedSingleObj (C.X (revDegree hi i)) (revDegree hi i))) :=
  F.mapIso (boundedTailPieceIso C lo hi n hlen i) ≪≫
    restrictionIsoOnShifted (boundedSingleFunctor A) F F' e (C.X (revDegree hi i)) (-lo) ≪≫
    (F'.mapIso (boundedTailPieceIso C lo hi n hlen i)).symm

/-- The comparison of graded pieces commutes with the differentials of the complex of
single-degree terms. -/
private lemma boundedTailPieceComparison_comm
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {D : Type*} [Category* D] [HasShift D ℤ]
    (F F' : DerivedCategory.Bounded A ⥤ D) [F.CommShift ℤ] [F'.CommShift ℤ]
    (e : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ F')
    (C : CochainComplex A ℤ) (lo hi : ℤ) (n : ℕ)
    (hlo : C.IsStrictlyGE lo) (hhi : C.IsStrictlyLE hi) (hlen : (n : ℤ) = hi - lo) (i : Fin n) :
    F.map (boundedTailComplexDifferentialMap C lo hi n hlo hhi hlen i) ≫
        (boundedTailPieceComparison F F' e C lo hi n hlen i.castSucc).hom =
      (boundedTailPieceComparison F F' e C lo hi n hlen i.succ).hom ≫
        F'.map (boundedTailComplexDifferentialMap C lo hi n hlo hhi hlen i) := by
  have : (boundedSingleFunctor A).Full :=
    Functor.Full.of_comp_faithful_iso (boundedSingleFunctorCompιIso A)
  have hmain := congrArg
    (fun f => F.map (boundedTailPieceIso C lo hi n hlen i.succ).hom ≫ f ≫
      F'.map (boundedTailPieceIso C lo hi n hlen i.castSucc).inv)
    (restrictionIsoOnShifted_naturality (boundedSingleFunctor A) F F' e
      (C.X (revDegree hi i.succ)) (C.X (revDegree hi i.castSucc)) (-lo)
      ((boundedTailPieceIso C lo hi n hlen i.succ).inv ≫
        boundedTailComplexDifferentialMap C lo hi n hlo hhi hlen i ≫
          (boundedTailPieceIso C lo hi n hlen i.castSucc).hom))
  simpa [boundedTailPieceComparison, Category.assoc] using hmain

/-- The last stage of the Postnikov system of a strictly bounded complex is the complex itself. -/
private noncomputable def boundedTailPostnikovLastIso
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (C : CochainComplex A ℤ) (lo hi : ℤ) (n : ℕ)
    (hlo : C.IsStrictlyGE lo) (hhi : C.IsStrictlyLE hi) (hlen : (n : ℤ) = hi - lo) :
    (boundedTailPostnikov C lo hi n hlo hhi hlen).obj (Fin.last n) ≅
      boundedQObj C lo hi hlo hhi :=
  have hlast : revDegree hi (Fin.last n) = lo := by
    dsimp [revDegree]
    rw [hlen]
    simp
  have hshift : revShift (Fin.last n) = 0 := by simp [revShift]
  haveI := brutalTail_inclusion_isIso_of_strictlyGE C lo hlo
  (eqToIso (by simp [boundedTailPostnikov, hlast, hshift, iterShift]) :
      (boundedTailPostnikov C lo hi n hlo hhi hlen).obj (Fin.last n) ≅
        boundedTailObj C lo hi lo hlo hhi le_rfl) ≪≫
    ObjectProperty.isoMk _ (DerivedCategory.Q.mapIso
      (asIso (HomologicalComplex.ιStupidTrunc C (ComplexShape.embeddingUpIntGE lo))))

/-- **Stacks Project, Tag 0FZU.** Exact functors from the bounded derived category of an
abelian category are siblings if their restrictions to the abelian category are naturally
isomorphic and all negative Ext groups between images of objects of the abelian category under
the first functor vanish. -/
@[stacks 0FZU]
public lemma areSiblings_of_restrictionIso_of_negative_ext
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [IsTriangulated D]
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (h_restriction : Nonempty
      (boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ F'))
    (h_negative : ∀ (X Y : A) (q : ℤ), q < 0 →
      Subsingleton
        (F.obj ((boundedSingleFunctor A).obj X) ⟶
          (F.obj ((boundedSingleFunctor A).obj Y))⟦q⟧)) :
    AreSiblings F F' := by
  refine ⟨h_restriction, fun K => ?_⟩
  obtain ⟨lo, hi₀, C, hlo, hhi₀, ⟨eK⟩⟩ := exists_truncatedRepresentative K
  let hi := max hi₀ lo
  have hhi : C.IsStrictlyLE hi := by
    have := hhi₀
    exact CochainComplex.isStrictlyLE_of_le C hi₀ hi (le_max_left _ _)
  let n : ℕ := (hi - lo).toNat
  have hlen : (n : ℤ) = hi - lo := Int.toNat_of_nonneg (by dsimp [hi]; omega)
  obtain ⟨e⟩ := h_restriction
  let S := boundedTailPostnikov C lo hi n hlo hhi hlen
  obtain ⟨g, _, _, _⟩ := CategoryTheory.Triangulated.PostnikovSystem.exists_iso
    (boundedTailPiece_hom_eq_zero F h_negative C lo hi n hlen)
    (mapPostnikovSystem F S) (mapPostnikovSystem F' S)
    (boundedTailPieceComparison F F' e C lo hi n hlen)
    (boundedTailPieceComparison_comm F F' e C lo hi n hlo hhi hlen)
  let eTotal : S.obj (Fin.last n) ≅ (⟨K.obj, K.property⟩ : DerivedCategory.Bounded A) :=
    boundedTailPostnikovLastIso C lo hi n hlo hhi hlen ≪≫ ObjectProperty.isoMk _ eK
  exact ⟨(F.mapIso eTotal).symm ≪≫ g (Fin.last n) ≪≫ F'.mapIso eTotal⟩

end AlgebraicGeometry

end
