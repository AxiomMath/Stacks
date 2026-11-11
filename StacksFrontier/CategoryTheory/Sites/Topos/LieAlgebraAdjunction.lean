module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward
public import StacksFrontier.CategoryTheory.Sites.Topos.StructureAdjunction
public import StacksFrontier.Topology.Sheaves.AlgebraicStructure.Examples
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Inverse and direct images of sheaves of Lie algebras along a morphism of topoi

Let `k` be a field and let `f = (f⁻¹, f_*) : Sh(C) → Sh(D)` be a morphism of topoi. A sheaf of
Lie algebras over `k` is a sheaf of sets `F` together with morphisms of sheaves of sets
`F × F → F` (addition and bracket), `F → F` (negation and multiplication by each `c : k`) and
`* → F` (zero), subject to the identities of a Lie algebra over `k`, each of which is an
equality between morphisms of sheaves of sets. A functor between categories of sheaves of sets
which preserves finite products carries all of this structure along. The inverse image `f⁻¹` is
left exact and the direct image `f_*` is a right adjoint, so both preserve finite products, and
they induce functors on sheaves of Lie algebras whose underlying sheaves of sets are, on the
nose, `f⁻¹` and `f_*` of the underlying sheaves of sets. The unit and counit of `f⁻¹ ⊣ f_*` on
sheaves of sets are morphisms of sheaves of Lie algebras, and the triangle identities follow from
those on sheaves of sets because taking underlying sheaves of sets is faithful. This is the case
of Lie algebras over a field in Stacks 00YV.

## Main definitions

* `CategoryTheory.Sheaf.lieSheaf`: the underlying sheaf of sets of a sheaf of Lie algebras, and
  `CategoryTheory.Sheaf.lieBinHom`, `lieUnHom`, `lieZeroHom`: its operations as morphisms of
  sheaves of sets.
* `CategoryTheory.Sheaf.lieObjLieRing`, `lieObjLieAlgebra`, `lieObj`: the Lie algebra structure
  transported to the image of the underlying sheaf of sets under a finite-product-preserving
  functor to types.
* `Stacks.Topos.pullbackLieSheaf`, `Stacks.Topos.pullbackLieFunctor`: the image of a sheaf of Lie
  algebras under a finite-product-preserving functor between categories of sheaves of sets.
* `Stacks.Topos.lieUnit`, `lieCounit`, `lieImageAdjunction`: the unit, the counit and the
  adjunction `f⁻¹ ⊣ f_*` on sheaves of Lie algebras.
* `Stacks.Topos.lieAlgebraStructureAdjunction`: the adjoint pair `f⁻¹ ⊣ f_*` on sheaves of Lie
  algebras over `k`, compatible with taking underlying sheaves of sets.

## Main results

* `CategoryTheory.Presheaf.isSheaf_lieAlgCat_of_isSheaf_forget`: a presheaf of Lie algebras whose
  underlying presheaf of sets is a sheaf is a sheaf.
* `Stacks.Topos.lieSheafMap_lieUnit`, `lieSheafMap_lieCounit`: the unit and counit on sheaves of
  Lie algebras are, on underlying sheaves of sets, the unit and counit of `f⁻¹ ⊣ f_*`.

## Implementation notes

The operations are handled uniformly: a binary operation is any family
`op : ∀ L : LieAlgCat k, L → L → L` commuting with all morphisms of Lie algebras (addition and
bracket), and a unary one is such a family `L → L` (negation and the scalar multiplications).
Transport along a finite-product-preserving functor, naturality in the functor and in the sheaf,
and the comparison between transporting in one step and in two steps are proved once for such
families. Each identity of a Lie algebra is transported by writing its variables as images of
one element under morphisms into the underlying sheaf of sets, so that both sides become images
of a single element under two morphisms of sheaves of sets, which agree because they agree on
sections.

The sheaf condition for the transported presheaf of Lie algebras is proved from separatedness,
as `CategoryTheory.Presheaf.isSheaf_ringCat_of_isSheaf_forget` does for rings, rather than from
`CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`; no size condition relating the universe of
the Lie algebras to the universes of the sites is needed.

The instances `HasSheafCompose (forget (LieAlgCat k))` on both sites are assumed, as they are
for rings in the sibling constructions. They hold for small sites whose sheaves take values in
the universe of the site, since `forget (LieAlgCat k)` preserves small limits.

## References

* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe t w v u v' u'

namespace CategoryTheory.Sheaf

open _root_.CategoryTheory.Functor

variable {k : Type w} [Field k]

section LieOperations

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget (LieAlgCat.{w} k))] (F : Sheaf J (LieAlgCat.{w} k))
  (op : ∀ L : LieAlgCat.{w} k, L → L → L)
  (hop : ∀ {L M : LieAlgCat.{w} k} (φ : L ⟶ M) (a b : L),
    φ.hom (op L a b) = op M (φ.hom a) (φ.hom b))
  (uop : ∀ L : LieAlgCat.{w} k, L → L)
  (huop : ∀ {L M : LieAlgCat.{w} k} (φ : L ⟶ M) (a : L), φ.hom (uop L a) = uop M (φ.hom a))

/-- The underlying sheaf of sets of a sheaf of Lie algebras. -/
abbrev lieSheaf : Sheaf J (Type w) :=
  (sheafCompose J (forget (LieAlgCat.{w} k))).obj F

/-- A binary operation on Lie algebras over `k` which commutes with every morphism of Lie
algebras, read on the underlying sheaf of sets of a sheaf of Lie algebras. -/
def lieBinHom : lieSheaf F ⨯ lieSheaf F ⟶ lieSheaf F :=
  binaryOpHom (fun X (a b : F.obj.obj X) ↦ op _ a b) (fun g a b ↦ hop (F.obj.map g) a b)

/-- A unary operation on Lie algebras over `k` which commutes with every morphism of Lie
algebras, read on the underlying sheaf of sets of a sheaf of Lie algebras. -/
def lieUnHom : lieSheaf F ⟶ lieSheaf F :=
  unaryOpHom (fun X (a : F.obj.obj X) ↦ uop _ a) (fun g a ↦ huop (F.obj.map g) a)

/-- The zero section of the underlying sheaf of sets of a sheaf of Lie algebras. -/
def lieZeroHom : ⊤_ (Sheaf J (Type w)) ⟶ lieSheaf F :=
  constHom (fun X ↦ (0 : F.obj.obj X)) (fun g ↦ map_zero (F.obj.map g).hom)

/-- Addition on the underlying sheaf of sets of a sheaf of Lie algebras. -/
abbrev lieAddHom : lieSheaf F ⨯ lieSheaf F ⟶ lieSheaf F :=
  lieBinHom F (fun _ a b ↦ a + b) (fun φ a b ↦ map_add φ.hom a b)

/-- The Lie bracket on the underlying sheaf of sets of a sheaf of Lie algebras. -/
abbrev lieBracketHom : lieSheaf F ⨯ lieSheaf F ⟶ lieSheaf F :=
  lieBinHom F (fun _ a b ↦ ⁅a, b⁆) (fun φ a b ↦ φ.hom.map_lie a b)

/-- Negation on the underlying sheaf of sets of a sheaf of Lie algebras. -/
abbrev lieNegHom : lieSheaf F ⟶ lieSheaf F :=
  lieUnHom F (fun _ a ↦ -a) (fun φ a ↦ map_neg φ.hom a)

/-- Multiplication by a scalar `c : k` on the underlying sheaf of sets of a sheaf of Lie
algebras over `k`. -/
abbrev lieSMulHom (c : k) : lieSheaf F ⟶ lieSheaf F :=
  lieUnHom F (fun _ a ↦ c • a) (fun φ a ↦ map_smul φ.hom c a)

variable {F}

/-- On sections over `X`, `lieBinHom F op hop` sends the pair of `a` and `b` to `op a b`. -/
@[simp]
lemma sectionsFunctor_map_lieBinHom (X : Cᵒᵖ)
    (a b : (sectionsFunctor J X).obj (lieSheaf F)) :
    (sectionsFunctor J X).map (lieBinHom F op hop)
      (prodObjMk (A := lieSheaf F) (B := lieSheaf F) a b) = op (F.obj.obj X) a b :=
  sectionsFunctor_map_binaryOpHom (A := lieSheaf F) (B := lieSheaf F) (E := lieSheaf F)
    _ _ X a b

/-- On sections over `X`, `lieUnHom F op hop` sends `a` to `op a`. -/
@[simp]
lemma sectionsFunctor_map_lieUnHom (X : Cᵒᵖ)
    (a : (sectionsFunctor J X).obj (lieSheaf F)) :
    (sectionsFunctor J X).map (lieUnHom F uop huop) a = uop (F.obj.obj X) a := rfl

/-- Sections over `X` of the underlying sheaf of sets of a sheaf of Lie algebras form a Lie ring:
they are the sections of the sheaf of Lie algebras itself. -/
instance lieSectionsLieRing (X : Cᵒᵖ) : LieRing ((sectionsFunctor J X).obj (lieSheaf F)) :=
  inferInstanceAs (LieRing (F.obj.obj X))

/-- Sections over `X` of the underlying sheaf of sets of a sheaf of Lie algebras over `k` form a
Lie algebra over `k`. -/
instance lieSectionsLieAlgebra (X : Cᵒᵖ) : LieAlgebra k ((sectionsFunctor J X).obj (lieSheaf F)) :=
  inferInstanceAs (LieAlgebra k (F.obj.obj X))

/-- On sections over `X`, `lieAddHom F` sends the pair of `a` and `b` to `a + b`. -/
@[simp]
lemma sectionsFunctor_map_lieAddHom (X : Cᵒᵖ) (a b : (sectionsFunctor J X).obj (lieSheaf F)) :
    (sectionsFunctor J X).map (lieAddHom F)
      (prodObjMk (A := lieSheaf F) (B := lieSheaf F) a b) = a + b :=
  sectionsFunctor_map_lieBinHom (fun _ a b ↦ a + b) (fun φ a b ↦ map_add φ.hom a b) X a b

/-- On sections over `X`, `lieBracketHom F` sends the pair of `a` and `b` to `⁅a, b⁆`. -/
@[simp]
lemma sectionsFunctor_map_lieBracketHom (X : Cᵒᵖ)
    (a b : (sectionsFunctor J X).obj (lieSheaf F)) :
    (sectionsFunctor J X).map (lieBracketHom F)
      (prodObjMk (A := lieSheaf F) (B := lieSheaf F) a b) = ⁅a, b⁆ :=
  sectionsFunctor_map_lieBinHom (fun _ a b ↦ ⁅a, b⁆) (fun φ a b ↦ φ.hom.map_lie a b) X a b

/-- On sections over `X`, `lieNegHom F` sends `a` to `-a`. -/
@[simp]
lemma sectionsFunctor_map_lieNegHom (X : Cᵒᵖ) (a : (sectionsFunctor J X).obj (lieSheaf F)) :
    (sectionsFunctor J X).map (lieNegHom F) a = -a := rfl

/-- On sections over `X`, `lieSMulHom F c` sends `a` to `c • a`. -/
@[simp]
lemma sectionsFunctor_map_lieSMulHom (c : k) (X : Cᵒᵖ)
    (a : (sectionsFunctor J X).obj (lieSheaf F)) :
    (sectionsFunctor J X).map (lieSMulHom F c) a = c • a := rfl

/-- On sections over `X`, `lieZeroHom F` takes the value `0`. -/
@[simp]
lemma sectionsFunctor_map_lieZeroHom (X : Cᵒᵖ)
    (p : (sectionsFunctor J X).obj (⊤_ (Sheaf J (Type w)))) :
    (sectionsFunctor J X).map (lieZeroHom F) p =
      (0 : (sectionsFunctor J X).obj (lieSheaf F)) := rfl

end LieOperations

section LieTransport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget (LieAlgCat.{w} k))] (F : Sheaf J (LieAlgCat.{w} k))
  (P : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteProducts P]
  (op : ∀ L : LieAlgCat.{w} k, L → L → L)
  (hop : ∀ {L M : LieAlgCat.{w} k} (φ : L ⟶ M) (a b : L),
    φ.hom (op L a b) = op M (φ.hom a) (φ.hom b))
  (uop : ∀ L : LieAlgCat.{w} k, L → L)
  (huop : ∀ {L M : LieAlgCat.{w} k} (φ : L ⟶ M) (a : L), φ.hom (uop L a) = uop M (φ.hom a))

/-- A natural binary operation of Lie algebras, transported to the image of the underlying sheaf
of sets of a sheaf of Lie algebras under a finite-product-preserving functor to types. -/
def lieBinObj (x y : P.obj (lieSheaf F)) : P.obj (lieSheaf F) :=
  P.map (lieBinHom F op hop) (prodObjMk x y)

/-- A natural unary operation of Lie algebras, transported to the image of the underlying sheaf
of sets of a sheaf of Lie algebras under a finite-product-preserving functor to types. -/
def lieUnObj (x : P.obj (lieSheaf F)) : P.obj (lieSheaf F) :=
  P.map (lieUnHom F uop huop) x

/-- The zero of the image of the underlying sheaf of sets of a sheaf of Lie algebras. -/
def lieZeroObj : P.obj (lieSheaf F) := P.map (lieZeroHom F) default

variable {F P}

/-- The transported binary operation on two elements in the image of a common element under
two morphisms. -/
lemma lieBinObj_map_map {Z : Sheaf J (Type w)} (m n : Z ⟶ lieSheaf F)
    (z : P.obj Z) :
    lieBinObj F P op hop (P.map m z) (P.map n z) =
      P.map (Limits.prod.lift m n ≫ lieBinHom F op hop) z := by
  rw [lieBinObj, P.map_comp_apply, map_lift_apply]

omit [PreservesFiniteProducts P] in
/-- The transported unary operation on the image of an element under a morphism. -/
lemma lieUnObj_map {Z : Sheaf J (Type w)} (m : Z ⟶ lieSheaf F) (z : P.obj Z) :
    lieUnObj F P uop huop (P.map m z) = P.map (m ≫ lieUnHom F uop huop) z := by
  rw [lieUnObj, P.map_comp_apply]

/-- The transported zero is the image of any element under the zero morphism. -/
lemma lieZeroObj_eq {Z : Sheaf J (Type w)} (z : P.obj Z) :
    lieZeroObj F P = P.map (Limits.terminal.from Z ≫ lieZeroHom F) z := by
  rw [lieZeroObj, P.map_comp_apply, map_terminalFrom_apply]

/-- Any three elements of `P` of the underlying sheaf of sets are the images of a single element
under three morphisms. -/
lemma exists_lieSheaf_map_eq₃ (x y z : P.obj (lieSheaf F)) :
    ∃ (Z : Sheaf J (Type w)) (s : P.obj Z) (a b c : Z ⟶ lieSheaf F),
      P.map a s = x ∧ P.map b s = y ∧ P.map c s = z :=
  ⟨_, prodObjMk (A := lieSheaf F) (B := lieSheaf F ⨯ lieSheaf F) x
    (prodObjMk (A := lieSheaf F) (B := lieSheaf F) y z), Limits.prod.fst,
    Limits.prod.snd ≫ Limits.prod.fst (X := lieSheaf F) (Y := lieSheaf F),
    Limits.prod.snd ≫ Limits.prod.snd (X := lieSheaf F) (Y := lieSheaf F),
    by simp, by simp, by simp⟩

/-- Any two elements of `P` of the underlying sheaf of sets are the images of a single element
under two morphisms. -/
lemma exists_lieSheaf_map_eq₂ (x y : P.obj (lieSheaf F)) :
    ∃ (Z : Sheaf J (Type w)) (s : P.obj Z) (a b : Z ⟶ lieSheaf F),
      P.map a s = x ∧ P.map b s = y :=
  ⟨_, prodObjMk (A := lieSheaf F) (B := lieSheaf F) x y,
    Limits.prod.fst (X := lieSheaf F) (Y := lieSheaf F),
    Limits.prod.snd (X := lieSheaf F) (Y := lieSheaf F), by simp, by simp⟩

omit [PreservesFiniteProducts P] in
/-- Any element of `P` of the underlying sheaf of sets is the image of itself under the
identity. -/
lemma exists_lieSheaf_map_eq₁ (x : P.obj (lieSheaf F)) :
    ∃ (Z : Sheaf J (Type w)) (s : P.obj Z) (a : Z ⟶ lieSheaf F), P.map a s = x :=
  ⟨_, x, 𝟙 _, by simp⟩

omit [PreservesFiniteProducts P] in
/-- Equal morphisms have equal images at an element. -/
private lemma map_apply_eq_of_eq {Z : Sheaf J (Type w)} {m n : Z ⟶ lieSheaf F} (h : m = n)
    (s : P.obj Z) : P.map m s = P.map n s := by
  rw [h]

variable (F P)

/-- Addition, transported. -/
abbrev lieAddObj : P.obj (lieSheaf F) → P.obj (lieSheaf F) → P.obj (lieSheaf F) :=
  lieBinObj F P (fun _ a b ↦ a + b) (fun φ a b ↦ map_add φ.hom a b)

/-- The Lie bracket, transported. -/
abbrev lieBracketObj : P.obj (lieSheaf F) → P.obj (lieSheaf F) → P.obj (lieSheaf F) :=
  lieBinObj F P (fun _ a b ↦ ⁅a, b⁆) (fun φ a b ↦ φ.hom.map_lie a b)

/-- Negation, transported. -/
abbrev lieNegObj : P.obj (lieSheaf F) → P.obj (lieSheaf F) :=
  lieUnObj F P (fun _ a ↦ -a) (fun φ a ↦ map_neg φ.hom a)

/-- Multiplication by a scalar `c : k`, transported. -/
abbrev lieSMulObj (c : k) : P.obj (lieSheaf F) → P.obj (lieSheaf F) :=
  lieUnObj F P (fun _ a ↦ c • a) (fun φ a ↦ map_smul φ.hom c a)

variable {F P}

/-- The transported addition on two elements in the image of a common element. -/
lemma lieAddObj_map_map {Z : Sheaf J (Type w)} (m n : Z ⟶ lieSheaf F) (z : P.obj Z) :
    lieAddObj F P (P.map m z) (P.map n z) = P.map (Limits.prod.lift m n ≫ lieAddHom F) z :=
  lieBinObj_map_map (fun _ a b ↦ a + b) (fun φ a b ↦ map_add φ.hom a b) m n z

/-- The transported bracket on two elements in the image of a common element. -/
lemma lieBracketObj_map_map {Z : Sheaf J (Type w)} (m n : Z ⟶ lieSheaf F) (z : P.obj Z) :
    lieBracketObj F P (P.map m z) (P.map n z) =
      P.map (Limits.prod.lift m n ≫ lieBracketHom F) z :=
  lieBinObj_map_map (fun _ a b ↦ ⁅a, b⁆) (fun φ a b ↦ φ.hom.map_lie a b) m n z

omit [PreservesFiniteProducts P] in
/-- The transported negation on the image of an element. -/
lemma lieNegObj_map {Z : Sheaf J (Type w)} (m : Z ⟶ lieSheaf F) (z : P.obj Z) :
    lieNegObj F P (P.map m z) = P.map (m ≫ lieNegHom F) z :=
  lieUnObj_map (fun _ a ↦ -a) (fun φ a ↦ map_neg φ.hom a) m z

omit [PreservesFiniteProducts P] in
/-- The transported scalar multiplication on the image of an element. -/
lemma lieSMulObj_map (c : k) {Z : Sheaf J (Type w)} (m : Z ⟶ lieSheaf F) (z : P.obj Z) :
    lieSMulObj F P c (P.map m z) = P.map (m ≫ lieSMulHom F c) z :=
  lieUnObj_map (fun _ a ↦ c • a) (fun φ a ↦ map_smul φ.hom c a) m z

variable (F P)

/-- The transported addition is associative. -/
lemma lieAddObj_assoc (x y z : P.obj (lieSheaf F)) :
    lieAddObj F P (lieAddObj F P x y) z = lieAddObj F P x (lieAddObj F P y z) := by
  obtain ⟨Z, s, a, b, c, rfl, rfl, rfl⟩ := exists_lieSheaf_map_eq₃ (F := F) x y z
  simp only [lieAddObj_map_map]
  refine map_apply_eq_of_eq (F := F) (hom_ext_sections fun X q ↦ ?_) s
  simp only [map_comp_apply, map_lift_apply, sectionsFunctor_map_lieAddHom]
  exact add_assoc _ _ _

/-- The transported zero is a left identity for the transported addition. -/
lemma lieAddObj_zero_add (x : P.obj (lieSheaf F)) :
    lieAddObj F P (lieZeroObj F P) x = x := by
  obtain ⟨Z, s, a, rfl⟩ := exists_lieSheaf_map_eq₁ (F := F) x
  rw [lieZeroObj_eq s]
  simp only [lieAddObj_map_map]
  refine map_apply_eq_of_eq (F := F) (hom_ext_sections fun X q ↦ ?_) s
  simp only [map_comp_apply, map_lift_apply, sectionsFunctor_map_lieAddHom,
    sectionsFunctor_map_lieZeroHom]
  exact zero_add _

/-- The transported negation is a left inverse for the transported addition. -/
lemma lieAddObj_neg_add_cancel (x : P.obj (lieSheaf F)) :
    lieAddObj F P (lieNegObj F P x) x = lieZeroObj F P := by
  obtain ⟨Z, s, a, rfl⟩ := exists_lieSheaf_map_eq₁ (F := F) x
  rw [lieZeroObj_eq s]
  simp only [lieAddObj_map_map, lieNegObj_map]
  refine map_apply_eq_of_eq (F := F) (hom_ext_sections fun X q ↦ ?_) s
  simp only [map_comp_apply, map_lift_apply, sectionsFunctor_map_lieAddHom,
    sectionsFunctor_map_lieNegHom,
    sectionsFunctor_map_lieZeroHom]
  exact neg_add_cancel _

/-- The transported addition is commutative. -/
lemma lieAddObj_comm (x y : P.obj (lieSheaf F)) :
    lieAddObj F P x y = lieAddObj F P y x := by
  obtain ⟨Z, s, a, b, rfl, rfl⟩ := exists_lieSheaf_map_eq₂ (F := F) x y
  simp only [lieAddObj_map_map]
  refine map_apply_eq_of_eq (F := F) (hom_ext_sections fun X q ↦ ?_) s
  simp only [map_comp_apply, map_lift_apply, sectionsFunctor_map_lieAddHom]
  exact add_comm _ _

/-- The transported scalar multiplication distributes over the transported addition. -/
lemma lieSMulObj_smul_add (c : k) (x y : P.obj (lieSheaf F)) :
    lieSMulObj F P c (lieAddObj F P x y) =
      lieAddObj F P (lieSMulObj F P c x) (lieSMulObj F P c y) := by
  obtain ⟨Z, s, a, b, rfl, rfl⟩ := exists_lieSheaf_map_eq₂ (F := F) x y
  simp only [lieAddObj_map_map, lieSMulObj_map]
  refine map_apply_eq_of_eq (F := F) (hom_ext_sections fun X q ↦ ?_) s
  simp only [map_comp_apply, map_lift_apply, sectionsFunctor_map_lieAddHom,
    sectionsFunctor_map_lieSMulHom]
  exact smul_add _ _ _

/-- The transported scalar multiplication is additive in the scalar. -/
lemma lieSMulObj_add_smul (c d : k) (x : P.obj (lieSheaf F)) :
    lieSMulObj F P (c + d) x = lieAddObj F P (lieSMulObj F P c x) (lieSMulObj F P d x) := by
  obtain ⟨Z, s, a, rfl⟩ := exists_lieSheaf_map_eq₁ (F := F) x
  simp only [lieAddObj_map_map, lieSMulObj_map]
  refine map_apply_eq_of_eq (F := F) (hom_ext_sections fun X q ↦ ?_) s
  simp only [map_comp_apply, map_lift_apply, sectionsFunctor_map_lieAddHom,
    sectionsFunctor_map_lieSMulHom]
  exact add_smul _ _ _

omit [PreservesFiniteProducts P] in
/-- The transported scalar multiplication is multiplicative in the scalar. -/
lemma lieSMulObj_mul_smul (c d : k) (x : P.obj (lieSheaf F)) :
    lieSMulObj F P (c * d) x = lieSMulObj F P c (lieSMulObj F P d x) := by
  obtain ⟨Z, s, a, rfl⟩ := exists_lieSheaf_map_eq₁ (F := F) x
  simp only [lieSMulObj_map]
  refine map_apply_eq_of_eq (F := F) (hom_ext_sections fun X q ↦ ?_) s
  simp only [map_comp_apply, sectionsFunctor_map_lieSMulHom]
  exact mul_smul _ _ _

omit [PreservesFiniteProducts P] in
/-- The scalar `1` acts trivially under the transported scalar multiplication. -/
lemma lieSMulObj_one_smul (x : P.obj (lieSheaf F)) : lieSMulObj F P 1 x = x := by
  obtain ⟨Z, s, a, rfl⟩ := exists_lieSheaf_map_eq₁ (F := F) x
  simp only [lieSMulObj_map]
  refine map_apply_eq_of_eq (F := F) (hom_ext_sections fun X q ↦ ?_) s
  simp only [map_comp_apply, sectionsFunctor_map_lieSMulHom]
  exact one_smul _ _

/-- The transported bracket is additive in its first argument. -/
lemma lieBracketObj_add_lie (x y z : P.obj (lieSheaf F)) :
    lieBracketObj F P (lieAddObj F P x y) z =
      lieAddObj F P (lieBracketObj F P x z) (lieBracketObj F P y z) := by
  obtain ⟨Z, s, a, b, c, rfl, rfl, rfl⟩ := exists_lieSheaf_map_eq₃ (F := F) x y z
  simp only [lieAddObj_map_map, lieBracketObj_map_map]
  refine map_apply_eq_of_eq (F := F) (hom_ext_sections fun X q ↦ ?_) s
  simp only [map_comp_apply, map_lift_apply, sectionsFunctor_map_lieAddHom,
    sectionsFunctor_map_lieBracketHom]
  exact add_lie _ _ _

/-- The transported bracket is additive in its second argument. -/
lemma lieBracketObj_lie_add (x y z : P.obj (lieSheaf F)) :
    lieBracketObj F P x (lieAddObj F P y z) =
      lieAddObj F P (lieBracketObj F P x y) (lieBracketObj F P x z) := by
  obtain ⟨Z, s, a, b, c, rfl, rfl, rfl⟩ := exists_lieSheaf_map_eq₃ (F := F) x y z
  simp only [lieAddObj_map_map, lieBracketObj_map_map]
  refine map_apply_eq_of_eq (F := F) (hom_ext_sections fun X q ↦ ?_) s
  simp only [map_comp_apply, map_lift_apply, sectionsFunctor_map_lieAddHom,
    sectionsFunctor_map_lieBracketHom]
  exact lie_add _ _ _

/-- The transported bracket vanishes on the diagonal. -/
lemma lieBracketObj_lie_self (x : P.obj (lieSheaf F)) :
    lieBracketObj F P x x = lieZeroObj F P := by
  obtain ⟨Z, s, a, rfl⟩ := exists_lieSheaf_map_eq₁ (F := F) x
  rw [lieZeroObj_eq s]
  simp only [lieBracketObj_map_map]
  refine map_apply_eq_of_eq (F := F) (hom_ext_sections fun X q ↦ ?_) s
  simp only [map_comp_apply, map_lift_apply, sectionsFunctor_map_lieBracketHom,
    sectionsFunctor_map_lieZeroHom]
  exact lie_self _

/-- The transported bracket satisfies the Leibniz identity. -/
lemma lieBracketObj_leibniz_lie (x y z : P.obj (lieSheaf F)) :
    lieBracketObj F P x (lieBracketObj F P y z) =
      lieAddObj F P (lieBracketObj F P (lieBracketObj F P x y) z)
        (lieBracketObj F P y (lieBracketObj F P x z)) := by
  obtain ⟨Z, s, a, b, c, rfl, rfl, rfl⟩ := exists_lieSheaf_map_eq₃ (F := F) x y z
  simp only [lieAddObj_map_map, lieBracketObj_map_map]
  refine map_apply_eq_of_eq (F := F) (hom_ext_sections fun X q ↦ ?_) s
  simp only [map_comp_apply, map_lift_apply, sectionsFunctor_map_lieAddHom,
    sectionsFunctor_map_lieBracketHom]
  exact leibniz_lie _ _ _

/-- The transported bracket commutes with the transported scalar multiplication in its second
argument. -/
lemma lieBracketObj_lie_smul (c : k) (x y : P.obj (lieSheaf F)) :
    lieBracketObj F P x (lieSMulObj F P c y) = lieSMulObj F P c (lieBracketObj F P x y) := by
  obtain ⟨Z, s, a, b, rfl, rfl⟩ := exists_lieSheaf_map_eq₂ (F := F) x y
  simp only [lieBracketObj_map_map, lieSMulObj_map]
  refine map_apply_eq_of_eq (F := F) (hom_ext_sections fun X q ↦ ?_) s
  simp only [map_comp_apply, map_lift_apply, sectionsFunctor_map_lieBracketHom,
    sectionsFunctor_map_lieSMulHom]
  exact lie_smul _ _ _

/-- The image of the underlying sheaf of sets of a sheaf of Lie algebras under a
finite-product-preserving functor to types is a Lie ring, with the transported operations. -/
@[instance_reducible]
def lieObjLieRing : LieRing (P.obj (lieSheaf F)) :=
  letI : Add (P.obj (lieSheaf F)) := ⟨lieAddObj F P⟩
  letI : Neg (P.obj (lieSheaf F)) := ⟨lieNegObj F P⟩
  letI : Zero (P.obj (lieSheaf F)) := ⟨lieZeroObj F P⟩
  letI : AddGroup (P.obj (lieSheaf F)) :=
    AddGroup.ofLeftAxioms (lieAddObj_assoc F P) (lieAddObj_zero_add F P)
      (lieAddObj_neg_add_cancel F P)
  { (inferInstance : AddGroup (P.obj (lieSheaf F))) with
    add_comm := lieAddObj_comm F P
    bracket := lieBracketObj F P
    add_lie := lieBracketObj_add_lie F P
    lie_add := lieBracketObj_lie_add F P
    lie_self := lieBracketObj_lie_self F P
    leibniz_lie := lieBracketObj_leibniz_lie F P }

/-- The image of the underlying sheaf of sets of a sheaf of Lie algebras over `k` under a
finite-product-preserving functor to types is a Lie algebra over `k`, with the transported
operations. -/
@[instance_reducible]
def lieObjLieAlgebra :
    letI := lieObjLieRing F P
    LieAlgebra k (P.obj (lieSheaf F)) :=
  letI := lieObjLieRing F P
  letI : SMul k (P.obj (lieSheaf F)) := ⟨lieSMulObj F P⟩
  letI : Module k (P.obj (lieSheaf F)) :=
    Module.ofMinimalAxioms (lieSMulObj_smul_add F P) (lieSMulObj_add_smul F P)
      (lieSMulObj_mul_smul F P) (lieSMulObj_one_smul F P)
  { (inferInstance : Module k (P.obj (lieSheaf F))) with
    lie_smul := lieBracketObj_lie_smul F P }

variable {F P} {Q : Sheaf J (Type w) ⥤ Type t} [PreservesFiniteProducts Q]

/-- A natural transformation of finite-product-preserving functors commutes with a transported
binary operation. -/
lemma lieBinObj_naturality (θ : P ⟶ Q) (x y : P.obj (lieSheaf F)) :
    θ.app (lieSheaf F) (lieBinObj F P op hop x y) =
      lieBinObj F Q op hop (θ.app _ x) (θ.app _ y) := by
  rw [lieBinObj, lieBinObj, natTrans_app_map_apply, prodObjMk_naturality]

omit [PreservesFiniteProducts P] [PreservesFiniteProducts Q] in
/-- A natural transformation of finite-product-preserving functors commutes with a transported
unary operation. -/
lemma lieUnObj_naturality (θ : P ⟶ Q) (x : P.obj (lieSheaf F)) :
    θ.app (lieSheaf F) (lieUnObj F P uop huop x) = lieUnObj F Q uop huop (θ.app _ x) :=
  natTrans_app_map_apply θ _ x

variable {F' : Sheaf J (LieAlgCat.{w} k)} (a : F ⟶ F')

/-- The morphism of underlying sheaves of sets of a morphism of sheaves of Lie algebras
intertwines a natural binary operation. -/
lemma lieBinHom_comp_map :
    lieBinHom F op hop ≫ (sheafCompose J (forget (LieAlgCat.{w} k))).map a =
      Limits.prod.map ((sheafCompose J (forget (LieAlgCat.{w} k))).map a)
          ((sheafCompose J (forget (LieAlgCat.{w} k))).map a) ≫ lieBinHom F' op hop := by
  refine hom_ext_sections fun X q ↦ ?_
  rw [← prodObjMk_map_fst_map_snd (P := sectionsFunctor J X) q,
    (sectionsFunctor J X).map_comp_apply, (sectionsFunctor J X).map_comp_apply,
    sectionsFunctor_map_lieBinHom, map_prodMap_apply, map_fst_prodObjMk, map_snd_prodObjMk,
    sectionsFunctor_map_lieBinHom]
  exact hop (a.hom.app X) _ _

/-- The morphism of underlying sheaves of sets of a morphism of sheaves of Lie algebras
intertwines a natural unary operation. -/
lemma lieUnHom_comp_map :
    lieUnHom F uop huop ≫ (sheafCompose J (forget (LieAlgCat.{w} k))).map a =
      (sheafCompose J (forget (LieAlgCat.{w} k))).map a ≫ lieUnHom F' uop huop :=
  hom_ext_sections fun X q ↦ huop (a.hom.app X) q

/-- The image of the morphism of underlying sheaves of sets of a morphism of sheaves of Lie
algebras commutes with a transported binary operation. -/
lemma map_lieBinObj (x y : P.obj (lieSheaf F)) :
    P.map ((sheafCompose J (forget (LieAlgCat.{w} k))).map a) (lieBinObj F P op hop x y) =
      lieBinObj F' P op hop (P.map ((sheafCompose J (forget (LieAlgCat.{w} k))).map a) x)
        (P.map ((sheafCompose J (forget (LieAlgCat.{w} k))).map a) y) := by
  rw [lieBinObj, ← P.map_comp_apply, lieBinHom_comp_map, P.map_comp_apply, map_prodMap_apply,
    map_fst_prodObjMk, map_snd_prodObjMk, lieBinObj]

omit [PreservesFiniteProducts P] in
/-- The image of the morphism of underlying sheaves of sets of a morphism of sheaves of Lie
algebras commutes with a transported unary operation. -/
lemma map_lieUnObj (x : P.obj (lieSheaf F)) :
    P.map ((sheafCompose J (forget (LieAlgCat.{w} k))).map a) (lieUnObj F P uop huop x) =
      lieUnObj F' P uop huop (P.map ((sheafCompose J (forget (LieAlgCat.{w} k))).map a) x) := by
  rw [lieUnObj, ← P.map_comp_apply, lieUnHom_comp_map, P.map_comp_apply, lieUnObj]

end LieTransport

section LieObj

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget (LieAlgCat.{w} k))] (F : Sheaf J (LieAlgCat.{w} k))
  (P : Sheaf J (Type w) ⥤ Type w) [PreservesFiniteProducts P]

/-- The image of the underlying sheaf of sets of a sheaf of Lie algebras under a
finite-product-preserving functor to types, as a Lie algebra over `k`. -/
def lieObj : LieAlgCat.{w} k :=
  letI := lieObjLieRing F P
  letI := lieObjLieAlgebra F P
  LieAlgCat.of k (P.obj (lieSheaf F))

variable {F P} {Q : Sheaf J (Type w) ⥤ Type w} [PreservesFiniteProducts Q]

/-- A natural transformation of finite-product-preserving functors to types induces a morphism
of Lie algebras between the transported Lie algebras. -/
def lieObjHom (θ : P ⟶ Q) : lieObj F P ⟶ lieObj F Q :=
  ⟨{ toFun := θ.app (lieSheaf F)
     map_add' := lieBinObj_naturality (fun _ a b ↦ a + b) (fun φ a b ↦ map_add φ.hom a b) θ
     map_smul' := fun c ↦ lieUnObj_naturality (fun _ a ↦ c • a) (fun φ a ↦ map_smul φ.hom c a) θ
     map_lie' := fun {_ _} ↦
       lieBinObj_naturality (fun _ a b ↦ ⁅a, b⁆) (fun φ a b ↦ φ.hom.map_lie a b) θ _ _ }⟩

/-- The morphism `lieObjHom θ` is `θ` on underlying sets. -/
@[simp]
lemma lieObjHom_hom_apply (θ : P ⟶ Q) (x : P.obj (lieSheaf F)) :
    (lieObjHom θ).hom x = θ.app (lieSheaf F) x := rfl

variable {F' : Sheaf J (LieAlgCat.{w} k)} (a : F ⟶ F') (P)

/-- A morphism of sheaves of Lie algebras induces a morphism between the transported Lie
algebras. -/
def lieObjMap : lieObj F P ⟶ lieObj F' P :=
  ⟨{ toFun := P.map ((sheafCompose J (forget (LieAlgCat.{w} k))).map a)
     map_add' := map_lieBinObj (fun _ a b ↦ a + b) (fun φ a b ↦ map_add φ.hom a b) a
     map_smul' := fun c ↦ map_lieUnObj (fun _ a ↦ c • a) (fun φ a ↦ map_smul φ.hom c a) a
     map_lie' := fun {_ _} ↦
       map_lieBinObj (fun _ a b ↦ ⁅a, b⁆) (fun φ a b ↦ φ.hom.map_lie a b) a _ _ }⟩

variable (F)

/-- Over an object `X`, the Lie algebra of sections of `F` is the Lie algebra transported
along the sections functor: the identity is a morphism of Lie algebras from the former to the
latter. -/
def sectionsToLieObj (X : Cᵒᵖ) : F.obj.obj X ⟶ lieObj F (sectionsFunctor J X) :=
  ⟨{ toFun := fun x ↦ x
     map_add' := fun x y ↦ (sectionsFunctor_map_lieAddHom (F := F) X x y).symm
     map_smul' := fun _ _ ↦ rfl
     map_lie' := fun {x y} ↦ (sectionsFunctor_map_lieBracketHom (F := F) X x y).symm }⟩

/-- The identity, read as a morphism of Lie algebras from the Lie algebra transported along the
sections functor over `X` to the Lie algebra of sections of `F` over `X`. -/
def lieObjToSections (X : Cᵒᵖ) : lieObj F (sectionsFunctor J X) ⟶ F.obj.obj X :=
  ⟨{ toFun := fun x ↦ x
     map_add' := fun x y ↦ sectionsFunctor_map_lieAddHom (F := F) X x y
     map_smul' := fun _ _ ↦ rfl
     map_lie' := fun {x y} ↦ sectionsFunctor_map_lieBracketHom (F := F) X x y }⟩

end LieObj

end CategoryTheory.Sheaf

/-! ## The sheaf condition for a presheaf of Lie algebras -/

namespace CategoryTheory.Presheaf

open Opposite

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A presheaf of Lie algebras whose underlying presheaf of types is a sheaf is itself a sheaf.

Unlike `Presheaf.isSheaf_iff_isSheaf_forget`, this needs no size condition relating the universe
of the Lie algebras to the universes of the site: the Lie algebra operations are computed on
sections, and a sheaf is separated, so the amalgamation of a compatible family of morphisms of
Lie algebras is again a morphism of Lie algebras. -/
theorem isSheaf_lieAlgCat_of_isSheaf_forget (P : Cᵒᵖ ⥤ LieAlgCat.{w} k)
    (h : Presheaf.IsSheaf J (P ⋙ forget (LieAlgCat.{w} k))) : Presheaf.IsSheaf J P := by
  intro E X S hS y hy
  let cover : J.Cover X := ⟨S, hS⟩
  have hx : ∀ ⦃I₁ I₂ : cover.Arrow⦄ (r : I₁.Relation I₂),
      (↾(fun e ↦ (y I₁.f I₁.hf).hom e) :
          ToType E ⟶ (P ⋙ forget (LieAlgCat.{w} k)).obj (op I₁.Y)) ≫
          (P ⋙ forget (LieAlgCat.{w} k)).map r.g₁.op =
        ↾(fun e ↦ (y I₂.f I₂.hf).hom e) ≫ (P ⋙ forget (LieAlgCat.{w} k)).map r.g₂.op := by
    intro I₁ I₂ r
    ext e
    simpa using congrArg (fun φ ↦ LieAlgCat.Hom.hom φ e) (hy r.g₁ r.g₂ I₁.hf I₂.hf r.w)
  let t := h.amalgamate cover (fun I ↦ ↾(fun e ↦ (y I.f I.hf).hom e)) hx
  have ht : ∀ (I : cover.Arrow) (e : ToType E),
      (P.map I.f.op).hom (t e) = (y I.f I.hf).hom e := fun I e ↦ by
    simpa using ConcreteCategory.congr_hom (h.amalgamate_map cover _ hx I) e
  have key₁ : ∀ (e : ToType E) (c : ToType (P.obj (op X))),
      (∀ I : cover.Arrow, (y I.f I.hf).hom e = (P.map I.f.op).hom c) → t e = c := by
    intro e c hc
    refine eq_of_isSheaf h cover (fun I ↦ ?_)
    change (P.map I.f.op).hom _ = (P.map I.f.op).hom _
    rw [ht I, hc I]
  have key₂ : ∀ (F : ToType E → ToType E → ToType E)
      (G : ∀ L : LieAlgCat.{w} k, ToType L → ToType L → ToType L),
      (∀ (L L' : LieAlgCat.{w} k) (φ : L ⟶ L') (a b),
        φ.hom (G L a b) = G L' (φ.hom a) (φ.hom b)) →
      (∀ a b : ToType E, G E a b = F a b) →
      ∀ a b, t (F a b) = G (P.obj (op X)) (t a) (t b) := by
    intro F G hG hGF a b
    refine key₁ _ _ (fun I ↦ ?_)
    calc (y I.f I.hf).hom (F a b)
        = (y I.f I.hf).hom (G E a b) := by rw [hGF]
      _ = G _ ((y I.f I.hf).hom a) ((y I.f I.hf).hom b) := hG _ _ _ _ _
      _ = G _ ((P.map I.f.op).hom (t a)) ((P.map I.f.op).hom (t b)) := by rw [ht I a, ht I b]
      _ = (P.map I.f.op).hom (G _ (t a) (t b)) := (hG _ _ _ _ _).symm
  let amalgamation : E ⟶ P.obj (op X) :=
    ⟨{ toFun := fun e ↦ t e
       map_add' := key₂ (· + ·) (fun _ a b ↦ a + b)
         (fun _ _ φ a b ↦ map_add φ.hom a b) (fun _ _ ↦ rfl)
       map_smul' := fun c e ↦ key₂ (fun a _ ↦ c • a) (fun _ a _ ↦ c • a)
         (fun _ _ φ a _ ↦ map_smul φ.hom c a) (fun _ _ ↦ rfl) e e
       map_lie' := fun {a b} ↦ key₂ (fun a b ↦ ⁅a, b⁆) (fun _ a b ↦ ⁅a, b⁆)
         (fun _ _ φ a b ↦ φ.hom.map_lie a b) (fun _ _ ↦ rfl) a b }⟩
  refine ⟨amalgamation, ?_, ?_⟩
  · intro Y f hf
    exact LieAlgCat.hom_ext (LieHom.ext fun e ↦ ht ⟨Y, f, hf⟩ e)
  · intro t' ht'
    refine LieAlgCat.hom_ext (LieHom.ext fun e ↦ ?_)
    refine eq_of_isSheaf h cover (fun I ↦ ?_)
    change (P.map I.f.op).hom (t'.hom e) = (P.map I.f.op).hom (t e)
    rw [ht I]
    exact congrArg (fun φ ↦ LieAlgCat.Hom.hom φ e) (ht' I.f I.hf)

end CategoryTheory.Presheaf

/-! ## The inverse image of a sheaf of Lie algebras along a finite-product-preserving functor -/

namespace Stacks.Topos

open CategoryTheory.Sheaf CategoryTheory.Functor

variable {k : Type w} [Field k]

section PullbackLieSheaf

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget (LieAlgCat.{w} k))] [K.HasSheafCompose (forget (LieAlgCat.{w} k))]
  (Φ : Sheaf K (Type w) ⥤ Sheaf J (Type w)) [PreservesFiniteProducts Φ]
  (F : Sheaf K (LieAlgCat.{w} k))

/-- The presheaf of Lie algebras whose sections over `X` are the sections over `X` of `Φ` of the
underlying sheaf of sets of `F`, with the Lie algebra structure transported along the
finite-product-preserving functor `Φ` followed by the sections functor. -/
def pullbackLiePresheaf : Cᵒᵖ ⥤ LieAlgCat.{w} k where
  obj X := lieObj F (Φ ⋙ sectionsFunctor J X)
  map g := lieObjHom (whiskerLeft Φ (sectionsRestrict g))
  map_id X := by
    refine LieAlgCat.hom_ext (LieHom.ext fun x ↦ ?_)
    change (Φ.obj (lieSheaf F)).obj.map (𝟙 X) x = x
    exact (Φ.obj (lieSheaf F)).obj.map_id_apply X x
  map_comp {X Y Z} g h := by
    refine LieAlgCat.hom_ext (LieHom.ext fun x ↦ ?_)
    change (Φ.obj (lieSheaf F)).obj.map (g ≫ h) x =
      (Φ.obj (lieSheaf F)).obj.map h ((Φ.obj (lieSheaf F)).obj.map g x)
    exact (Φ.obj (lieSheaf F)).obj.map_comp_apply g h x

/-- The inverse image of a sheaf of Lie algebras along a finite-product-preserving functor
between categories of sheaves of sets. Its underlying sheaf of sets is `Φ` of the underlying
sheaf of sets of `F`. -/
def pullbackLieSheaf : Sheaf J (LieAlgCat.{w} k) :=
  ⟨pullbackLiePresheaf J Φ F,
    Presheaf.isSheaf_lieAlgCat_of_isSheaf_forget _ (Φ.obj (lieSheaf F)).property⟩

variable {F} {F' F'' : Sheaf K (LieAlgCat.{w} k)}

/-- The inverse image of a morphism of sheaves of Lie algebras along a finite-product-preserving
functor of sheaves of sets. Its underlying morphism of sheaves of sets is `Φ` of the underlying
morphism of sheaves of sets. -/
def pullbackLieSheafMap (a : F ⟶ F') : pullbackLieSheaf J Φ F ⟶ pullbackLieSheaf J Φ F' where
  hom :=
    { app := fun X ↦ lieObjMap (Φ ⋙ sectionsFunctor J X) a
      naturality := fun X Y g ↦ by
        refine LieAlgCat.hom_ext (LieHom.ext fun x ↦ ?_)
        change (Φ.map ((sheafCompose K (forget (LieAlgCat.{w} k))).map a)).hom.app Y
            ((Φ.obj (lieSheaf F)).obj.map g x) =
          (Φ.obj (lieSheaf F')).obj.map g
            ((Φ.map ((sheafCompose K (forget (LieAlgCat.{w} k))).map a)).hom.app X x)
        exact NatTrans.naturality_apply
          (Φ.map ((sheafCompose K (forget (LieAlgCat.{w} k))).map a)).hom g x }

/-- The underlying morphism of sheaves of sets of the inverse image of a morphism of sheaves of
Lie algebras is `Φ` of its underlying morphism of sheaves of sets. -/
@[simp]
lemma lieSheafMap_pullbackLieSheafMap (a : F ⟶ F') :
    (sheafCompose J (forget (LieAlgCat.{w} k))).map (pullbackLieSheafMap J Φ a) =
      Φ.map ((sheafCompose K (forget (LieAlgCat.{w} k))).map a) :=
  hom_ext_sections fun _ _ ↦ rfl

/-- The inverse image of sheaves of Lie algebras along a finite-product-preserving functor of
sheaves of sets, as a functor. -/
def pullbackLieFunctor : Sheaf K (LieAlgCat.{w} k) ⥤ Sheaf J (LieAlgCat.{w} k) where
  obj F := pullbackLieSheaf J Φ F
  map a := pullbackLieSheafMap J Φ a
  map_id F := by
    have h : Φ.map ((sheafCompose K (forget (LieAlgCat.{w} k))).map (𝟙 F)) =
        𝟙 (Φ.obj (lieSheaf F)) := by
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    refine (sheafCompose J (forget (LieAlgCat.{w} k))).map_injective
      (hom_ext_sections fun X s ↦ ?_)
    exact congrFun (congrArg (fun m ↦ m.hom.app X) h) s
  map_comp a b := by
    have h : Φ.map ((sheafCompose K (forget (LieAlgCat.{w} k))).map (a ≫ b)) =
        Φ.map ((sheafCompose K (forget (LieAlgCat.{w} k))).map a) ≫
          Φ.map ((sheafCompose K (forget (LieAlgCat.{w} k))).map b) := by
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    refine (sheafCompose J (forget (LieAlgCat.{w} k))).map_injective
      (hom_ext_sections fun X s ↦ ?_)
    exact congrFun (congrArg (fun m ↦ m.hom.app X) h) s

/-- On morphisms, the underlying morphism of sheaves of sets of `pullbackLieFunctor` is `Φ` of
the underlying morphism of sheaves of sets. -/
@[simp]
lemma lieSheafMap_pullbackLieFunctor_map (a : F ⟶ F') :
    (sheafCompose J (forget (LieAlgCat.{w} k))).map ((pullbackLieFunctor J Φ).map a) =
      Φ.map ((sheafCompose K (forget (LieAlgCat.{w} k))).map a) :=
  lieSheafMap_pullbackLieSheafMap J Φ a

/-! ### Transporting in one step and in two steps -/

variable {J} (Ψ : Sheaf J (Type w) ⥤ Type w) [PreservesFiniteProducts Ψ] (F)

/-- `Φ` of a transported binary operation is the product comparison followed by the
corresponding operation of the inverse-image sheaf of Lie algebras, provided that operation is
computed on sections by transport. -/
lemma map_lieBinHom (op : ∀ L : LieAlgCat.{w} k, L → L → L)
    (hop : ∀ {L M : LieAlgCat.{w} k} (φ : L ⟶ M) (a b : L),
      φ.hom (op L a b) = op M (φ.hom a) (φ.hom b))
    (hcomp : ∀ (X : Cᵒᵖ) (a b : (pullbackLieSheaf J Φ F).obj.obj X),
      op _ a b = lieBinObj F (Φ ⋙ sectionsFunctor J X) op hop a b) :
    Φ.map (lieBinHom F op hop) =
      Limits.prodComparison Φ (lieSheaf F) (lieSheaf F) ≫
        lieBinHom (pullbackLieSheaf J Φ F) op hop := by
  refine hom_ext_sections fun X q ↦ ?_
  have h₁ := map_prodComparison_apply (P := sectionsFunctor J X) Φ (lieSheaf F) (lieSheaf F) q
  have h₂ := sectionsFunctor_map_lieBinHom (F := pullbackLieSheaf J Φ F) op hop X
    ((Φ ⋙ sectionsFunctor J X).map (Limits.prod.fst (X := lieSheaf F) (Y := lieSheaf F)) q)
    ((Φ ⋙ sectionsFunctor J X).map (Limits.prod.snd (X := lieSheaf F) (Y := lieSheaf F)) q)
  have h₃ := hcomp X
    ((Φ ⋙ sectionsFunctor J X).map (Limits.prod.fst (X := lieSheaf F) (Y := lieSheaf F)) q)
    ((Φ ⋙ sectionsFunctor J X).map (Limits.prod.snd (X := lieSheaf F) (Y := lieSheaf F)) q)
  have h₄ := prodObjMk_map_fst_map_snd (P := Φ ⋙ sectionsFunctor J X) q
  exact (congrArg ((Φ ⋙ sectionsFunctor J X).map (lieBinHom F op hop)) h₄).symm.trans
    (h₃.symm.trans (h₂.symm.trans
      (congrArg ((sectionsFunctor J X).map (lieBinHom (pullbackLieSheaf J Φ F) op hop))
        h₁.symm)))

/-- A transported binary operation on the inverse-image sheaf of Lie algebras, transported
once more along `Ψ`, is the operation of `F` transported along `Φ ⋙ Ψ`. -/
lemma lieBinObj_pullbackLieSheaf (op : ∀ L : LieAlgCat.{w} k, L → L → L)
    (hop : ∀ {L M : LieAlgCat.{w} k} (φ : L ⟶ M) (a b : L),
      φ.hom (op L a b) = op M (φ.hom a) (φ.hom b))
    (hcomp : ∀ (X : Cᵒᵖ) (a b : (pullbackLieSheaf J Φ F).obj.obj X),
      op _ a b = lieBinObj F (Φ ⋙ sectionsFunctor J X) op hop a b)
    (x y : Ψ.obj (Φ.obj (lieSheaf F))) :
    lieBinObj (pullbackLieSheaf J Φ F) Ψ op hop x y = lieBinObj F (Φ ⋙ Ψ) op hop x y := by
  have h := map_lieBinHom Φ F op hop hcomp
  have h₁ := map_prodComparison_apply (P := Ψ) Φ (lieSheaf F) (lieSheaf F)
    (prodObjMk (P := Φ ⋙ Ψ) (A := lieSheaf F) (B := lieSheaf F) x y)
  rw [map_fst_prodObjMk, map_snd_prodObjMk] at h₁
  exact (congrArg (Ψ.map (lieBinHom (pullbackLieSheaf J Φ F) op hop)) h₁.symm).trans
    ((Ψ.map_comp_apply (Limits.prodComparison Φ (lieSheaf F) (lieSheaf F))
      (lieBinHom (pullbackLieSheaf J Φ F) op hop)
      (prodObjMk (P := Φ ⋙ Ψ) (A := lieSheaf F) (B := lieSheaf F) x y)).symm.trans
    (congrArg (fun m ↦ Ψ.map m
      (prodObjMk (P := Φ ⋙ Ψ) (A := lieSheaf F) (B := lieSheaf F) x y)) h).symm)

omit [PreservesFiniteProducts Ψ] in
/-- A transported unary operation on the inverse-image sheaf of Lie algebras, transported once
more along `Ψ`, is the operation of `F` transported along `Φ ⋙ Ψ`. -/
lemma lieUnObj_pullbackLieSheaf (uop : ∀ L : LieAlgCat.{w} k, L → L)
    (huop : ∀ {L M : LieAlgCat.{w} k} (φ : L ⟶ M) (a : L), φ.hom (uop L a) = uop M (φ.hom a))
    (hcomp : ∀ (X : Cᵒᵖ) (a : (pullbackLieSheaf J Φ F).obj.obj X),
      uop _ a = lieUnObj F (Φ ⋙ sectionsFunctor J X) uop huop a)
    (x : Ψ.obj (Φ.obj (lieSheaf F))) :
    lieUnObj (pullbackLieSheaf J Φ F) Ψ uop huop x = lieUnObj F (Φ ⋙ Ψ) uop huop x := by
  have h : Φ.map (lieUnHom F uop huop) = lieUnHom (pullbackLieSheaf J Φ F) uop huop :=
    hom_ext_sections fun X q ↦ (hcomp X q).symm
  exact (congrArg (fun m ↦ Ψ.map m x) h).symm

/-- The Lie algebra transported along `Ψ` from the inverse-image sheaf of Lie algebras maps by
the identity to the Lie algebra transported along `Φ ⋙ Ψ` from `F`. -/
def lieObjPullbackHom : lieObj (pullbackLieSheaf J Φ F) Ψ ⟶ lieObj F (Φ ⋙ Ψ) :=
  ⟨{ toFun := fun x ↦ x
     map_add' := lieBinObj_pullbackLieSheaf Φ F Ψ (fun _ a b ↦ a + b)
       (fun φ a b ↦ map_add φ.hom a b) (fun _ _ _ ↦ rfl)
     map_smul' := fun c ↦ lieUnObj_pullbackLieSheaf Φ F Ψ (fun _ a ↦ c • a)
        (fun φ a ↦ map_smul φ.hom c a) (fun _ _ ↦ rfl)
     map_lie' := fun {_ _} ↦ lieBinObj_pullbackLieSheaf Φ F Ψ (fun _ a b ↦ ⁅a, b⁆)
        (fun φ a b ↦ φ.hom.map_lie a b) (fun _ _ _ ↦ rfl) _ _ }⟩

/-- The identity, read as a morphism of Lie algebras from the Lie algebra transported along
`Φ ⋙ Ψ` from `F` to the Lie algebra transported along `Ψ` from the inverse-image sheaf of Lie
algebras. -/
def lieObjPullbackInv : lieObj F (Φ ⋙ Ψ) ⟶ lieObj (pullbackLieSheaf J Φ F) Ψ :=
  ⟨{ toFun := fun x ↦ x
     map_add' := fun x y ↦ (lieBinObj_pullbackLieSheaf Φ F Ψ (fun _ a b ↦ a + b)
       (fun φ a b ↦ map_add φ.hom a b) (fun _ _ _ ↦ rfl) x y).symm
     map_smul' := fun c x ↦ (lieUnObj_pullbackLieSheaf Φ F Ψ (fun _ a ↦ c • a)
        (fun φ a ↦ map_smul φ.hom c a) (fun _ _ ↦ rfl) x).symm
     map_lie' := fun {x y} ↦ (lieBinObj_pullbackLieSheaf Φ F Ψ (fun _ a b ↦ ⁅a, b⁆)
        (fun φ a b ↦ φ.hom.map_lie a b) (fun _ _ _ ↦ rfl) x y).symm }⟩

end PullbackLieSheaf

/-! ## The adjunction along a morphism of topoi -/

section Adjunction

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget (LieAlgCat.{w} k))] [K.HasSheafCompose (forget (LieAlgCat.{w} k))]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))

/-- The inverse image of sheaves of Lie algebras along a morphism of topoi. -/
abbrev inverseImageLieFunctor : Sheaf K (LieAlgCat.{w} k) ⥤ Sheaf J (LieAlgCat.{w} k) :=
  pullbackLieFunctor J f.inverseImage

/-- The direct image of sheaves of Lie algebras along a morphism of topoi. -/
abbrev pushforwardLieFunctor : Sheaf J (LieAlgCat.{w} k) ⥤ Sheaf K (LieAlgCat.{w} k) :=
  pullbackLieFunctor K f.pushforward

/-- The unit `F ⟶ f_*f⁻¹F` of sheaves of Lie algebras. Its underlying morphism of sheaves of
sets is the unit of `f⁻¹ ⊣ f_*` at the underlying sheaf of sets of `F`. -/
def lieUnit (F : Sheaf K (LieAlgCat.{w} k)) :
    F ⟶ (pushforwardLieFunctor f).obj ((inverseImageLieFunctor f).obj F) where
  hom :=
    { app := fun X ↦ sectionsToLieObj F X ≫
        lieObjHom (F := F) (whiskerRight f.adj.unit (sectionsFunctor K X)) ≫
        lieObjPullbackInv f.inverseImage F (f.pushforward ⋙ sectionsFunctor K X)
      naturality := fun X Y g ↦ by
        refine LieAlgCat.hom_ext (LieHom.ext fun x ↦ ?_)
        exact NatTrans.naturality_apply (f.adj.unit.app (lieSheaf F)).hom g x }

/-- The underlying morphism of sheaves of sets of `lieUnit f F` is the unit of `f⁻¹ ⊣ f_*`. -/
lemma lieSheafMap_lieUnit (F : Sheaf K (LieAlgCat.{w} k)) :
    (sheafCompose K (forget (LieAlgCat.{w} k))).map (lieUnit f F) =
      f.adj.unit.app (lieSheaf F) :=
  hom_ext_sections fun _ _ ↦ rfl

/-- The counit `f⁻¹f_*G ⟶ G` of sheaves of Lie algebras. Its underlying morphism of sheaves of
sets is the counit of `f⁻¹ ⊣ f_*` at the underlying sheaf of sets of `G`. -/
def lieCounit (G : Sheaf J (LieAlgCat.{w} k)) :
    (inverseImageLieFunctor f).obj ((pushforwardLieFunctor f).obj G) ⟶ G where
  hom :=
    { app := fun X ↦ lieObjPullbackHom f.pushforward G (f.inverseImage ⋙ sectionsFunctor J X) ≫
        lieObjHom (F := G) (whiskerRight f.adj.counit (sectionsFunctor J X)) ≫
        lieObjToSections G X
      naturality := fun X Y g ↦ by
        refine LieAlgCat.hom_ext (LieHom.ext fun x ↦ ?_)
        exact NatTrans.naturality_apply (f.adj.counit.app (lieSheaf G)).hom g x }

/-- The underlying morphism of sheaves of sets of `lieCounit f G` is the counit of
`f⁻¹ ⊣ f_*`. -/
lemma lieSheafMap_lieCounit (G : Sheaf J (LieAlgCat.{w} k)) :
    (sheafCompose J (forget (LieAlgCat.{w} k))).map (lieCounit f G) =
      f.adj.counit.app (lieSheaf G) :=
  hom_ext_sections fun _ _ ↦ rfl

/-- The inverse image of sheaves of Lie algebras along a morphism of topoi is left adjoint to the
direct image, with `lieUnit` and `lieCounit` as unit and counit. -/
def lieImageAdjunction : inverseImageLieFunctor (k := k) f ⊣ pushforwardLieFunctor f :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app := lieUnit f
          naturality := fun F F' a ↦ by
            have h := f.adj.unit.naturality ((sheafCompose K (forget (LieAlgCat.{w} k))).map a)
            refine (sheafCompose K (forget (LieAlgCat.{w} k))).map_injective
              (hom_ext_sections fun X s ↦ ?_)
            exact congrFun (congrArg (fun m ↦ m.hom.app X) h) s }
      counit :=
        { app := lieCounit f
          naturality := fun G G' a ↦ by
            have h := f.adj.counit.naturality ((sheafCompose J (forget (LieAlgCat.{w} k))).map a)
            refine (sheafCompose J (forget (LieAlgCat.{w} k))).map_injective
              (hom_ext_sections fun X s ↦ ?_)
            exact congrFun (congrArg (fun m ↦ m.hom.app X) h) s }
      left_triangle := by
        refine NatTrans.ext (funext fun F ↦ ?_)
        have h := f.adj.left_triangle_components (lieSheaf F)
        refine (sheafCompose J (forget (LieAlgCat.{w} k))).map_injective
          (hom_ext_sections fun X s ↦ ?_)
        exact congrFun (congrArg (fun m ↦ m.hom.app X) h) s
      right_triangle := by
        refine NatTrans.ext (funext fun G ↦ ?_)
        have h := f.adj.right_triangle_components (lieSheaf G)
        refine (sheafCompose K (forget (LieAlgCat.{w} k))).map_injective
          (hom_ext_sections fun X s ↦ ?_)
        exact congrFun (congrArg (fun m ↦ m.hom.app X) h) s }

/-- The unit of `lieImageAdjunction f` at `F` is `lieUnit f F`. -/
@[simp]
lemma lieImageAdjunction_unit_app (F : Sheaf K (LieAlgCat.{w} k)) :
    (lieImageAdjunction f).unit.app F = lieUnit f F := rfl

/-- The counit of `lieImageAdjunction f` at `G` is `lieCounit f G`. -/
@[simp]
lemma lieImageAdjunction_counit_app (G : Sheaf J (LieAlgCat.{w} k)) :
    (lieImageAdjunction f).counit.app G = lieCounit f G := rfl

variable (k)

/-- **Stacks 00YV, case of Lie algebras over a field `k`.** A morphism of topoi
`f : Sh(C) → Sh(D)` induces an adjoint pair `f⁻¹ ⊣ f_*` on sheaves of Lie algebras over `k`,
compatible with taking the underlying sheaves of sets: the underlying sheaf of sets of `f⁻¹F`,
resp. `f_*G`, is `f⁻¹`, resp. `f_*`, of the underlying sheaf of sets, and the unit of the
adjunction on sheaves of Lie algebras is the unit of `f⁻¹ ⊣ f_*` on sheaves of sets. -/
def lieAlgebraStructureAdjunction :
    StructureAdjunction f (forget (LieAlgCat.{w} k)) where
  inverseImage := inverseImageLieFunctor f
  pushforward := pushforwardLieFunctor f
  adj := lieImageAdjunction f
  inverseImageForgetIso :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ hom_ext_sections fun _ _ ↦ rfl)
  pushforwardForgetIso :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ hom_ext_sections fun _ _ ↦ rfl)
  forget_map_unit_app F := by
    have h : f.pushforward.map (𝟙 (f.inverseImage.obj (lieSheaf F))) = 𝟙 _ :=
      f.pushforward.map_id _
    refine hom_ext_sections fun X s ↦ ?_
    exact congrFun (congrArg (fun m ↦ m.hom.app X) h)
      ((f.adj.unit.app (lieSheaf F)).hom.app X s)

end Adjunction

end Stacks.Topos
