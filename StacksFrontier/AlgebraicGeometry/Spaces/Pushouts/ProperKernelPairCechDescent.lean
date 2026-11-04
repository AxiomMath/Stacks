module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.DescentDataSheaves
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairCech

/-!
# Compatible étale diagrams over a Čech nerve are descent data

Let `p : Y ⟶ X'` be a morphism of algebraic spaces over `S`. An object of the limit of the small
étale sites of the terms of the Čech nerve of `p`, in the form of
`AlgebraicGeometry.Space.CompatibleEtaleDiagram`, is a simplicial algebraic space `E` étale over
the Čech nerve with cartesian transition squares. Its degree-zero term `E₀`, a space étale over
`Y`, carries a descent datum relative to `p`: a point `v` of `E₀` and a point `y` of `Y` with the
same image in `X'` give a point of `Y ×_{X'} Y`, which lifts to the unique point of `E₁` over it
whose first face is `v`, and the second face of that lift is the moved point. The cocycle
condition is read off `E₂`. This is the dictionary by which Stacks 0GG0 enters condition (1) of
Stacks 0GHL in the proof of Stacks 0AGG.

## Main definitions

* `AlgebraicGeometry.Space.cechPt`: a point of a term of the Čech nerve, from its components.
* `AlgebraicGeometry.Space.CompatibleEtaleDiagram.cechTransport` and
  `AlgebraicGeometry.Space.CompatibleEtaleDiagram.cechDescentData`: the move operation of a
  compatible étale diagram over the Čech nerve, and its descent datum relative to `p`.

## References

* [Stacks Project, Tag 0GHL](https://stacks.math.columbia.edu/tag/0GHL)
* [Stacks Project, Tag 0GG0](https://stacks.math.columbia.edu/tag/0GG0)
* [Stacks Project, Tag 0AGG](https://stacks.math.columbia.edu/tag/0AGG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} (p : Y ⟶ X)

/-! ### Points of the Čech nerve -/

/-- A point of the degree-`n` term of the Čech nerve of `p`, given by its `n + 1` components
with a common image in `X'`. -/
abbrev cechPt {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {n : ℕ} (b : Z ⟶ X.obj)
    (y : Fin (n + 1) → (Z ⟶ Y.obj)) (h : ∀ i, y i ≫ p.hom = b) :
    Z ⟶ ((cechNerveSpace p).obj (op ⦋n⦌)).obj :=
  WidePullback.lift (arrows := fun _ : Fin (n + 1) => p.hom) b y h

/-- The components of `AlgebraicGeometry.Space.cechPt` are the given points. -/
@[reassoc (attr := simp)]
theorem cechPt_proj {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {n : ℕ} (b : Z ⟶ X.obj)
    (y : Fin (n + 1) → (Z ⟶ Y.obj)) (h : ∀ i, y i ≫ p.hom = b) (i : Fin (n + 1)) :
    cechPt p b y h ≫ (cechProj p (n := op ⦋n⦌) i).hom = y i :=
  WidePullback.lift_π _ _ _ _ _

/-- The image in `X'` of `AlgebraicGeometry.Space.cechPt` is the given point. -/
@[reassoc (attr := simp)]
theorem cechPt_base {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {n : ℕ} (b : Z ⟶ X.obj)
    (y : Fin (n + 1) → (Z ⟶ Y.obj)) (h : ∀ i, y i ≫ p.hom = b) :
    cechPt p b y h ≫ (cechBase p (op ⦋n⦌)).hom = b :=
  WidePullback.lift_base _ _ _ _

/-- `AlgebraicGeometry.Space.cechProj_comp`, as a statement about presheaves. -/
private theorem hom_cechProj_comp {n : SimplexCategoryᵒᵖ} (i : Fin (n.unop.len + 1)) :
    (cechProj p i).hom ≫ p.hom = (cechBase p n).hom :=
  congrArg (fun k => k.hom) (cechProj_comp p i)

/-- `AlgebraicGeometry.Space.cechNerveSpace_map_cechProj`, as a statement about presheaves. -/
private theorem hom_map_cechProj {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (i : Fin (m.unop.len + 1)) :
    ((cechNerveSpace p).map θ).hom ≫ (cechProj p i).hom = (cechProj p (θ.unop.toOrderHom i)).hom :=
  congrArg (fun k => k.hom) (cechNerveSpace_map_cechProj p θ i)

/-- Two points of a term of the Čech nerve with the same components are equal. -/
theorem cech_hom_ext {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {n : ℕ}
    {f g : Z ⟶ ((cechNerveSpace p).obj (op ⦋n⦌)).obj}
    (h : ∀ i : Fin (n + 1), f ≫ (cechProj p (n := op ⦋n⦌) i).hom =
      g ≫ (cechProj p (n := op ⦋n⦌) i).hom) : f = g := by
  refine WidePullback.hom_ext (fun _ : Fin (n + 1) => p.hom) _ _ h ?_
  have h0 := congrArg (· ≫ p.hom) (h 0)
  have e := hom_cechProj_comp p (n := op ⦋n⦌) 0
  simp only [Category.assoc] at h0
  show f ≫ (cechBase p (op ⦋n⦌)).hom = g ≫ (cechBase p (op ⦋n⦌)).hom
  rwa [← e]

/-- The transition of the Čech nerve along `θ` reindexes the components of a point by `θ`. -/
@[reassoc (attr := simp)]
theorem cechPt_map {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {n m : ℕ} (b : Z ⟶ X.obj)
    (y : Fin (n + 1) → (Z ⟶ Y.obj)) (h : ∀ i, y i ≫ p.hom = b) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    cechPt p b y h ≫ ((cechNerveSpace p).map θ.op).hom =
      cechPt p b (fun i => y (θ.toOrderHom i)) (fun _ => h _) := by
  refine cech_hom_ext p fun i => ?_
  rw [Category.assoc, cechPt_proj]
  exact (congrArg (cechPt p b y h ≫ ·) (hom_map_cechProj p θ.op i)).trans (cechPt_proj p b y h _)

/-- The projection of the degree-zero term of the Čech nerve to `Y` is an isomorphism. -/
instance : IsIso (cechProj p (n := op ⦋0⦌) 0) :=
  ⟨⟨cechZeroSection p, ObjectProperty.hom_ext _ (cech_hom_ext p fun i => by
      fin_cases i
      exact congrArg (fun k => k.hom)
        ((Category.assoc _ _ _).trans ((congrArg (cechProj p 0 ≫ ·)
          (cechZeroSection_cechProj p 0)).trans ((Category.comp_id _).trans
            (Category.id_comp _).symm)))),
    cechZeroSection_cechProj p 0⟩⟩

/-! ### Fibre descent data -/

/-- The move operation of the descent datum of a sheaf over `X'` is that of its fibre
products. -/
theorem fibreDescentData_transport_move (G : Descent.SheavesWithSpaceFibres
      (fun _ : PUnit.{1} => p.hom)) {Z : Over X.obj}
    (v : Z ⟶ (Over.map p.hom).obj ((Descent.fibreDescentData (fun _ : PUnit.{1} => p.hom)
      X.property (fun _ => Y.property) G).obj PUnit.unit))
    (y : Z ⟶ Over.mk p.hom) :
    (Descent.fibreDescentData (fun _ : PUnit.{1} => p.hom) X.property (fun _ => Y.property)
        G).transport.move (i := PUnit.unit) (j := PUnit.unit) v y =
      Descent.fibreMove (fun _ : PUnit.{1} => p.hom) G.obj (i := PUnit.unit) (j := PUnit.unit)
        v y := by
  refine (Descent.DescentData.transport_move _ v y).trans ?_
  exact (congrArg (prod.lift v y ≫ ·) (prod.lift_snd _ _)).trans
    (((Descent.fibreTransport (fun _ : PUnit.{1} => p.hom) G.obj).comp_move (prod.lift v y)
      prod.fst prod.snd).trans (congrArg₂ (fun a b =>
        (Descent.fibreTransport (fun _ : PUnit.{1} => p.hom) G.obj).move (i := PUnit.unit)
          (j := PUnit.unit) a b) (prod.lift_fst v y) (prod.lift_snd v y)))

/-- The sheaf over `X'` underlying an algebraic space over `X'`. -/
abbrev sheafOf (V : Descent.AlgebraicSpacesOver (B := B) (S := S) (hS := hS) X.obj) :
    Descent.SheavesWithSpaceFibres (fun _ : PUnit.{1} => p.hom) :=
  (Descent.algebraicSpacesOverToSheaves (fun _ : PUnit.{1} => p.hom) X.property
    (fun _ => Y.property)).obj V

/-- The fibre descent datum of an algebraic space over `X'`, relative to `p`. -/
abbrev fibreDatum (V : Descent.AlgebraicSpacesOver (B := B) (S := S) (hS := hS) X.obj) :
    Descent.HomDescentData.{u, 0} p.hom X.property Y.property :=
  (Descent.fibreDescentFunctor (fun _ : PUnit.{1} => p.hom) X.property
    (fun _ => Y.property)).obj (sheafOf p V)

/-- The degree-zero term of the Čech nerve is `Y`, as presheaves. -/
def cechZeroIso : ((cechNerveSpace p).obj (op ⦋0⦌)).obj ≅ Y.obj where
  hom := (cechProj p (n := op ⦋0⦌) 0).hom
  inv := (cechZeroSection p).hom
  hom_inv_id := cech_hom_ext p fun i => by
    obtain rfl := Fin.fin_one_eq_zero i
    rw [Category.assoc]
    exact (congrArg ((cechProj p (n := op ⦋0⦌) 0).hom ≫ ·)
      (congrArg (fun k => k.hom) (cechZeroSection_cechProj p 0))).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)
  inv_hom_id := congrArg (fun k => k.hom) (cechZeroSection_cechProj p 0)

/-! ### The descent datum of a compatible étale diagram -/

namespace CompatibleEtaleDiagram

variable {p} {B₀ : AlgebraicSpaces B S hS} {ν : X ⟶ B₀}
  (E : CompatibleEtaleDiagram B S hS (cechDiagram p ν))

/-- The vertex `j` of `⦋n⦌`, as a morphism of `SimplexCategoryᵒᵖ`. -/
abbrev vtx (n : ℕ) (j : Fin (n + 1)) : op ⦋n⦌ ⟶ op ⦋0⦌ :=
  (SimplexCategory.const ⦋0⦌ ⦋n⦌ j).op

/-- The degree-`n` term of `E`, as a presheaf. -/
abbrev term (n : ℕ) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := (E.U.obj (op ⦋n⦌)).obj

/-- The structure morphism of the degree-`n` term of `E` to the Čech nerve. -/
abbrev proj (n : ℕ) : E.term n ⟶ ((cechNerveSpace p).obj (op ⦋n⦌)).obj :=
  (E.projection.app (op ⦋n⦌)).hom

/-- The transition morphism of `E` along a morphism of `SimplexCategory`. -/
abbrev tr {n m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) : E.term n ⟶ E.term m := (E.U.map θ.op).hom

/-- The transitions of `E` compose. -/
theorem tr_comp {n m k : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (θ' : ⦋k⦌ ⟶ ⦋m⦌) :
    E.tr θ ≫ E.tr θ' = E.tr (θ' ≫ θ) := by
  show (E.U.map θ.op ≫ E.U.map θ'.op).hom = _
  rw [← Functor.map_comp]
  rfl

/-- The transitions of `E` lie over those of the Čech nerve. -/
theorem tr_proj {n m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    E.tr θ ≫ E.proj m = E.proj n ≫ ((cechNerveSpace p).map θ.op).hom :=
  congrArg (fun k => k.hom) (E.projection.naturality θ.op)

/-- The transition squares of `E`, as cartesian squares of presheaves. -/
theorem isPullback_tr {n m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    IsPullback (E.tr θ) (E.proj n) (E.proj m) ((cechNerveSpace p).map θ.op).hom :=
  AlgebraicSpaces.isPullback_hom B S hS (E.cartesian θ.op)

/-- The structure morphism `E₀ ⟶ Y`. -/
abbrev toY : E.term 0 ⟶ Y.obj := E.proj 0 ≫ (cechProj p (n := op ⦋0⦌) 0).hom

/-- The vertex `j` of a point of `Eₙ`, mapped to `Y`, is the `j`th component of its image in
the Čech nerve. -/
theorem tr_toY {n : ℕ} (j : Fin (n + 1)) :
    E.tr (SimplexCategory.const ⦋0⦌ ⦋n⦌ j) ≫ E.toY =
      E.proj n ≫ (cechProj p (n := op ⦋n⦌) j).hom := by
  rw [← Category.assoc, E.tr_proj, Category.assoc]
  exact congrArg (E.proj n ≫ ·) (hom_map_cechProj p (SimplexCategory.const ⦋0⦌ ⦋n⦌ j).op 0)

/-- The condition for a point of `E₀` and a point of the degree-`n` term of the Čech nerve to
lift to `Eₙ` through the vertex `0`. -/
theorem lift_cond {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {n : ℕ} (v : Z ⟶ E.term 0)
    (d : Z ⟶ ((cechNerveSpace p).obj (op ⦋n⦌)).obj)
    (h : v ≫ E.toY = d ≫ (cechProj p (n := op ⦋n⦌) 0).hom) :
    v ≫ E.proj 0 = d ≫ ((cechNerveSpace p).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op).hom := by
  refine cech_hom_ext p fun i => ?_
  obtain rfl : i = 0 := Fin.fin_one_eq_zero i
  refine ((Category.assoc _ _ _).trans h).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact (congrArg (d ≫ ·) (hom_map_cechProj p (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op 0)).symm

/-- The lift of a point of `E₀` along a point of the degree-`n` term of the Čech nerve with the
same vertex `0`. -/
def liftPt {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {n : ℕ} (v : Z ⟶ E.term 0)
    (d : Z ⟶ ((cechNerveSpace p).obj (op ⦋n⦌)).obj)
    (h : v ≫ E.toY = d ≫ (cechProj p (n := op ⦋n⦌) 0).hom) : Z ⟶ E.term n :=
  (E.isPullback_tr (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)).lift v d (E.lift_cond v d h)

/-- The vertex `0` of `AlgebraicGeometry.Space.CompatibleEtaleDiagram.liftPt` is the given point
of `E₀`. -/
@[reassoc (attr := simp)]
theorem liftPt_tr {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {n : ℕ} (v : Z ⟶ E.term 0)
    (d : Z ⟶ ((cechNerveSpace p).obj (op ⦋n⦌)).obj)
    (h : v ≫ E.toY = d ≫ (cechProj p (n := op ⦋n⦌) 0).hom) :
    E.liftPt v d h ≫ E.tr (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) = v :=
  IsPullback.lift_fst _ _ _ _

/-- The image in the Čech nerve of `AlgebraicGeometry.Space.CompatibleEtaleDiagram.liftPt` is
the given point. -/
@[reassoc (attr := simp)]
theorem liftPt_proj {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {n : ℕ} (v : Z ⟶ E.term 0)
    (d : Z ⟶ ((cechNerveSpace p).obj (op ⦋n⦌)).obj)
    (h : v ≫ E.toY = d ≫ (cechProj p (n := op ⦋n⦌) 0).hom) :
    E.liftPt v d h ≫ E.proj n = d :=
  IsPullback.lift_snd _ _ _ _

/-- A point of `Eₙ` with the given vertex `0` and image in the Čech nerve is
`AlgebraicGeometry.Space.CompatibleEtaleDiagram.liftPt`. -/
theorem eq_liftPt {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {n : ℕ} (v : Z ⟶ E.term 0)
    (d : Z ⟶ ((cechNerveSpace p).obj (op ⦋n⦌)).obj)
    (h : v ≫ E.toY = d ≫ (cechProj p (n := op ⦋n⦌) 0).hom) (e : Z ⟶ E.term n)
    (he : e ≫ E.tr (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) = v) (hd : e ≫ E.proj n = d) :
    e = E.liftPt v d h :=
  (E.isPullback_tr _).hom_ext (he.trans (E.liftPt_tr v d h).symm)
    (hd.trans (E.liftPt_proj v d h).symm)

/-- The component of the descent datum: `E₀` as a space over `Y`. -/
abbrev obj₀ : Over Y.obj := Over.mk E.toY

/-- A point of `E₀` over `X'`, mapped to `Y` and then to `X'`, is its structure morphism. -/
theorem toY_comp {Z : Over X.obj} (v : Z ⟶ (Over.map p.hom).obj E.obj₀) :
    (v.left ≫ E.toY) ≫ p.hom = Z.hom :=
  (Category.assoc _ _ _).trans (Over.w v)

/-- The point of `Y ×_{X'} Y` with components the image of `v` in `Y` and `y`. -/
abbrev movePt {Z : Over X.obj} (v : Z ⟶ (Over.map p.hom).obj E.obj₀) (y : Z ⟶ Over.mk p.hom) :
    Z.left ⟶ ((cechNerveSpace p).obj (op ⦋1⦌)).obj :=
  cechPt p Z.hom ![v.left ≫ E.toY, y.left] (fun i => by
    fin_cases i
    · exact E.toY_comp v
    · exact Over.w y)

/-- The lift of `v` to `E₁` over the point `(v, y)` of `Y ×_{X'} Y`. -/
abbrev moveLift {Z : Over X.obj} (v : Z ⟶ (Over.map p.hom).obj E.obj₀) (y : Z ⟶ Over.mk p.hom) :
    Z.left ⟶ E.term 1 :=
  E.liftPt v.left (E.movePt v y) (by simp)

/-- The vertex `1` of `AlgebraicGeometry.Space.CompatibleEtaleDiagram.moveLift v y`, mapped to
`Y`, is `y`. -/
theorem moveLift_toY {Z : Over X.obj} (v : Z ⟶ (Over.map p.hom).obj E.obj₀)
    (y : Z ⟶ Over.mk p.hom) :
    E.moveLift v y ≫ E.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) ≫ E.toY = y.left := by
  rw [E.tr_toY, liftPt_proj_assoc, cechPt_proj]
  rfl

/-- The move operation of `E`: `v` is carried to the second vertex of its lift to `E₁`. -/
def cechMove {Z : Over X.obj} (v : Z ⟶ (Over.map p.hom).obj E.obj₀) (y : Z ⟶ Over.mk p.hom) :
    Z ⟶ (Over.map p.hom).obj E.obj₀ :=
  Over.homMk (E.moveLift v y ≫ E.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)) (by
    change (E.moveLift v y ≫ E.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)) ≫ E.toY ≫ p.hom = Z.hom
    calc _ = (E.moveLift v y ≫ E.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) ≫ E.toY) ≫ p.hom := by
          simp only [Category.assoc]
      _ = y.left ≫ p.hom := by rw [E.moveLift_toY]
      _ = Z.hom := Over.w y)

/-- The underlying morphism of `AlgebraicGeometry.Space.CompatibleEtaleDiagram.cechMove`. -/
@[simp]
theorem cechMove_left {Z : Over X.obj} (v : Z ⟶ (Over.map p.hom).obj E.obj₀)
    (y : Z ⟶ Over.mk p.hom) :
    (E.cechMove v y).left = E.moveLift v y ≫ E.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) :=
  rfl

/-- The transition of `E` along an identity is the identity. -/
theorem tr_id (n : ℕ) : E.tr (𝟙 ⦋n⦌) = 𝟙 _ := by
  show (E.U.map (𝟙 (op ⦋n⦌))).hom = _
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- Equal morphisms of `SimplexCategory` give equal transitions of `E`. -/
theorem tr_congr {n m : ℕ} {θ θ' : ⦋m⦌ ⟶ ⦋n⦌} (h : θ = θ') : E.tr θ = E.tr θ' := by
  subst h; rfl

/-- The transition of `E` along an endomorphism of `⦋0⦌` is the identity. -/
theorem tr_zero (f : ⦋0⦌ ⟶ ⦋0⦌) : E.tr f = 𝟙 _ := by
  rw [E.tr_congr (SimplexCategory.Hom.ext_zero_left f (𝟙 _) (Fin.fin_one_eq_zero _)), E.tr_id]

/-- `AlgebraicGeometry.Space.CompatibleEtaleDiagram.tr_comp`, with a `reassoc` form. -/
@[reassoc] alias tr_comp_assoc' := tr_comp

/-- `AlgebraicGeometry.Space.CompatibleEtaleDiagram.moveLift` is natural in the point of `X'`. -/
theorem comp_moveLift {Z W : Over X.obj} (k : W ⟶ Z) (v : Z ⟶ (Over.map p.hom).obj E.obj₀)
    (y : Z ⟶ Over.mk p.hom) :
    k.left ≫ E.moveLift v y = E.moveLift (k ≫ v) (k ≫ y) := by
  refine E.eq_liftPt _ _ _ _ (by rw [Category.assoc, liftPt_tr]; rfl) ?_
  rw [Category.assoc, liftPt_proj]
  refine cech_hom_ext p fun i => ?_
  fin_cases i <;> (simp only [Category.assoc, cechPt_proj]; rfl)

/-- A point of `E₁` with vertex `0` equal to `v` and vertex `1` over `y` is
`AlgebraicGeometry.Space.CompatibleEtaleDiagram.moveLift v y`. -/
theorem moveLift_eq_of_move {Z : Over X.obj} (v : Z ⟶ (Over.map p.hom).obj E.obj₀)
    (y : Z ⟶ Over.mk p.hom) (e : Z.left ⟶ E.term 1)
    (h₀ : e ≫ E.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) = v.left)
    (h₁ : e ≫ E.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) ≫ E.toY = y.left) :
    e = E.moveLift v y := by
  have c0 : e ≫ E.proj 1 ≫ (cechProj p (n := op ⦋1⦌) 0).hom = v.left ≫ E.toY := by
    rw [← E.tr_toY, ← Category.assoc, h₀]
  have c1 : e ≫ E.proj 1 ≫ (cechProj p (n := op ⦋1⦌) 1).hom = y.left := by
    rwa [← E.tr_toY]
  refine E.eq_liftPt _ _ _ e h₀ ?_
  refine cech_hom_ext p fun i => ?_
  fin_cases i
  · rw [Category.assoc, cechPt_proj]; exact c0
  · rw [Category.assoc, cechPt_proj]; exact c1

/-- The move operation of `E`, as a `CategoryTheory.FamilyTransport` on the one-member family
`E₀ ⟶ Y ⟶ X'`. -/
def cechTransport :
    FamilyTransport (fun _ : PUnit.{1} => (Over.map p.hom).obj E.obj₀)
      (fun _ => Over.mk p.hom) (fun _ => Descent.structureMap p.hom E.obj₀) where
  move v y := E.cechMove v y
  comp_move k v y := by
    refine Over.OverMorphism.ext ?_
    change k.left ≫ E.moveLift v y ≫ _ = E.moveLift (k ≫ v) (k ≫ y) ≫ _
    rw [← Category.assoc, E.comp_moveLift]
  move_base v y := by
    refine Over.OverMorphism.ext ?_
    change (E.moveLift v y ≫ _) ≫ E.toY = y.left
    rw [Category.assoc, E.moveLift_toY]
  move_self v := by
    refine Over.OverMorphism.ext ?_
    change E.moveLift v _ ≫ _ = v.left
    have hσ : E.moveLift v (v ≫ Descent.structureMap p.hom E.obj₀) =
        v.left ≫ E.tr (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) := by
      refine (E.moveLift_eq_of_move _ _ _ ?_ ?_).symm
      · rw [Category.assoc, E.tr_comp, E.tr_zero]; exact Category.comp_id _
      · rw [← Category.assoc, Category.assoc v.left, E.tr_comp, E.tr_zero]
        exact congrArg (· ≫ E.toY) (Category.comp_id v.left)
    rw [hσ, Category.assoc, E.tr_comp, E.tr_zero]; exact Category.comp_id _
  move_comp := fun {_ _ _ Z} v y z => by
    refine Over.OverMorphism.ext ?_
    let a := v.left ≫ E.toY
    let d₂ := cechPt p (n := 2) Z.hom ![a, y.left, z.left] (fun i => by
      fin_cases i
      · exact E.toY_comp v
      · exact Over.w y
      · exact Over.w z)
    let e₂ := E.liftPt v.left d₂ (by simp [d₂, a])
    have hproj (j : Fin 3) : e₂ ≫ E.tr (SimplexCategory.const ⦋0⦌ ⦋2⦌ j) ≫ E.toY =
        ![a, y.left, z.left] j := by
      rw [E.tr_toY, liftPt_proj_assoc, cechPt_proj]
    have h0 : e₂ ≫ E.tr (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0) = v.left := E.liftPt_tr _ _ _
    have hy : E.moveLift v y = e₂ ≫ E.tr (SimplexCategory.δ 2) := by
      refine (E.moveLift_eq_of_move _ _ _ ?_ ?_).symm
      · rw [Category.assoc, E.tr_comp]; exact h0
      · rw [← Category.assoc, Category.assoc e₂, E.tr_comp]; exact hproj 1
    have hz : E.moveLift v z = e₂ ≫ E.tr (SimplexCategory.δ 1) := by
      refine (E.moveLift_eq_of_move _ _ _ ?_ ?_).symm
      · rw [Category.assoc, E.tr_comp]; exact h0
      · rw [← Category.assoc, Category.assoc e₂, E.tr_comp]; exact hproj 2
    have hyz : E.moveLift (E.cechMove v y) z = e₂ ≫ E.tr (SimplexCategory.δ 0) := by
      refine (E.moveLift_eq_of_move _ _ _ ?_ ?_).symm
      · rw [Category.assoc, E.tr_comp, cechMove_left, hy, Category.assoc, E.tr_comp]
        rfl
      · rw [← Category.assoc, Category.assoc e₂, E.tr_comp]; exact hproj 2
    change E.moveLift (E.cechMove v y) z ≫ _ = E.moveLift v z ≫ _
    rw [hyz, hz, Category.assoc, Category.assoc, E.tr_comp, E.tr_comp]
    rfl

/-- The move operation of `AlgebraicGeometry.Space.CompatibleEtaleDiagram.cechTransport`. -/
@[simp]
theorem cechTransport_move {Z : Over X.obj} (v : Z ⟶ (Over.map p.hom).obj E.obj₀)
    (y : Z ⟶ Over.mk p.hom) :
    E.cechTransport.move (i := PUnit.unit) (j := PUnit.unit) v y = E.cechMove v y := rfl

/-- **The descent datum of a compatible étale diagram over the Čech nerve of `p`**, relative to
`p`: its component is `E₀ ⟶ Y`, and its gluing isomorphisms are those of the move operation
`AlgebraicGeometry.Space.CompatibleEtaleDiagram.cechTransport`. -/
def cechDescentData : Descent.HomDescentData.{u, 0} p.hom X.property Y.property where
  obj _ := E.obj₀
  obj_isAlgebraicSpace _ := (E.U.obj (op ⦋0⦌)).property
  gluing i j := E.cechTransport.gluing i j
  cocycle i j k := E.cechTransport.gluing_cocycle i j k

/-- The move operation of the descent datum of `E` is
`AlgebraicGeometry.Space.CompatibleEtaleDiagram.cechMove`. -/
theorem cechDescentData_transport_move {Z : Over X.obj}
    (v : Z ⟶ (Over.map p.hom).obj E.obj₀) (y : Z ⟶ Over.mk p.hom) :
    E.cechDescentData.transport.move (i := PUnit.unit) (j := PUnit.unit) v y =
      E.cechMove v y := by
  show prod.lift v y ≫ (E.cechTransport.gluing PUnit.unit PUnit.unit).hom.left ≫ prod.snd = _
  rw [FamilyTransport.gluing_hom, prod.lift_snd, E.cechTransport.comp_move, prod.lift_fst,
    prod.lift_snd]
  rfl

/-- The component of the descent datum is étale over `Y`. -/
theorem isEtale_cechDescentData_obj :
    IsEtale B S hS (E.cechDescentData.obj PUnit.unit).hom :=
  isEtale_comp B S hS (E.etale (op ⦋0⦌)) (isEtale_of_isIso B S hS _)

/-! ### Morphisms of compatible étale diagrams -/

variable {E} {F : CompatibleEtaleDiagram B S hS (cechDiagram p ν)}

/-- A morphism of compatible étale diagrams over the Čech nerve commutes with the projections. -/
theorem app_proj {α : E.U ⟶ F.U} (hα : α ≫ F.projection = E.projection) (n : ℕ) :
    (α.app (op ⦋n⦌)).hom ≫ F.proj n = E.proj n :=
  congrArg (fun k => k.hom) (congrArg (fun t => t.app (op ⦋n⦌)) hα)

/-- A morphism of compatible étale diagrams commutes with the transitions. -/
theorem app_tr (α : E.U ⟶ F.U) {n m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    E.tr θ ≫ (α.app (op ⦋m⦌)).hom = (α.app (op ⦋n⦌)).hom ≫ F.tr θ :=
  congrArg (fun k => k.hom) (α.naturality θ.op)

/-- A morphism of compatible étale diagrams over the Čech nerve commutes with the maps to `Y`. -/
theorem app_toY {α : E.U ⟶ F.U} (hα : α ≫ F.projection = E.projection) :
    (α.app (op ⦋0⦌)).hom ≫ F.toY = E.toY := by
  rw [← Category.assoc, app_proj hα]

/-- The component of the morphism of descent data induced by a morphism of compatible étale
diagrams. -/
abbrev cechDescentMapObj {α : E.U ⟶ F.U} (hα : α ≫ F.projection = E.projection) :
    E.obj₀ ⟶ F.obj₀ :=
  Over.homMk (α.app (op ⦋0⦌)).hom (app_toY hα)

/-- A morphism of compatible étale diagrams carries
`AlgebraicGeometry.Space.CompatibleEtaleDiagram.moveLift` to `moveLift`. -/
theorem moveLift_app {α : E.U ⟶ F.U} (hα : α ≫ F.projection = E.projection) {Z : Over X.obj}
    (v : Z ⟶ (Over.map p.hom).obj E.obj₀) (y : Z ⟶ Over.mk p.hom) :
    E.moveLift v y ≫ (α.app (op ⦋1⦌)).hom =
      F.moveLift (v ≫ (Over.map p.hom).map (cechDescentMapObj hα)) y := by
  refine F.moveLift_eq_of_move _ _ _ ?_ ?_
  · rw [Category.assoc, ← app_tr, ← Category.assoc, liftPt_tr]
    rfl
  · rw [Category.assoc, ← Category.assoc (α.app _).hom, ← app_tr, Category.assoc,
      app_toY hα]
    exact E.moveLift_toY v y

/-- **The morphism of descent data induced by a morphism of compatible étale diagrams** over
the Čech nerve. -/
def cechDescentMap {α : E.U ⟶ F.U} (hα : α ≫ F.projection = E.projection) :
    E.cechDescentData ⟶ F.cechDescentData :=
  Descent.DescentData.homOfMove (fun _ => cechDescentMapObj hα) (fun {i j Z} v y => by
    obtain ⟨⟩ := i; obtain ⟨⟩ := j
    refine (congrArg (· ≫ _) (E.cechDescentData_transport_move v y)).trans
      (Eq.trans ?_ (F.cechDescentData_transport_move _ y).symm)
    refine Over.OverMorphism.ext ?_
    change (E.moveLift v y ≫ E.tr _) ≫ (α.app (op ⦋0⦌)).hom = F.moveLift _ y ≫ F.tr _
    rw [Category.assoc, app_tr, ← Category.assoc]
    exact congrArg (· ≫ F.tr _) (moveLift_app hα v y))

/-- The component of `AlgebraicGeometry.Space.CompatibleEtaleDiagram.cechDescentMap`. -/
@[simp]
theorem cechDescentMap_hom {α : E.U ⟶ F.U} (hα : α ≫ F.projection = E.projection) :
    (cechDescentMap hα).hom PUnit.unit = cechDescentMapObj hα := rfl

/-! ### Realizations and the fibre descent datum -/

variable (r : EtaleRealization B S hS (cechCocone p ν) E)

/-- The total space of a realization, as an algebraic space over `X'`. -/
abbrev realSpace : Descent.AlgebraicSpacesOver (B := B) (S := S) (hS := hS) X.obj :=
  ⟨Over.mk r.toX.hom, r.U.property⟩

/-- The identification of the degree-`n` term of `E` with its image in the realization. -/
abbrev bc (n : ℕ) : E.term n ⟶ r.U.obj := (r.baseChange.app (op ⦋n⦌)).hom

/-- The identifications of the terms of `E` with their images in a realization commute with the
transitions. -/
theorem tr_bc {n m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) : E.tr θ ≫ bc r m = bc r n :=
  (congrArg (fun k => k.hom) (r.baseChange.naturality θ.op)).trans (Category.comp_id _)

/-- `E₀` is the fibre product of the realization and `Y` over `X'`. -/
theorem isPullback_bc_toY : IsPullback (bc r 0) E.toY r.toX.hom p.hom :=
  (AlgebraicSpaces.isPullback_hom B S hS (r.isPullback (op ⦋0⦌))).flip.of_iso (Iso.refl _)
    (Iso.refl _) (cechZeroIso p) (Iso.refl _) (by simp)
    (by simp only [Iso.refl_hom, Category.id_comp]; rfl) (by simp)
    (by
      show (cechBase p (op ⦋0⦌)).hom ≫ 𝟙 _ = (cechProj p (n := op ⦋0⦌) 0).hom ≫ p.hom
      rw [Category.comp_id]
      exact (hom_cechProj_comp p (n := op ⦋0⦌) 0).symm)

/-- The component of the fibre descent datum of a realization is the degree-zero term of `E`. -/
def realComponentIso :
    (fibreDatum p (realSpace r)).obj PUnit.unit ≅ E.obj₀ :=
  Over.isoMk (isPullback_bc_toY r).isoPullback.symm
    (IsPullback.isoPullback_inv_snd (isPullback_bc_toY r))

/-- `AlgebraicGeometry.Space.CompatibleEtaleDiagram.realComponentIso` followed by the map to the
realization is the first projection. -/
@[reassoc (attr := simp)]
theorem realComponentIso_hom_bc :
    (realComponentIso r).hom.left ≫ bc r 0 = pullback.fst _ _ :=
  IsPullback.isoPullback_inv_fst (isPullback_bc_toY r)

/-- `AlgebraicGeometry.Space.CompatibleEtaleDiagram.realComponentIso` carries the move operation
of the fibre descent datum to that of `E`. -/
theorem realComponentIso_move {Z : Over X.obj}
    (v : Z ⟶ (Over.map p.hom).obj ((fibreDatum p (realSpace r)).obj PUnit.unit))
    (y : Z ⟶ Over.mk p.hom) :
    Descent.fibreMove (fun _ : PUnit.{1} => p.hom) (realSpace r).obj (i := PUnit.unit)
        (j := PUnit.unit) v y ≫ (Over.map p.hom).map (realComponentIso r).hom =
      E.cechMove (v ≫ (Over.map p.hom).map (realComponentIso r).hom) y := by
  refine Over.OverMorphism.ext ((isPullback_bc_toY r).hom_ext ?_ ?_)
  · have hL : (Descent.fibreMove (fun _ : PUnit.{1} => p.hom) (realSpace r).obj
          (i := PUnit.unit) (j := PUnit.unit) v y).left ≫ (realComponentIso r).hom.left ≫
          bc r 0 = v.left ≫ pullback.fst _ _ :=
      (congrArg (_ ≫ ·) (realComponentIso_hom_bc r)).trans (Descent.fibreMove_left_fst _ _ v y)
    have hR : (E.moveLift (v ≫ (Over.map p.hom).map (realComponentIso r).hom) y ≫
        E.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)) ≫ bc r 0 = v.left ≫ pullback.fst _ _ := by
      rw [Category.assoc, tr_bc, ← tr_bc r (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0), ← Category.assoc,
        liftPt_tr]
      exact (Category.assoc _ _ _).trans (congrArg (v.left ≫ ·) (realComponentIso_hom_bc r))
    exact (Category.assoc _ _ _).trans (hL.trans hR.symm)
  · have hL : (Descent.fibreMove (fun _ : PUnit.{1} => p.hom) (realSpace r).obj
          (i := PUnit.unit) (j := PUnit.unit) v y).left ≫ (realComponentIso r).hom.left ≫
          E.toY = y.left :=
      (congrArg (_ ≫ ·) (Over.w (realComponentIso r).hom)).trans
        (Descent.fibreMove_left_snd _ _ v y)
    have hR : (E.moveLift (v ≫ (Over.map p.hom).map (realComponentIso r).hom) y ≫
        E.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)) ≫ E.toY = y.left :=
      (Category.assoc _ _ _).trans (E.moveLift_toY _ y)
    exact (Category.assoc _ _ _).trans (hL.trans hR.symm)

/-- **The fibre descent datum of a realization of `E` is the descent datum of `E`.** -/
def realIso : fibreDatum p (realSpace r) ≅ E.cechDescentData where
  hom := Descent.DescentData.homOfMove (fun _ => (realComponentIso r).hom)
    (fun {i j Z} v y => by
      obtain ⟨⟩ := i; obtain ⟨⟩ := j
      refine (congrArg (· ≫ _) (fibreDescentData_transport_move p _ v y)).trans
        (Eq.trans ?_ (E.cechDescentData_transport_move _ y).symm)
      exact realComponentIso_move r v y)
  inv := Descent.DescentData.homOfMove (fun _ => (realComponentIso r).inv)
    (fun {i j Z} v y => by
      obtain ⟨⟩ := i; obtain ⟨⟩ := j
      refine (congrArg (· ≫ _) (E.cechDescentData_transport_move v y)).trans
        (Eq.trans ?_ (fibreDescentData_transport_move p _ _ y).symm)
      let c := realComponentIso r
      let w := v ≫ (Over.map p.hom).map c.inv
      have h := realComponentIso_move r w y
      have hv : w ≫ (Over.map p.hom).map c.hom = v :=
        (Category.assoc _ _ _).trans ((congrArg (v ≫ ·)
          ((Over.map p.hom).mapIso c).inv_hom_id).trans (Category.comp_id v))
      have h2 := congrArg Over.Hom.left (h.trans (congrArg (fun t => E.cechMove t y) hv))
      refine Over.OverMorphism.ext ?_
      exact (congrArg (· ≫ c.inv.left) h2.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (congrArg Over.Hom.left c.hom_inv_id)).trans (Category.comp_id _))))
  hom_inv_id := Descent.DescentData.Hom.ext (funext fun _ => (realComponentIso r).hom_inv_id)
  inv_hom_id := Descent.DescentData.Hom.ext (funext fun _ => (realComponentIso r).inv_hom_id)

/-! ### Realizations from effective descent data -/

variable (E)

/-- The component isomorphism of an isomorphism of descent data. -/
def compIso {D D' : Descent.HomDescentData.{u, 0} p.hom X.property Y.property} (ψ : D ≅ D') :
    D.obj PUnit.unit ≅ D'.obj PUnit.unit where
  hom := ψ.hom.hom PUnit.unit
  inv := ψ.inv.hom PUnit.unit
  hom_inv_id := congrArg (fun m => m.hom PUnit.unit) ψ.hom_inv_id
  inv_hom_id := congrArg (fun m => m.hom PUnit.unit) ψ.inv_hom_id

variable {V : Descent.AlgebraicSpacesOver (B := B) (S := S) (hS := hS) X.obj}
  (ψ : fibreDatum p V ≅ E.cechDescentData)

/-- The identification of `V ×_{X'} Y` with `E₀`, as presheaves. -/
def ec : pullback V.obj.hom p.hom ≅ E.term 0 where
  hom := (compIso ψ).hom.left
  inv := (compIso ψ).inv.left
  hom_inv_id := congrArg Over.Hom.left (compIso ψ).hom_inv_id
  inv_hom_id := congrArg Over.Hom.left (compIso ψ).inv_hom_id

/-- `AlgebraicGeometry.Space.CompatibleEtaleDiagram.ec` lies over `Y`. -/
theorem ec_hom_toY : (E.ec ψ).hom ≫ E.toY = pullback.snd V.obj.hom p.hom :=
  Over.w (compIso ψ).hom

/-- The inverse of `AlgebraicGeometry.Space.CompatibleEtaleDiagram.ec` lies over `Y`. -/
theorem ec_inv_snd : (E.ec ψ).inv ≫ pullback.snd V.obj.hom p.hom = E.toY :=
  Over.w (compIso ψ).inv

/-- The identification of `E₀` with `V ×_{X'} Y`, followed by the projection to `V`. -/
abbrev bc₀ : E.term 0 ⟶ V.obj.left :=
  (E.ec ψ).inv ≫ pullback.fst V.obj.hom p.hom

/-- The image in `V` of the two vertices of a point of `E₁` agree. -/
theorem tr_one_bc₀ :
    E.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) ≫ E.bc₀ ψ =
      E.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) ≫ E.bc₀ ψ := by
  let Z : Over X.obj := Over.mk (E.proj 1 ≫ (cechBase p (op ⦋1⦌)).hom)
  let v : Z ⟶ (Over.map p.hom).obj E.obj₀ :=
    Over.homMk (E.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0)) (by
      show E.tr _ ≫ E.toY ≫ p.hom = E.proj 1 ≫ _
      rw [← Category.assoc, E.tr_toY, Category.assoc, hom_cechProj_comp])
  let y : Z ⟶ Over.mk p.hom :=
    Over.homMk (E.proj 1 ≫ (cechProj p (n := op ⦋1⦌) 1).hom) (by
      show (E.proj 1 ≫ _) ≫ p.hom = E.proj 1 ≫ _
      rw [Category.assoc, hom_cechProj_comp])
  have hlift : E.moveLift v y = 𝟙 _ :=
    (E.moveLift_eq_of_move v y (𝟙 _) (Category.id_comp _)
      ((Category.id_comp _).trans (E.tr_toY 1))).symm
  have hmove := Descent.DescentData.move_naturality ψ.inv (i := PUnit.unit) (j := PUnit.unit) v y
  have h1 := (congrArg (· ≫ _) (E.cechDescentData_transport_move v y).symm).trans
    (hmove.trans (fibreDescentData_transport_move p _ _ y))
  have h2 := congrArg (fun m => m.left ≫ pullback.fst V.obj.hom p.hom) h1
  have hL : E.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) ≫ E.bc₀ ψ =
      ((E.cechMove v y) ≫ (Over.map p.hom).map (ψ.inv.hom PUnit.unit)).left ≫
        pullback.fst V.obj.hom p.hom := by
    show E.tr _ ≫ (E.ec ψ).inv ≫ _ =
      ((E.moveLift v y ≫ E.tr _) ≫ (ψ.inv.hom PUnit.unit).left) ≫ _
    rw [hlift, Category.id_comp]
    exact (Category.assoc _ _ _).symm
  have hR : (Descent.fibreMove (fun _ : PUnit.{1} => p.hom) (sheafOf p V).obj (i := PUnit.unit)
      (j := PUnit.unit) (v ≫ (Over.map p.hom).map (ψ.inv.hom PUnit.unit)) y).left ≫
        pullback.fst V.obj.hom p.hom = E.tr (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) ≫ E.bc₀ ψ :=
    (Descent.fibreMove_left_fst _ _ _ y).trans (Category.assoc _ _ _)
  exact hL.trans (h2.trans hR)

/-- The images in `V` of all the vertices of a point of `Eₙ` agree. -/
theorem tr_bc₀ {n : ℕ} (j : Fin (n + 1)) :
    E.tr (SimplexCategory.const ⦋0⦌ ⦋n⦌ j) ≫ E.bc₀ ψ =
      E.tr (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) ≫ E.bc₀ ψ := by
  let ε := SimplexCategory.mkOfLe (0 : Fin (n + 1)) j (Fin.zero_le _)
  have h1 : SimplexCategory.const ⦋0⦌ ⦋n⦌ j = SimplexCategory.const ⦋0⦌ ⦋1⦌ 1 ≫ ε := rfl
  have h0 : SimplexCategory.const ⦋0⦌ ⦋n⦌ 0 = SimplexCategory.const ⦋0⦌ ⦋1⦌ 0 ≫ ε := rfl
  rw [E.tr_congr h1, E.tr_congr h0, ← E.tr_comp, ← E.tr_comp, Category.assoc, Category.assoc,
    E.tr_one_bc₀]

/-- The identification of the degree-`n` term of `E` with its image in `V`. -/
abbrev bcN (n : SimplexCategoryᵒᵖ) : E.U.obj n ⟶ ⟨V.obj.left, V.property⟩ :=
  ObjectProperty.homMk (E.tr (n := n.unop.len) (SimplexCategory.const ⦋0⦌ _ 0) ≫ E.bc₀ ψ)

/-- `E₀` is the fibre product of `V` and the degree-zero term of the Čech nerve over `X'`. -/
theorem isPullback_bc₀ :
    IsPullback (E.bc₀ ψ) (E.proj 0) V.obj.hom (cechBase p (op ⦋0⦌)).hom := by
  refine (IsPullback.of_hasPullback V.obj.hom p.hom).of_iso (E.ec ψ) (Iso.refl _)
    (cechZeroIso p).symm (Iso.refl _) ?_ ?_ (by simp) ?_
  · show _ ≫ 𝟙 _ = (E.ec ψ).hom ≫ (E.ec ψ).inv ≫ _
    rw [Category.comp_id, Iso.hom_inv_id_assoc]
  · show pullback.snd _ _ ≫ (cechZeroSection p).hom = (E.ec ψ).hom ≫ E.proj 0
    rw [← E.ec_hom_toY ψ, Category.assoc, Category.assoc]
    refine congrArg ((E.ec ψ).hom ≫ ·) ?_
    exact (congrArg (E.proj 0 ≫ ·) (cechZeroIso p).hom_inv_id).trans (Category.comp_id _)
  · show p.hom ≫ 𝟙 _ = (cechZeroSection p).hom ≫ (cechBase p (op ⦋0⦌)).hom
    rw [Category.comp_id]
    exact (congrArg (fun k => k.hom) (cechZeroSection_cechBase p)).symm

/-- **The realization of `E` attached to an algebraic space `V` étale over `X'` whose fibre
descent datum is the descent datum of `E`.** -/
def realizationOfIso (hV : IsEtale B S hS V.obj.hom) :
    EtaleRealization B S hS (cechCocone p ν) E where
  U := ⟨V.obj.left, V.property⟩
  toX := ObjectProperty.homMk V.obj.hom
  etale := hV
  baseChange :=
    { app := fun n => E.bcN ψ n
      naturality := fun n m f => ObjectProperty.hom_ext _ (by
        change E.tr (n := n.unop.len) (m := m.unop.len) f.unop ≫ E.tr _ ≫ E.bc₀ ψ =
          (E.tr _ ≫ E.bc₀ ψ) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, E.tr_comp, E.tr_congr
          (SimplexCategory.const_comp _ _ _), E.tr_bc₀]) }
  overX n := ObjectProperty.hom_ext _ (by
    change E.proj n.unop.len ≫ (cechBase p (op ⦋n.unop.len⦌)).hom =
      (E.tr _ ≫ (E.ec ψ).inv ≫ pullback.fst V.obj.hom p.hom) ≫ V.obj.hom
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc _ (pullback.snd _ _),
      E.ec_inv_snd, ← Category.assoc, E.tr_toY, Category.assoc]
    exact congrArg (E.proj _ ≫ ·)
      (congrArg (fun k => k.hom) (cechProj_comp p (n := op ⦋n.unop.len⦌) 0)).symm)
  isPullback n := IsPullback.of_map_of_faithful (ObjectProperty.ι _) (by
    have sq := (E.isPullback_tr (SimplexCategory.const ⦋0⦌ ⦋n.unop.len⦌ 0)).paste_horiz
      (E.isPullback_bc₀ ψ)
    have hb : ((cechNerveSpace p).map (SimplexCategory.const ⦋0⦌ ⦋n.unop.len⦌ 0).op).hom ≫
        (cechBase p (op ⦋0⦌)).hom = (cechBase p (op ⦋n.unop.len⦌)).hom :=
      congrArg (fun k => k.hom)
        (cechNerveSpace_map_cechBase p (SimplexCategory.const ⦋0⦌ ⦋n.unop.len⦌ 0).op)
    rw [hb] at sq
    exact sq.flip)

/-! ### Full faithfulness -/

variable {E}

/-- The inverse of `AlgebraicGeometry.Space.CompatibleEtaleDiagram.realComponentIso` followed
by the first projection is the map to the realization. -/
theorem realComponentIso_inv_fst :
    (realComponentIso r).inv.left ≫ pullback.fst _ _ = bc r 0 := by
  rw [← realComponentIso_hom_bc r]
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ bc r 0)
    (congrArg Over.Hom.left (realComponentIso r).inv_hom_id))).trans (Category.id_comp _)

variable (s : EtaleRealization B S hS (cechCocone p ν) F) {α : E.U ⟶ F.U}
  (hα : α ≫ F.projection = E.projection)

/-- The morphism of fibre descent data between two realizations induced by a morphism of
compatible étale diagrams. -/
abbrev realMap : fibreDatum p (realSpace r) ⟶ fibreDatum p (realSpace s) :=
  (realIso r).hom ≫ cechDescentMap hα ≫ (realIso s).inv

/-- The morphism of fibre descent data induced by a morphism `φ` of realizations is
`AlgebraicGeometry.Space.CompatibleEtaleDiagram.realMap` exactly when `φ` is compatible with `α`
in degree zero. -/
theorem map_eq_realMap_iff (φ : realSpace r ⟶ realSpace s) :
    (Descent.fibreDescentFunctor (fun _ : PUnit.{1} => p.hom) X.property
        (fun _ => Y.property)).map ((Descent.algebraicSpacesOverToSheaves
          (fun _ : PUnit.{1} => p.hom) X.property (fun _ => Y.property)).map φ) =
        realMap r s hα ↔
      bc r 0 ≫ φ.hom.left = (α.app (op ⦋0⦌)).hom ≫ bc s 0 := by
  have hΦ : ((realMap r s hα).hom PUnit.unit).left ≫
      pullback.fst (realSpace s).obj.hom p.hom =
      (realComponentIso r).hom.left ≫ (α.app (op ⦋0⦌)).hom ≫ bc s 0 :=
    (Category.assoc _ _ _).trans (congrArg ((realComponentIso r).hom.left ≫ ·)
      ((Category.assoc _ _ _).trans (congrArg ((α.app (op ⦋0⦌)).hom ≫ ·)
        (realComponentIso_inv_fst s))))
  have hL := Descent.fibreComponentMap_left_fst (fun _ : PUnit.{1} => p.hom) φ.hom PUnit.unit
  have hc : ∀ t : E.term 0 ⟶ s.U.obj, (realComponentIso r).inv.left ≫
      ((realComponentIso r).hom.left ≫ t) = t := fun t =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ t)
      (congrArg Over.Hom.left (realComponentIso r).inv_hom_id)).trans (Category.id_comp _))
  constructor
  · intro h
    have h1 := congrArg (fun m => (m.hom PUnit.unit).left ≫
      pullback.fst (realSpace s).obj.hom p.hom) h
    have h2 : pullback.fst (realSpace r).obj.hom p.hom ≫ φ.hom.left =
        (realComponentIso r).hom.left ≫ (α.app (op ⦋0⦌)).hom ≫ bc s 0 :=
      hL.symm.trans (h1.trans hΦ)
    refine (congrArg (· ≫ φ.hom.left) (realComponentIso_inv_fst r).symm).trans ?_
    exact (Category.assoc _ _ _).trans ((congrArg ((realComponentIso r).inv.left ≫ ·) h2).trans
      (hc _))
  · intro h
    refine Descent.DescentData.Hom.ext (funext fun _ => Over.OverMorphism.ext ?_)
    refine pullback.hom_ext ?_ ?_
    · refine hL.trans (Eq.trans ?_ hΦ.symm)
      refine (congrArg (· ≫ φ.hom.left) (realComponentIso_hom_bc r).symm).trans ?_
      exact (Category.assoc _ _ _).trans (congrArg ((realComponentIso r).hom.left ≫ ·) h)
    · exact (Descent.fibreComponentMap_left_snd (fun _ : PUnit.{1} => p.hom) φ.hom
        PUnit.unit).trans (Over.w ((realMap r s hα).hom PUnit.unit)).symm

/-- A morphism of realizations compatible with `α` in degree zero is compatible with `α` in
every degree. -/
theorem bc_comp_eq {f : r.U ⟶ s.U}
    (h₀ : bc r 0 ≫ f.hom = (α.app (op ⦋0⦌)).hom ≫ bc s 0) (n : SimplexCategoryᵒᵖ) :
    r.baseChange.app n ≫ f = α.app n ≫ s.baseChange.app n := by
  refine ObjectProperty.hom_ext _ ?_
  show bc r n.unop.len ≫ f.hom = (α.app (op ⦋n.unop.len⦌)).hom ≫ bc s n.unop.len
  rw [← tr_bc r (SimplexCategory.const ⦋0⦌ ⦋n.unop.len⦌ 0),
    ← tr_bc s (SimplexCategory.const ⦋0⦌ ⦋n.unop.len⦌ 0), Category.assoc, h₀,
    ← Category.assoc, ← Category.assoc, app_tr]

end CompatibleEtaleDiagram

variable (B S hS) in
/-- **Étale descent of algebraic spaces along proper surjective morphisms**, in the
space-level form used by condition (1) of Stacks 0GHL in the proof of Stacks 0AGG: for a
proper surjective morphism `f : Y ⟶ X` of algebraic spaces over `S`,

* every descent datum relative to `f` whose underlying space is étale over `Y` is isomorphic to
  the fibre descent datum `Y ×_X V` of an algebraic space `V` étale over `X` (this is the
  conclusion of Stacks 0GG0; the fibre descent datum is the canonical descent datum of `V`,
  `AlgebraicGeometry.Space.Descent.canonicalDescentFunctor`, up to a canonical isomorphism);
* morphisms between algebraic spaces étale over `X` are the morphisms of their fibre descent
  data (full faithfulness, which the source draws from the equivalence of Stacks 0GFW).

It follows from the proper case of Stacks 0GFW and the translation step of Stacks 0GG0 by
`AlgebraicGeometry.Space.etaleSpaceDescentAlongProperSurjective_of_sheafDescent`, in
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairSheafDescent`: the first half is
Stacks 0GG0 read through `AlgebraicGeometry.Space.canonicalIsoFibreDatum`, the second is
`AlgebraicGeometry.Space.etaleSpaceHomDescentAlongProperSurjective_of_descentEffective`. -/
def EtaleSpaceDescentAlongProperSurjective : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X), IsSurjective B S hS f.hom →
    IsProper B S hS f.hom →
    (∀ D : Descent.HomDescentData.{u, 0} f.hom X.property Y.property,
        IsEtale B S hS (D.obj PUnit.unit).hom →
        ∃ V : Descent.AlgebraicSpacesOver (B := B) (S := S) (hS := hS) X.obj,
          IsEtale B S hS V.obj.hom ∧ Nonempty (fibreDatum f V ≅ D)) ∧
      ∀ V W : Descent.AlgebraicSpacesOver (B := B) (S := S) (hS := hS) X.obj,
        IsEtale B S hS V.obj.hom → IsEtale B S hS W.obj.hom →
          Function.Bijective (fun φ : V ⟶ W =>
            (Descent.fibreDescentFunctor (fun _ : PUnit.{1} => f.hom) X.property
              (fun _ => Y.property)).map ((Descent.algebraicSpacesOverToSheaves
                (fun _ : PUnit.{1} => f.hom) X.property (fun _ => Y.property)).map φ))

/-- **Condition (1) of Stacks 0GHL for the Čech nerve of a proper surjective morphism**: base
change along the Čech cocone of `p` is an equivalence from the small étale site of `X'` onto the
limit of the small étale sites of the terms of the Čech nerve, granted étale descent of algebraic
spaces along proper surjective morphisms. -/
theorem etaleComparisonIsEquivalence_cechCocone {B₀ : AlgebraicSpaces B S hS} (ν : X ⟶ B₀)
    (h : EtaleSpaceDescentAlongProperSurjective B S hS) (hsurj : IsSurjective B S hS p.hom)
    (hprop : IsProper B S hS p.hom) :
    EtaleComparisonIsEquivalence B S hS (cechCocone p ν) where
  essentiallySurjective E := by
    obtain ⟨V, hV, ⟨ψ⟩⟩ := (h p hsurj hprop).1 E.cechDescentData E.isEtale_cechDescentData_obj
    exact ⟨E.realizationOfIso ψ hV⟩
  fullyFaithful E F r s α hα := by
    have hbij := (h p hsurj hprop).2 (CompatibleEtaleDiagram.realSpace r)
      (CompatibleEtaleDiagram.realSpace s) r.etale s.etale
    obtain ⟨φ, hφ⟩ := hbij.2 (CompatibleEtaleDiagram.realMap r s hα)
    have h₀ := (CompatibleEtaleDiagram.map_eq_realMap_iff r s hα φ).1 hφ
    refine ⟨ObjectProperty.homMk φ.hom.left, ⟨ObjectProperty.hom_ext _ (Over.w φ.hom),
      CompatibleEtaleDiagram.bc_comp_eq r s h₀⟩, ?_⟩
    rintro f' ⟨hf'1, hf'2⟩
    let φ' : CompatibleEtaleDiagram.realSpace r ⟶ CompatibleEtaleDiagram.realSpace s :=
      ObjectProperty.homMk (Over.homMk f'.hom (congrArg (fun k => k.hom) hf'1))
    have h' : φ' = φ := hbij.1 (((CompatibleEtaleDiagram.map_eq_realMap_iff r s hα φ').2
      (congrArg (fun k => k.hom) (hf'2 (op ⦋0⦌)))).trans hφ.symm)
    exact ObjectProperty.hom_ext _ (congrArg (fun k => k.hom.left) h')

end AlgebraicGeometry.Space

end
