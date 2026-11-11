module

public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# The inhomogeneous cochain complex of `ℤ/2` with trivial coefficients killed by `2`

Let `𝒜` be a preadditive category with finite products and `M` an object of `𝒜`. Let
`G = Multiplicative (ZMod 2)` be the group of order two, written multiplicatively, with generator
`σ`. The nerve `X = nerve (SingleObj G)` of the one-object groupoid of `G` is the bar construction
of `G`: an `n`-simplex is a string `(g₁, …, gₙ)` of elements of `G`, the face `d₀` drops `g₁`, the
face `dₙ` drops `gₙ`, the inner face `dᵢ` replaces `(gᵢ, gᵢ₊₁)` by their product, and the
degeneracies insert `1`. Applying `M ^ (-)` to `X` gives a cosimplicial object
`[n] ↦ ∏_{X_n} M` whose alternating coface complex is the inhomogeneous cochain complex of `G` with
trivial coefficients `M` (degree `n`: maps `Gⁿ → M`).

If `2 • 𝟙 M = 0`, this cochain complex is homotopy equivalent to the complex with `M` in every
degree `≥ 0` and zero differential. Indeed, the normalized cochains — those vanishing on
degenerate simplices — form a homotopy equivalent direct summand (the dual Dold–Kan projection,
obtained from Mathlib's `PInfty` in `𝒜ᵒᵖ`), and in each degree `n` there is exactly one
nondegenerate simplex, `(σ, …, σ)`: a string containing `1` is degenerate. The normalized complex
is therefore `M` in each degree with differential `(1 + (-1)ⁿ⁺¹) • 𝟙 M`, since the inner faces of
`(σ, …, σ)` contain `σ² = 1` and are degenerate. This differential vanishes when `2 • 𝟙 M = 0`.

## Main definitions

* `Stacks.GroupCohomology.TrivialBar.powCosimplicial X M`: the cosimplicial object
  `[n] ↦ ∏_{X_n} M` of a simplicial set `X` with finite sets of simplices.
* `Stacks.GroupCohomology.TrivialBar.nerveZModTwo`: the nerve of the one-object groupoid of
  `Multiplicative (ZMod 2)`.
* `Stacks.GroupCohomology.TrivialBar.cochainCosimplicial M`: `powCosimplicial nerveZModTwo M`.
* `Stacks.GroupCohomology.TrivialBar.barCochainComplex M`: its alternating coface complex.
* `Stacks.GroupCohomology.TrivialBar.zeroDiffComplex M`: `M` in each degree, zero differential.
* `Stacks.GroupCohomology.TrivialBar.cosimplicialPInfty V`: the dual Dold–Kan projection on the
  alternating coface complex of a cosimplicial object `V` of a preadditive category, homotopic to
  the identity (`homotopyCosimplicialPInftyId`).
* `Stacks.GroupCohomology.TrivialBar.homotopyEquivExtend`: a homotopy equivalence extends along an
  embedding of complex shapes.

## Main results

* `Stacks.GroupCohomology.TrivialBar.homotopyEquivZeroDiffComplex`: if `2 • 𝟙 M = 0`, a homotopy
  equivalence `zeroDiffComplex M ≃ barCochainComplex M`, natural in `M`
  (`homotopyEquivZeroDiffComplex_hom_naturality`, `homotopyEquivZeroDiffComplex_inv_naturality`).
* `Stacks.GroupCohomology.TrivialBar.homotopyEquivZeroDiffComplexInt`: the same for the
  `ℤ`-indexed complexes obtained by extension along `ComplexShape.embeddingUpNat`.

## Implementation notes

The group `ℤ/2` is taken multiplicatively, `Multiplicative (ZMod 2)`, so that it is a `Group` and
`SingleObj` applies. In `SingleObj G`, composition `f ≫ g` is the product `g * f`.

## References

* [Stacks, Tag 07DC](https://stacks.math.columbia.edu/tag/07DC)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite Simplicial AlgebraicTopology AlgebraicTopology.DoldKan

universe w v u

namespace Stacks.GroupCohomology.TrivialBar

variable {𝒜 : Type u} [Category.{v} 𝒜]

/-! ### The cosimplicial object `M ^ X` -/

section Pow

variable [HasFiniteProducts 𝒜] (X : SSet.{w}) [∀ Δ : SimplexCategoryᵒᵖ, Finite (X.obj Δ)]

/-- The cosimplicial object `[n] ↦ ∏_{X_n} M` obtained by applying `M ^ (-)` to a simplicial set
`X` with finite sets of simplices: the coface or codegeneracy along `θ : Δ ⟶ Δ'` has component at
`y : X_{Δ'}` the projection to the factor `X(θ) y`. -/
abbrev powCosimplicial (M : 𝒜) : CosimplicialObject 𝒜 where
  obj Δ := ∏ᶜ fun _ : X.obj (op Δ) => M
  map θ := Pi.lift fun y => Pi.π (fun _ => M) (X.map θ.op y)
  map_id Δ := by
    refine Pi.hom_ext _ _ fun y => ?_
    simp
  map_comp θ θ' := by
    refine Pi.hom_ext _ _ fun y => ?_
    simp

variable {X}

/-- The components of the structure maps of `powCosimplicial X M`. -/
@[reassoc (attr := simp)]
lemma powCosimplicial_map_π (M : 𝒜) {Δ Δ' : SimplexCategory} (θ : Δ ⟶ Δ')
    (y : X.obj (op Δ')) :
    (powCosimplicial X M).map θ ≫ Pi.π (fun _ : X.obj (op Δ') => M) y =
      Pi.π (fun _ : X.obj (op Δ) => M) (X.map θ.op y) :=
  Pi.lift_comp_π _ _

/-- The components of the cofaces of `powCosimplicial X M`. -/
@[reassoc (attr := simp)]
lemma powCosimplicial_δ_π (M : 𝒜) {n : ℕ} (i : Fin (n + 2)) (y : X _⦋n + 1⦌) :
    (powCosimplicial X M).δ i ≫ Pi.π (fun _ : X _⦋n + 1⦌ => M) y =
      Pi.π (fun _ : X _⦋n⦌ => M) (X.δ i y) :=
  Pi.lift_comp_π _ _

/-- The components of the codegeneracies of `powCosimplicial X M`. -/
@[reassoc (attr := simp)]
lemma powCosimplicial_σ_π (M : 𝒜) {n : ℕ} (i : Fin (n + 1)) (y : X _⦋n⦌) :
    (powCosimplicial X M).σ i ≫ Pi.π (fun _ : X _⦋n⦌ => M) y =
      Pi.π (fun _ : X _⦋n + 1⦌ => M) (X.σ i y) :=
  Pi.lift_comp_π _ _

variable (X) in
/-- The morphism `M ^ X ⟶ M' ^ X` of cosimplicial objects induced by `f : M ⟶ M'`. -/
def powCosimplicialMap {M M' : 𝒜} (f : M ⟶ M') : powCosimplicial X M ⟶ powCosimplicial X M' where
  app Δ := Limits.Pi.map fun _ => f
  naturality Δ Δ' θ := by
    refine Pi.hom_ext _ _ fun y => ?_
    simp

/-- The components of `powCosimplicialMap X f`. -/
@[reassoc (attr := simp)]
lemma powCosimplicialMap_app_π {M M' : 𝒜} (f : M ⟶ M') (Δ : SimplexCategory)
    (y : X.obj (op Δ)) :
    (powCosimplicialMap X f).app Δ ≫ Pi.π (fun _ : X.obj (op Δ) => M') y =
      Pi.π (fun _ : X.obj (op Δ) => M) y ≫ f :=
  Limits.Pi.map_π (fun _ => f) y

end Pow

/-! ### The dual Dold–Kan projection -/

/-- If `f` vanishes on the degeneracies of a simplicial object, then `PInfty ≫ f = f`. -/
private lemma PInfty_f_comp_of_degeneraciesVanish {C : Type*} [Category* C] [Preadditive C]
    {Y : SimplicialObject C} {n : ℕ} {T : C} (f : Y _⦋n⦌ ⟶ T) (hf : DegeneraciesVanish f) :
    (PInfty (X := Y)).f n ≫ f = f := by
  have h := (degeneraciesVanish_iff_QInfty_f_comp f).1 hf
  have e := PInfty_f_add_QInfty_f (X := Y) n =≫ f
  calc (PInfty (X := Y)).f n ≫ f = (PInfty (X := Y)).f n ≫ f + (QInfty (X := Y)).f n ≫ f :=
        (add_zero _).symm.trans (congrArg ((PInfty (X := Y)).f n ≫ f + ·) h.symm)
    _ = ((PInfty (X := Y)).f n + (QInfty (X := Y)).f n) ≫ f :=
        (Preadditive.add_comp _ _ _ _ _ _).symm
    _ = 𝟙 _ ≫ f := e
    _ = f := Category.id_comp f

section Projection

variable [Preadditive 𝒜] (V : CosimplicialObject 𝒜)

/-- The simplicial object of `𝒜ᵒᵖ` corresponding to a cosimplicial object `V` of `𝒜`. -/
abbrev opSimplicial : SimplicialObject 𝒜ᵒᵖ := (cosimplicialSimplicialEquiv 𝒜).functor.obj (op V)

/-- The component in degree `n` of the dual Dold–Kan projection of `V`: the projection `PInfty`
of `opSimplicial V`, read in `𝒜`. Its image consists of the cochains killed by every
codegeneracy. -/
def cosimplicialPInftyApp (n : ℕ) : V.obj ⦋n⦌ ⟶ V.obj ⦋n⦌ :=
  ((PInfty (X := opSimplicial V)).f n).unop

/-- The dual Dold–Kan projection kills the codegeneracies. -/
@[reassoc]
lemma cosimplicialPInftyApp_comp_σ {n : ℕ} (i : Fin (n + 1)) :
    cosimplicialPInftyApp V (n + 1) ≫ V.σ i = 0 :=
  Quiver.Hom.op_inj (σ_comp_PInfty (opSimplicial V) i)

/-- A morphism into `V_{n+1}` killed by every codegeneracy is fixed by the dual Dold–Kan
projection. -/
lemma comp_cosimplicialPInftyApp {W : 𝒜} {n : ℕ} (ψ : W ⟶ V.obj ⦋n + 1⦌)
    (hψ : ∀ i : Fin (n + 1), ψ ≫ V.σ i = 0) :
    ψ ≫ cosimplicialPInftyApp V (n + 1) = ψ :=
  Quiver.Hom.op_inj (PInfty_f_comp_of_degeneraciesVanish (Y := opSimplicial V) (n := n + 1) ψ.op
    ((degeneraciesVanish_succ_iff _).2 fun i => Quiver.Hom.unop_inj (hψ i)))

/-- The dual Dold–Kan projection is the identity in degree `0`. -/
lemma cosimplicialPInftyApp_zero : cosimplicialPInftyApp V 0 = 𝟙 _ :=
  congrArg Quiver.Hom.unop (PInfty_f_0 (X := opSimplicial V))

variable {V} in
/-- Naturality of the dual Dold–Kan projection. -/
@[reassoc]
lemma cosimplicialPInftyApp_naturality {V' : CosimplicialObject 𝒜} (φ : V ⟶ V') (n : ℕ) :
    cosimplicialPInftyApp V n ≫ φ.app ⦋n⦌ = φ.app ⦋n⦌ ≫ cosimplicialPInftyApp V' n :=
  Quiver.Hom.op_inj (PInfty_f_naturality n ((cosimplicialSimplicialEquiv 𝒜).functor.map φ.op))

/-- The dual Dold–Kan projection commutes with the alternating sum of the cofaces. -/
lemma cosimplicialPInftyApp_comm (n : ℕ) :
    cosimplicialPInftyApp V n ≫ AlternatingCofaceMapComplex.objD V n =
      AlternatingCofaceMapComplex.objD V n ≫ cosimplicialPInftyApp V (n + 1) := by
  have h := (PInfty (X := opSimplicial V)).comm (n + 1) n
  have hd : (AlternatingFaceMapComplex.obj (opSimplicial V)).d (n + 1) n =
      AlternatingFaceMapComplex.objD (opSimplicial V) n :=
    AlternatingFaceMapComplex.obj_d_eq _ _
  rw [hd] at h
  rw [AlternatingCofaceMapComplex.d_eq_unop_d]
  exact congrArg Quiver.Hom.unop h.symm

/-- The differential of the alternating coface complex out of degree `n`. -/
lemma alternatingCofaceMapComplex_obj_d (n : ℕ) :
    ((alternatingCofaceMapComplex 𝒜).obj V).d n (n + 1) =
      AlternatingCofaceMapComplex.objD V n := by
  simp [alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj]

/-- The dual Dold–Kan projection on the alternating coface complex of a cosimplicial object
`V`. -/
def cosimplicialPInfty :
    (alternatingCofaceMapComplex 𝒜).obj V ⟶ (alternatingCofaceMapComplex 𝒜).obj V :=
  CochainComplex.ofHom (fun n => cosimplicialPInftyApp V n) (fun n => by
    rw [alternatingCofaceMapComplex_obj_d]
    exact cosimplicialPInftyApp_comm V n)

/-- The components of the dual Dold–Kan projection. -/
@[simp]
lemma cosimplicialPInfty_f (n : ℕ) :
    (cosimplicialPInfty V).f n = cosimplicialPInftyApp V n := rfl

/-- The alternating coface complex of `V` is, termwise by the identity, the unopposite of the
alternating face complex of `opSimplicial V`. -/
def alternatingCofaceMapComplexIsoUnop :
    (alternatingCofaceMapComplex 𝒜).obj V ≅
      (HomologicalComplex.unopFunctor 𝒜 (ComplexShape.down ℕ)).obj
        (op ((alternatingFaceMapComplex 𝒜ᵒᵖ).obj (opSimplicial V))) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    rintro i _ rfl
    have h₁ := alternatingFaceMapComplex_obj_d (opSimplicial V) i
    have h₂ := alternatingCofaceMapComplex_obj_d V i
    have h₃ := AlternatingCofaceMapComplex.d_eq_unop_d V i
    exact (Category.id_comp _).trans (((congrArg Quiver.Hom.unop h₁).trans
      (h₃.symm.trans h₂.symm)).trans (Category.comp_id _).symm))

/-- The dual Dold–Kan projection is homotopic to the identity. -/
def homotopyCosimplicialPInftyId : Homotopy (cosimplicialPInfty V) (𝟙 _) :=
  (Homotopy.ofEq (by
    ext n
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm)).trans
  ((((Homotopy.unop (homotopyPInftyToId (opSimplicial V))).compRight
    (alternatingCofaceMapComplexIsoUnop V).inv).compLeft
      (alternatingCofaceMapComplexIsoUnop V).hom).trans
    (Homotopy.ofEq (by
      simp only [op_id, CategoryTheory.Functor.map_id]
      exact (congrArg ((alternatingCofaceMapComplexIsoUnop V).hom ≫ ·)
        (Category.id_comp _)).trans (alternatingCofaceMapComplexIsoUnop V).hom_inv_id)))

end Projection

/-! ### The bar simplicial set of `ℤ/2` -/

section Nerve

/-- The generator `σ` of `Multiplicative (ZMod 2)`. -/
def gen : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

/-- The generator `σ` is not `1`. -/
lemma gen_ne_one : gen ≠ 1 := by decide

/-- The generator `σ` has order two. -/
lemma gen_mul_gen : gen * gen = 1 := by decide

/-- Every element of `Multiplicative (ZMod 2)` is `1` or `σ`. -/
lemma eq_one_or_eq_gen (g : Multiplicative (ZMod 2)) : g = 1 ∨ g = gen :=
  (by decide : ∀ a : ZMod 2, Multiplicative.ofAdd a = 1 ∨ Multiplicative.ofAdd a = gen)
    (Multiplicative.toAdd g)

/-- The nerve of the one-object groupoid of `Multiplicative (ZMod 2)`: the bar construction
of `ℤ/2`. -/
abbrev nerveZModTwo : SSet.{0} := nerve (SingleObj (Multiplicative (ZMod 2)))

/-- An `n`-simplex of `nerveZModTwo`, seen as a functor `Fin (n + 1) ⥤ SingleObj _`. -/
abbrev toArrows {n : ℕ} (y : nerveZModTwo _⦋n⦌) :
    ComposableArrows (SingleObj (Multiplicative (ZMod 2))) n := y

/-- The arrow `a ⟶ b` of a simplex of the bar construction, an element of `ℤ/2`. -/
def mapArr {n : ℕ} (y : nerveZModTwo _⦋n⦌) {a b : Fin (n + 1)} (φ : a ⟶ b) :
    Multiplicative (ZMod 2) :=
  (toArrows y).map φ

/-- The arrow `a ⟶ b` of a simplex depends only on `a` and `b`. -/
lemma mapArr_congr {n : ℕ} (y : nerveZModTwo _⦋n⦌) {a b a' b' : Fin (n + 1)} (φ : a ⟶ b)
    (φ' : a' ⟶ b') (ha : a = a') (hb : b = b') : mapArr y φ = mapArr y φ' := by
  subst ha hb
  exact congrArg (mapArr y) (Subsingleton.elim _ _)

/-- The arrows of a simplex of the bar construction compose by multiplication. -/
lemma mapArr_comp {n : ℕ} (y : nerveZModTwo _⦋n⦌) {a b c : Fin (n + 1)} (φ : a ⟶ b)
    (ψ : b ⟶ c) : mapArr y (φ ≫ ψ) = mapArr y ψ * mapArr y φ :=
  ((toArrows y).map_comp φ ψ).trans
    (SingleObj.comp_as_mul (f := (toArrows y).map φ) (g := (toArrows y).map ψ))

/-- The string `(g₁, …, gₙ)` of a simplex of the bar construction: `gₖ₊₁` is the arrow from
vertex `k` to vertex `k + 1`. -/
def arr {n : ℕ} (y : nerveZModTwo _⦋n⦌) (k : Fin n) : Multiplicative (ZMod 2) :=
  mapArr y (homOfLE (show k.castSucc ≤ k.succ from Fin.castSucc_lt_succ.le))

/-- A simplex of the bar construction is determined by its string. -/
lemma ext_arr {n : ℕ} {y z : nerveZModTwo _⦋n⦌} (h : ∀ k, arr y k = arr z k) : y = z :=
  ComposableArrows.ext (F := toArrows y) (G := toArrows z) (fun _ => rfl) (fun i hi => by
    have e : ∀ w : nerveZModTwo _⦋n⦌, (toArrows w).map' i (i + 1) = arr w ⟨i, hi⟩ := fun w =>
      mapArr_congr w _ _ (Fin.ext (by simp)) (Fin.ext (by simp))
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact ((e y).trans (h ⟨i, hi⟩)).trans (e z).symm)

/-- An arrow of a simplex between consecutive vertices is an entry of its string. -/
lemma map_eq_arr {n : ℕ} (y : nerveZModTwo _⦋n⦌) {a b : Fin (n + 1)} (φ : a ⟶ b) (k : Fin n)
    (ha : (a : ℕ) = k) (hb : (b : ℕ) = k + 1) : mapArr y φ = arr y k := by
  rw [arr]
  exact mapArr_congr y _ _ (Fin.ext (by simpa using ha)) (Fin.ext (by simpa using hb))

/-- An arrow of a simplex from a vertex to itself is `1`. -/
lemma map_eq_one {n : ℕ} (y : nerveZModTwo _⦋n⦌) {a b : Fin (n + 1)} (φ : a ⟶ b)
    (h : a = b) : mapArr y φ = 1 := by
  subst h
  exact (congrArg (mapArr y) (Subsingleton.elim φ (𝟙 a))).trans
    (((toArrows y).map_id a).trans (SingleObj.id_as_one (x := (toArrows y).obj a)))

/-- An arrow of a simplex across two consecutive edges is the product of two entries of its
string. -/
lemma map_eq_arr_mul {n : ℕ} (y : nerveZModTwo _⦋n⦌) {a b : Fin (n + 1)} (φ : a ⟶ b)
    (k l : Fin n) (ha : (a : ℕ) = k) (hl : (l : ℕ) = k + 1) (hb : (b : ℕ) = k + 2) :
    mapArr y φ = arr y l * arr y k := by
  have h₁ : a ≤ l.castSucc := by rw [Fin.le_def, Fin.val_castSucc]; omega
  have h₂ : l.castSucc ≤ b := by rw [Fin.le_def, Fin.val_castSucc]; omega
  rw [show φ = homOfLE h₁ ≫ homOfLE h₂ from Subsingleton.elim _ _, mapArr_comp,
    map_eq_arr y (homOfLE h₁) k ha (by rw [Fin.val_castSucc]; omega),
    map_eq_arr y (homOfLE h₂) l (Fin.val_castSucc l) (by omega)]

/-- The value of `Fin.succAbove`. -/
lemma val_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    (p.succAbove i : ℕ) = if (i : ℕ) < p then (i : ℕ) else (i : ℕ) + 1 := by
  rcases lt_or_ge (i : ℕ) p with h | h
  · have h' : Fin.castSucc i < p := by rw [Fin.lt_def, Fin.val_castSucc]; exact h
    rw [Fin.succAbove_of_castSucc_lt p i h', ite_eq_left h, Fin.val_castSucc]
  · have h' : p ≤ Fin.castSucc i := by rw [Fin.le_def, Fin.val_castSucc]; exact h
    have h'' : ¬ (i : ℕ) < p := by omega
    rw [Fin.succAbove_of_le_castSucc p i h', ite_eq_right h'', Fin.val_succ]

/-- The value of `Fin.predAbove`. -/
lemma val_predAbove {n : ℕ} (p : Fin n) (i : Fin (n + 1)) :
    (p.predAbove i : ℕ) = if (p : ℕ) < i then (i : ℕ) - 1 else (i : ℕ) := by
  rcases lt_or_ge (p : ℕ) i with h | h
  · have h' : Fin.castSucc p < i := by rw [Fin.lt_def, Fin.val_castSucc]; exact h
    rw [Fin.predAbove_of_castSucc_lt p i h', ite_eq_left h, Fin.val_pred]
  · have h' : i ≤ Fin.castSucc p := by rw [Fin.le_def, Fin.val_castSucc]; exact h
    have h'' : ¬ (p : ℕ) < i := by omega
    rw [Fin.predAbove_of_le_castSucc p i h', ite_eq_right h'', Fin.coe_castPred]

/-- The difference of the values of `Fin.succAbove` at consecutive points. -/
lemma val_succAbove_succ_sub {n : ℕ} (i : Fin (n + 2)) (k : Fin n) :
    (i.succAbove k.succ : ℕ) - (i.succAbove k.castSucc : ℕ) =
      if (k : ℕ) + 1 = i then 2 else 1 := by
  rw [val_succAbove, val_succAbove, Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> omega

/-- The arrows of a face of a simplex. -/
lemma map_δ {n : ℕ} (y : nerveZModTwo _⦋n + 1⦌) (i : Fin (n + 2)) {a b : Fin (n + 1)}
    (φ : a ⟶ b) :
    mapArr (n := n) (nerveZModTwo.δ i y) φ =
      mapArr (n := n + 1) y (homOfLE (show i.succAbove a ≤ i.succAbove b from
        (Fin.strictMono_succAbove i).monotone (leOfHom φ))) :=
  rfl

/-- The arrows of a degeneracy of a simplex. -/
lemma map_σ {n : ℕ} (y : nerveZModTwo _⦋n⦌) (i : Fin (n + 1)) {a b : Fin (n + 2)}
    (φ : a ⟶ b) :
    mapArr (n := n + 1) (nerveZModTwo.σ i y) φ =
      mapArr (n := n) y (homOfLE (show i.predAbove a ≤ i.predAbove b from
        i.predAbove_right_monotone (leOfHom φ))) :=
  rfl

/-- The functor `Fin (n + 1) ⥤ SingleObj (Multiplicative (ZMod 2))` sending `i ≤ j` to
`σ ^ (j - i)`. -/
def genString (n : ℕ) : Fin (n + 1) ⥤ SingleObj (Multiplicative (ZMod 2)) where
  obj _ := SingleObj.star _
  map {i j} _ := gen ^ ((j : ℕ) - i)
  map_id i := by
    simp only [Nat.sub_self, pow_zero]
    rfl
  map_comp {i j k} f g := by
    change gen ^ ((k : ℕ) - i) = gen ^ ((k : ℕ) - j) * gen ^ ((j : ℕ) - i)
    rw [← pow_add]
    congr 1
    have h₁ := leOfHom f
    have h₂ := leOfHom g
    rw [Fin.le_def] at h₁ h₂
    omega

/-- The nondegenerate `n`-simplex `(σ, …, σ)` of the bar construction of `ℤ/2`. -/
def genSimplex (n : ℕ) : nerveZModTwo _⦋n⦌ := genString n

/-- The arrows of the simplex `(σ, …, σ)`. -/
lemma genSimplex_map {n : ℕ} {a b : Fin (n + 1)} (φ : a ⟶ b) :
    mapArr (n := n) (genSimplex n) φ = gen ^ ((b : ℕ) - a) := rfl

/-- The string of `(σ, …, σ)`. -/
lemma arr_genSimplex {n : ℕ} (k : Fin n) : arr (n := n) (genSimplex n) k = gen := by
  rw [arr, genSimplex_map, Fin.val_succ, Fin.val_castSucc, Nat.add_sub_cancel_left, pow_one]

/-- A simplex is `(σ, …, σ)` if and only if its string is constant equal to `σ`. -/
lemma eq_genSimplex_iff {n : ℕ} (y : nerveZModTwo _⦋n⦌) :
    y = genSimplex n ↔ ∀ k, arr (n := n) y k = gen := by
  refine ⟨fun h k => h ▸ arr_genSimplex k, fun h => ext_arr (n := n) fun k => ?_⟩
  rw [h, arr_genSimplex]

/-- There is a single `0`-simplex. -/
lemma eq_genSimplex_zero (y : nerveZModTwo _⦋0⦌) : y = genSimplex 0 :=
  (eq_genSimplex_iff y).2 fun k => k.elim0

/-- The face `d₀` of `(σ, …, σ)` is `(σ, …, σ)`. -/
lemma δ_zero_genSimplex (n : ℕ) : nerveZModTwo.δ 0 (genSimplex (n + 1)) = genSimplex n := by
  refine (eq_genSimplex_iff _).2 fun k => ?_
  have h : (k : ℕ) + 1 ≠ ((0 : Fin (n + 2)) : ℕ) := by
    rw [Fin.val_zero]
    omega
  rw [arr, map_δ, genSimplex_map, val_succAbove_succ_sub, ite_eq_right h, pow_one]

/-- The last face of `(σ, …, σ)` is `(σ, …, σ)`. -/
lemma δ_last_genSimplex (n : ℕ) :
    nerveZModTwo.δ (Fin.last (n + 1)) (genSimplex (n + 1)) = genSimplex n := by
  refine (eq_genSimplex_iff _).2 fun k => ?_
  have h : (k : ℕ) + 1 ≠ ((Fin.last (n + 1) : Fin (n + 2)) : ℕ) := by
    have := k.isLt
    rw [Fin.val_last]
    omega
  rw [arr, map_δ, genSimplex_map, val_succAbove_succ_sub, ite_eq_right h, pow_one]

/-- An inner face of `(σ, …, σ)` contains `σ² = 1`, so it is not `(σ, …, σ)`. -/
lemma δ_genSimplex_ne {n : ℕ} (i : Fin (n + 2)) (h₀ : i ≠ 0) (h₁ : i ≠ Fin.last (n + 1)) :
    nerveZModTwo.δ i (genSimplex (n + 1)) ≠ genSimplex n := by
  have hi0 : (i : ℕ) ≠ 0 := fun h => h₀ (Fin.ext (by simp [h]))
  have hi1 : (i : ℕ) ≠ n + 1 := fun h => h₁ (Fin.ext (by simp [h]))
  have hi2 := i.isLt
  intro h
  have hk : (i : ℕ) - 1 < n := by omega
  have := ((eq_genSimplex_iff _).1 h) ⟨i - 1, hk⟩
  have h₂ : ((⟨(i : ℕ) - 1, hk⟩ : Fin n) : ℕ) + 1 = i := by
    change (i : ℕ) - 1 + 1 = i
    omega
  rw [arr, map_δ, genSimplex_map, val_succAbove_succ_sub, ite_eq_left h₂, pow_two,
    gen_mul_gen] at this
  exact gen_ne_one this.symm

/-- A degenerate simplex is not `(σ, …, σ)`. -/
lemma σ_ne_genSimplex {n : ℕ} (i : Fin (n + 1)) (y : nerveZModTwo _⦋n⦌) :
    nerveZModTwo.σ i y ≠ genSimplex (n + 1) := by
  intro h
  have := ((eq_genSimplex_iff _).1 h) i
  rw [arr, map_σ, map_eq_one _ _
    ((Fin.predAbove_castSucc_self i).trans (Fin.predAbove_succ_self i).symm)] at this
  exact gen_ne_one this.symm

/-- If the `j`-th entry of the string of `y` is `1`, then `y` is the degeneracy `σⱼ` of its face
`δⱼ₊₁`. -/
lemma σ_δ_of_arr_eq_one {n : ℕ} (y : nerveZModTwo _⦋n + 1⦌) (j : Fin (n + 1))
    (hj : arr (n := n + 1) y j = 1) :
    nerveZModTwo.σ j (nerveZModTwo.δ j.succ y) = y := by
  refine ext_arr (n := n + 1) fun k => ?_
  have hc : ∀ x : Fin (n + 2), (j.succ.succAbove (j.predAbove x) : ℕ) =
      if (x : ℕ) = j + 1 then (j : ℕ) else (x : ℕ) := by
    intro x
    rw [val_succAbove, val_predAbove, Fin.val_succ]
    split_ifs <;> omega
  have hk₀ : ((j.succ.succAbove (j.predAbove k.castSucc)) : ℕ) =
      if (k : ℕ) = j + 1 then (j : ℕ) else (k : ℕ) := by
    simp only [hc, Fin.val_castSucc]
  have hk₁ : ((j.succ.succAbove (j.predAbove k.succ)) : ℕ) =
      if (k : ℕ) + 1 = j + 1 then (j : ℕ) else (k : ℕ) + 1 := by
    simp only [hc, Fin.val_succ]
  change mapArr (n := n + 1) (nerveZModTwo.σ j (nerveZModTwo.δ j.succ y))
    (homOfLE (show k.castSucc ≤ k.succ from Fin.castSucc_lt_succ.le)) = arr y k
  rw [map_σ, map_δ]
  rcases lt_trichotomy (k : ℕ) j with hk | hk | hk
  · refine map_eq_arr y _ k ?_ ?_
    · rw [hk₀]; split_ifs <;> omega
    · rw [hk₁]; split_ifs <;> omega
  · refine (map_eq_one y _ (Fin.ext ?_)).trans ?_
    · rw [hk₀, hk₁]; split_ifs <;> omega
    · rw [← hj]
      exact congrArg (arr y) (Fin.ext hk).symm
  · rcases Nat.lt_or_ge (j + 1) k with hk' | hk'
    · refine map_eq_arr y _ k ?_ ?_
      · rw [hk₀]; split_ifs <;> omega
      · rw [hk₁]; split_ifs <;> omega
    · rw [map_eq_arr_mul y _ j k ?_ ?_ ?_, hj, mul_one]
      · rw [hk₀]; split_ifs <;> omega
      · omega
      · rw [hk₁]; split_ifs <;> omega

/-- Every simplex of positive dimension other than `(σ, …, σ)` is degenerate. -/
lemma exists_σ_of_ne_genSimplex {n : ℕ} (y : nerveZModTwo _⦋n + 1⦌)
    (hy : y ≠ genSimplex (n + 1)) : ∃ (j : Fin (n + 1)) (y' : nerveZModTwo _⦋n⦌),
      nerveZModTwo.σ j y' = y := by
  have : ∃ j, arr (n := n + 1) y j ≠ gen := by
    by_contra h
    push Not at h
    exact hy ((eq_genSimplex_iff y).2 h)
  obtain ⟨j, hj⟩ := this
  exact ⟨j, _, σ_δ_of_arr_eq_one y j ((eq_one_or_eq_gen _).resolve_right hj)⟩

/-- The bar construction of `ℤ/2` has finitely many simplices in each degree. -/
instance finite_nerveZModTwo_obj (Δ : SimplexCategoryᵒᵖ) : Finite (nerveZModTwo.obj Δ) :=
  Finite.of_injective (fun y : nerveZModTwo.obj Δ => arr (n := Δ.unop.len) y)
    fun _ _ h => ext_arr (n := Δ.unop.len) fun k => congrFun h k

end Nerve

/-! ### The bar cochain complex of `ℤ/2` and the zero-differential complex -/

section Complexes

variable [Preadditive 𝒜] [HasFiniteProducts 𝒜]

/-- The cosimplicial object `[n] ↦ ∏_{(ℤ/2)ⁿ} M` of inhomogeneous cochains of `ℤ/2` with trivial
coefficients `M`. -/
abbrev cochainCosimplicial (M : 𝒜) : CosimplicialObject 𝒜 := powCosimplicial nerveZModTwo M

/-- The inhomogeneous cochain complex of `ℤ/2` with trivial coefficients `M`: the alternating
coface complex of `cochainCosimplicial M`. -/
abbrev barCochainComplex (M : 𝒜) : CochainComplex 𝒜 ℕ :=
  (alternatingCofaceMapComplex 𝒜).obj (cochainCosimplicial M)

/-- The cochain complex with `M` in each degree and zero differential. -/
def zeroDiffComplex (M : 𝒜) : CochainComplex 𝒜 ℕ where
  X _ := M
  d _ _ := 0

omit [HasFiniteProducts 𝒜] in
/-- The terms of `zeroDiffComplex M`. -/
@[simp]
lemma zeroDiffComplex_X (M : 𝒜) (n : ℕ) : (zeroDiffComplex M).X n = M := rfl

omit [HasFiniteProducts 𝒜] in
/-- The differentials of `zeroDiffComplex M` vanish. -/
@[simp]
lemma zeroDiffComplex_d (M : 𝒜) (i j : ℕ) : (zeroDiffComplex M).d i j = 0 := rfl

/-- The morphism of zero-differential complexes induced by `f : M ⟶ M'`. -/
def zeroDiffComplexMap {M M' : 𝒜} (f : M ⟶ M') : zeroDiffComplex M ⟶ zeroDiffComplex M' where
  f _ := f
  comm' _ _ _ := comp_zero.trans zero_comp.symm

omit [HasFiniteProducts 𝒜] in
/-- The components of `zeroDiffComplexMap f`. -/
@[simp]
lemma zeroDiffComplexMap_f {M M' : 𝒜} (f : M ⟶ M') (n : ℕ) :
    (zeroDiffComplexMap f).f n = f := rfl

/-- The projection of a cochain to its value at a simplex. -/
abbrev evalAt (M : 𝒜) {n : ℕ} (y : nerveZModTwo _⦋n⦌) : (cochainCosimplicial M).obj ⦋n⦌ ⟶ M :=
  Pi.π (fun _ : nerveZModTwo _⦋n⦌ => M) y

open Classical in
/-- The inclusion of `M` as the cochains supported on the simplex `(σ, …, σ)`. -/
def genIncl (M : 𝒜) (n : ℕ) : M ⟶ (cochainCosimplicial M).obj ⦋n⦌ :=
  Pi.lift fun y => if y = genSimplex n then 𝟙 M else 0

/-- The value of a cochain at the simplex `(σ, …, σ)`. -/
def genProj (M : 𝒜) (n : ℕ) : (cochainCosimplicial M).obj ⦋n⦌ ⟶ M :=
  evalAt M (genSimplex n)

/-- The cochain `genIncl M n` vanishes away from `(σ, …, σ)`. -/
@[reassoc]
lemma genIncl_π (M : 𝒜) {n : ℕ} (y : nerveZModTwo _⦋n⦌) (hy : y ≠ genSimplex n) :
    genIncl M n ≫ evalAt M y = 0 :=
  (Pi.lift_comp_π _ y).trans (ite_eq_right hy)

/-- The cochain `genIncl M n` is `𝟙 M` at `(σ, …, σ)`. -/
@[reassoc (attr := simp)]
lemma genIncl_genProj (M : 𝒜) (n : ℕ) : genIncl M n ≫ genProj M n = 𝟙 M :=
  (Pi.lift_comp_π _ _).trans (ite_eq_left rfl)

/-- The cochain `genIncl M (n + 1)` vanishes on degenerate simplices. -/
lemma genIncl_comp_σ (M : 𝒜) {n : ℕ} (i : Fin (n + 1)) :
    genIncl M (n + 1) ≫ (cochainCosimplicial M).σ i = 0 := by
  refine Pi.hom_ext _ _ fun y => ?_
  rw [Category.assoc, powCosimplicial_σ_π, genIncl_π _ _ (σ_ne_genSimplex i y), zero_comp]

/-- The cochain `genIncl M n` is normalized. -/
lemma genIncl_comp_cosimplicialPInftyApp (M : 𝒜) (n : ℕ) :
    genIncl M n ≫ cosimplicialPInftyApp (cochainCosimplicial M) n = genIncl M n := by
  rcases n with _ | n
  · rw [cosimplicialPInftyApp_zero, Category.comp_id]
  · exact comp_cosimplicialPInftyApp _ _ (genIncl_comp_σ M)

/-- Normalized cochains vanish away from `(σ, …, σ)`. -/
@[reassoc]
lemma cosimplicialPInftyApp_π_of_ne (M : 𝒜) {n : ℕ} (y : nerveZModTwo _⦋n⦌)
    (hy : y ≠ genSimplex n) :
    cosimplicialPInftyApp (cochainCosimplicial M) n ≫ evalAt M y = 0 := by
  rcases n with _ | n
  · exact absurd (eq_genSimplex_zero y) hy
  · obtain ⟨j, y', rfl⟩ := exists_σ_of_ne_genSimplex y hy
    rw [evalAt, ← powCosimplicial_σ_π, cosimplicialPInftyApp_comp_σ_assoc, zero_comp]

/-- A normalized cochain is determined by its value at `(σ, …, σ)`. -/
lemma cosimplicialPInftyApp_genProj_genIncl (M : 𝒜) (n : ℕ) :
    cosimplicialPInftyApp (cochainCosimplicial M) n ≫ genProj M n ≫ genIncl M n =
      cosimplicialPInftyApp (cochainCosimplicial M) n := by
  refine Pi.hom_ext _ _ fun y => ?_
  by_cases hy : y = genSimplex n
  · subst hy
    rw [Category.assoc, Category.assoc, show Pi.π (fun _ : nerveZModTwo _⦋n⦌ => M)
      (genSimplex n) = genProj M n from rfl, genIncl_genProj, Category.comp_id]
  · rw [Category.assoc, Category.assoc, show Pi.π (fun _ : nerveZModTwo _⦋n⦌ => M) y =
      evalAt M y from rfl, genIncl_π _ _ hy, comp_zero, comp_zero,
      cosimplicialPInftyApp_π_of_ne _ _ hy]

omit [HasFiniteProducts 𝒜] in
/-- If `2 • 𝟙 M = 0`, then `f + f = 0` for every morphism `f` into `M`. -/
lemma add_self_eq_zero {M W : 𝒜} (hM : (2 : ℤ) • 𝟙 M = 0) (f : W ⟶ M) : f + f = 0 := by
  have h : f ≫ ((2 : ℤ) • 𝟙 M) = 0 := by rw [hM, comp_zero]
  rwa [Preadditive.comp_zsmul, Category.comp_id, two_zsmul] at h

/-- If `2 • 𝟙 M = 0`, the differential of a normalized cochain vanishes at `(σ, …, σ)`: the two
outer faces of `(σ, …, σ)` contribute `(1 + (-1)ⁿ⁺¹)` times its value and the inner faces are
degenerate. -/
@[reassoc]
lemma cosimplicialPInftyApp_objD_genProj {M : 𝒜} (hM : (2 : ℤ) • 𝟙 M = 0) (n : ℕ) :
    cosimplicialPInftyApp (cochainCosimplicial M) n ≫
      AlternatingCofaceMapComplex.objD (cochainCosimplicial M) n ≫ genProj M (n + 1) = 0 := by
  rw [AlternatingCofaceMapComplex.objD, Preadditive.sum_comp, Preadditive.comp_sum]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, genProj, evalAt,
    powCosimplicial_δ_π]
  rw [Fintype.sum_eq_add 0 (Fin.last (n + 1)) (fun h => by simpa using congrArg Fin.val h)]
  · rw [δ_zero_genSimplex, δ_last_genSimplex, Fin.val_zero, Fin.val_last, pow_zero, one_smul]
    rcases neg_one_pow_eq_or ℤ (n + 1) with h | h
    · rw [h, one_smul]
      exact add_self_eq_zero hM _
    · rw [h, neg_smul, one_smul, add_neg_cancel]
  · rintro i ⟨h₀, h₁⟩
    rw [show Pi.π (fun _ : nerveZModTwo _⦋n⦌ => M) (nerveZModTwo.δ i (genSimplex (n + 1))) =
      evalAt M (nerveZModTwo.δ i (genSimplex (n + 1))) from rfl,
      cosimplicialPInftyApp_π_of_ne _ _ (δ_genSimplex_ne i h₀ h₁), smul_zero]

/-- When `2 • 𝟙 M = 0`, the dual Dold–Kan projection followed by the differential vanishes:
the normalized cochain complex has zero differential. -/
@[reassoc]
lemma cosimplicialPInftyApp_objD {M : 𝒜} (hM : (2 : ℤ) • 𝟙 M = 0) (n : ℕ) :
    cosimplicialPInftyApp (cochainCosimplicial M) n ≫
      AlternatingCofaceMapComplex.objD (cochainCosimplicial M) n = 0 := by
  rw [cosimplicialPInftyApp_comm, ← cosimplicialPInftyApp_genProj_genIncl M (n + 1),
    ← Category.assoc, ← cosimplicialPInftyApp_comm, Category.assoc,
    cosimplicialPInftyApp_objD_genProj_assoc hM, zero_comp]

/-- When `2 • 𝟙 M = 0`, the inclusion of `M` at `(σ, …, σ)` is a cocycle in every degree. -/
lemma genIncl_objD {M : 𝒜} (hM : (2 : ℤ) • 𝟙 M = 0) (n : ℕ) :
    genIncl M n ≫ AlternatingCofaceMapComplex.objD (cochainCosimplicial M) n = 0 := by
  rw [← genIncl_comp_cosimplicialPInftyApp M n, Category.assoc, cosimplicialPInftyApp_objD hM,
    comp_zero]

/-- When `2 • 𝟙 M = 0`, the differential followed by the retraction vanishes. -/
lemma objD_cosimplicialPInftyApp_genProj {M : 𝒜} (hM : (2 : ℤ) • 𝟙 M = 0) (n : ℕ) :
    AlternatingCofaceMapComplex.objD (cochainCosimplicial M) n ≫
      cosimplicialPInftyApp (cochainCosimplicial M) (n + 1) ≫ genProj M (n + 1) = 0 := by
  rw [← Category.assoc, ← cosimplicialPInftyApp_comm, cosimplicialPInftyApp_objD hM, zero_comp]

/-- The inclusion `zeroDiffComplex M ⟶ barCochainComplex M`, the cochains supported on the
nondegenerate simplices `(σ, …, σ)`; a morphism of complexes when `2 • 𝟙 M = 0`. -/
def zeroDiffComplexToBar {M : 𝒜} (hM : (2 : ℤ) • 𝟙 M = 0) :
    zeroDiffComplex M ⟶ barCochainComplex M :=
  CochainComplex.ofHom (fun n => genIncl M n) (fun i =>
    (congrArg (genIncl M i ≫ ·) (alternatingCofaceMapComplex_obj_d (cochainCosimplicial M) i)).trans
      ((genIncl_objD hM i).trans zero_comp.symm))

/-- The retraction `barCochainComplex M ⟶ zeroDiffComplex M`: apply the dual Dold–Kan
projection, then evaluate at `(σ, …, σ)`; a morphism of complexes when `2 • 𝟙 M = 0`. -/
def barToZeroDiffComplex {M : 𝒜} (hM : (2 : ℤ) • 𝟙 M = 0) :
    barCochainComplex M ⟶ zeroDiffComplex M :=
  CochainComplex.ofHom (fun n => cosimplicialPInftyApp (cochainCosimplicial M) n ≫ genProj M n)
    (fun i => comp_zero.trans ((objD_cosimplicialPInftyApp_genProj hM i).symm.trans
      (congrArg (· ≫ (cosimplicialPInftyApp (cochainCosimplicial M) (i + 1) ≫ genProj M (i + 1)))
        (alternatingCofaceMapComplex_obj_d (cochainCosimplicial M) i).symm)))

/-- **The inhomogeneous cochain complex of `ℤ/2` with trivial coefficients `M`, where
`2 • 𝟙 M = 0`, is homotopy equivalent to the complex with `M` in each degree `≥ 0` and zero
differential.** -/
def homotopyEquivZeroDiffComplex {M : 𝒜} (hM : (2 : ℤ) • 𝟙 M = 0) :
    HomotopyEquiv (zeroDiffComplex M) (barCochainComplex M) where
  hom := zeroDiffComplexToBar hM
  inv := barToZeroDiffComplex hM
  homotopyHomInvId := Homotopy.ofEq (by
    ext n
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ genProj M n)
      (genIncl_comp_cosimplicialPInftyApp M n)).trans (genIncl_genProj M n)))
  homotopyInvHomId := (Homotopy.ofEq (by
    ext n
    exact (Category.assoc _ _ _).trans (cosimplicialPInftyApp_genProj_genIncl M n))).trans
      (homotopyCosimplicialPInftyId _)

/-- The components of the inclusion of `homotopyEquivZeroDiffComplex`. -/
@[simp]
lemma homotopyEquivZeroDiffComplex_hom_f {M : 𝒜} (hM : (2 : ℤ) • 𝟙 M = 0) (n : ℕ) :
    (homotopyEquivZeroDiffComplex hM).hom.f n = genIncl M n := rfl

/-- The components of the retraction of `homotopyEquivZeroDiffComplex`. -/
@[simp]
lemma homotopyEquivZeroDiffComplex_inv_f {M : 𝒜} (hM : (2 : ℤ) • 𝟙 M = 0) (n : ℕ) :
    (homotopyEquivZeroDiffComplex hM).inv.f n =
      cosimplicialPInftyApp (cochainCosimplicial M) n ≫ genProj M n := rfl

/-- Naturality in `M` of `genIncl`. -/
lemma genIncl_naturality {M M' : 𝒜} (f : M ⟶ M') (n : ℕ) :
    f ≫ genIncl M' n = genIncl M n ≫ (powCosimplicialMap nerveZModTwo f).app ⦋n⦌ := by
  refine Pi.hom_ext _ _ fun y => ?_
  rw [Category.assoc, Category.assoc, powCosimplicialMap_app_π]
  by_cases hy : y = genSimplex n
  · subst hy
    rw [show Pi.π (fun _ : nerveZModTwo _⦋n⦌ => M') (genSimplex n) = genProj M' n from rfl,
      show Pi.π (fun _ : nerveZModTwo _⦋n⦌ => M) (genSimplex n) = genProj M n from rfl,
      genIncl_genProj, genIncl_genProj_assoc, Category.comp_id]
  · rw [show Pi.π (fun _ : nerveZModTwo _⦋n⦌ => M') y = evalAt M' y from rfl,
      show Pi.π (fun _ : nerveZModTwo _⦋n⦌ => M) y = evalAt M y from rfl,
      genIncl_π _ _ hy, comp_zero, genIncl_π_assoc _ _ hy, zero_comp]

/-- Naturality in `M` of the retraction. -/
lemma cosimplicialPInftyApp_genProj_naturality {M M' : 𝒜} (f : M ⟶ M') (n : ℕ) :
    (powCosimplicialMap nerveZModTwo f).app ⦋n⦌ ≫
        cosimplicialPInftyApp (cochainCosimplicial M') n ≫ genProj M' n =
      (cosimplicialPInftyApp (cochainCosimplicial M) n ≫ genProj M n) ≫ f := by
  rw [← cosimplicialPInftyApp_naturality_assoc, genProj, genProj, evalAt, evalAt,
    powCosimplicialMap_app_π, Category.assoc]

/-- Naturality in `M` of the inclusion of `homotopyEquivZeroDiffComplex`. -/
lemma homotopyEquivZeroDiffComplex_hom_naturality {M M' : 𝒜} (hM : (2 : ℤ) • 𝟙 M = 0)
    (hM' : (2 : ℤ) • 𝟙 M' = 0) (f : M ⟶ M') :
    zeroDiffComplexMap f ≫ (homotopyEquivZeroDiffComplex hM').hom =
      (homotopyEquivZeroDiffComplex hM).hom ≫
        (alternatingCofaceMapComplex 𝒜).map (powCosimplicialMap nerveZModTwo f) := by
  ext n
  exact genIncl_naturality f n

/-- Naturality in `M` of the retraction of `homotopyEquivZeroDiffComplex`. -/
lemma homotopyEquivZeroDiffComplex_inv_naturality {M M' : 𝒜} (hM : (2 : ℤ) • 𝟙 M = 0)
    (hM' : (2 : ℤ) • 𝟙 M' = 0) (f : M ⟶ M') :
    (alternatingCofaceMapComplex 𝒜).map (powCosimplicialMap nerveZModTwo f) ≫
        (homotopyEquivZeroDiffComplex hM').inv =
      (homotopyEquivZeroDiffComplex hM).inv ≫ zeroDiffComplexMap f := by
  ext n
  exact cosimplicialPInftyApp_genProj_naturality f n

end Complexes

/-! ### The `ℤ`-indexed complexes -/

section Int

variable [Preadditive 𝒜] [HasZeroObject 𝒜]

/-- A homotopy equivalence of complexes extends along an embedding of complex shapes. -/
def homotopyEquivExtend {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    {K L : HomologicalComplex 𝒜 c} (h : HomotopyEquiv K L) (e : c.Embedding c') [e.IsRelIff] :
    HomotopyEquiv (K.extend e) (L.extend e) where
  hom := HomologicalComplex.extendMap h.hom e
  inv := HomologicalComplex.extendMap h.inv e
  homotopyHomInvId := by
    rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_id]
    exact h.homotopyHomInvId.extend e
  homotopyInvHomId := by
    rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_id]
    exact h.homotopyInvHomId.extend e

variable [HasFiniteProducts 𝒜]

/-- The inhomogeneous cochain complex of `ℤ/2` with trivial coefficients `M`, indexed by `ℤ` and
zero in negative degrees. -/
abbrev barCochainComplexInt (M : 𝒜) : CochainComplex 𝒜 ℤ :=
  (barCochainComplex M).extend ComplexShape.embeddingUpNat

/-- The complex with `M` in each degree `≥ 0`, zero in negative degrees, and zero differential. -/
abbrev zeroDiffComplexInt (M : 𝒜) : CochainComplex 𝒜 ℤ :=
  (zeroDiffComplex M).extend ComplexShape.embeddingUpNat

/-- **The `ℤ`-indexed version of `homotopyEquivZeroDiffComplex`.** -/
def homotopyEquivZeroDiffComplexInt {M : 𝒜} (hM : (2 : ℤ) • 𝟙 M = 0) :
    HomotopyEquiv (zeroDiffComplexInt M) (barCochainComplexInt M) :=
  homotopyEquivExtend (homotopyEquivZeroDiffComplex hM) ComplexShape.embeddingUpNat

/-- The inclusion of `homotopyEquivZeroDiffComplexInt` is the extension of that of
`homotopyEquivZeroDiffComplex`. -/
lemma homotopyEquivZeroDiffComplexInt_hom {M : 𝒜} (hM : (2 : ℤ) • 𝟙 M = 0) :
    (homotopyEquivZeroDiffComplexInt hM).hom =
      HomologicalComplex.extendMap (homotopyEquivZeroDiffComplex hM).hom _ := rfl

/-- The retraction of `homotopyEquivZeroDiffComplexInt` is the extension of that of
`homotopyEquivZeroDiffComplex`. -/
lemma homotopyEquivZeroDiffComplexInt_inv {M : 𝒜} (hM : (2 : ℤ) • 𝟙 M = 0) :
    (homotopyEquivZeroDiffComplexInt hM).inv =
      HomologicalComplex.extendMap (homotopyEquivZeroDiffComplex hM).inv _ := rfl

/-- Naturality in `M` of the inclusion of `homotopyEquivZeroDiffComplexInt`. -/
lemma homotopyEquivZeroDiffComplexInt_hom_naturality {M M' : 𝒜} (hM : (2 : ℤ) • 𝟙 M = 0)
    (hM' : (2 : ℤ) • 𝟙 M' = 0) (f : M ⟶ M') :
    HomologicalComplex.extendMap (zeroDiffComplexMap f) ComplexShape.embeddingUpNat ≫
        (homotopyEquivZeroDiffComplexInt hM').hom =
      (homotopyEquivZeroDiffComplexInt hM).hom ≫
        HomologicalComplex.extendMap
          ((alternatingCofaceMapComplex 𝒜).map (powCosimplicialMap nerveZModTwo f))
          ComplexShape.embeddingUpNat := by
  rw [homotopyEquivZeroDiffComplexInt_hom, homotopyEquivZeroDiffComplexInt_hom,
    ← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    homotopyEquivZeroDiffComplex_hom_naturality hM hM']

/-- Naturality in `M` of the retraction of `homotopyEquivZeroDiffComplexInt`. -/
lemma homotopyEquivZeroDiffComplexInt_inv_naturality {M M' : 𝒜} (hM : (2 : ℤ) • 𝟙 M = 0)
    (hM' : (2 : ℤ) • 𝟙 M' = 0) (f : M ⟶ M') :
    HomologicalComplex.extendMap
          ((alternatingCofaceMapComplex 𝒜).map (powCosimplicialMap nerveZModTwo f))
          ComplexShape.embeddingUpNat ≫ (homotopyEquivZeroDiffComplexInt hM').inv =
      (homotopyEquivZeroDiffComplexInt hM).inv ≫
        HomologicalComplex.extendMap (zeroDiffComplexMap f) ComplexShape.embeddingUpNat := by
  rw [homotopyEquivZeroDiffComplexInt_inv, homotopyEquivZeroDiffComplexInt_inv,
    ← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    homotopyEquivZeroDiffComplex_inv_naturality hM hM']

end Int

end Stacks.GroupCohomology.TrivialBar
