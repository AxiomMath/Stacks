module

public import StacksFrontier.CategoryTheory.Sites.Topos.PolynomialSystemSections

/-!
# The sheaf of solutions of a polynomial system over a base ring is an equalizer

Let `𝒪` be a sheaf of commutative rings on a site `(C, J)` whose sections are algebras over one
fixed ring `R₀`, compatibly with restriction — a *sheaf of `R₀`-algebras*, given here as the
family `sec` of structure maps and its compatibility `hsec`.  A family `P₁, …, P_n` of polynomials
in `n` variables with coefficients in `R₀` then has a *row* `∏ⁿ 𝒪 ⇉ ∏ⁿ 𝒪`
(`CategoryTheory.CommRingObj.evalSystemHom` against `zeroSystemHom`), and this file shows:

**a sheaf `H` whose sections over every object of the site are, naturally, the solutions of the
system in the sections of `𝒪`, is the equalizer of that row.**

This is step (2) of the proof of [Stacks Project, Tag 04I6] at the level of sheaves.  There
`R₀ = Γ(Y, ⊤) = B`, the site is the small étale site of `Y = Spec(B)`, `𝒪 = 𝒪_Y` with
`sec U = p_U^♯` the structure map of the chart `U` on global functions, `P` is a standard
presentation `C = B[x₁, …, x_n]/(P₁, …, P_n)` of an affine `V` étale over `Y`, and `H = h_V`: the
natural identification of `Hom_Y(U, V)` with the solutions of the system in `Γ(U, ⊤)` is
`Stacks.EtaleCohomology.homOverEquivSolutions` together with
`Stacks.EtaleCohomology.homOverEquivSolutions_naturality`.

## Main definitions

* `Stacks.Sheaves.PolynomialSystem.baseCoefficients`: the coefficients of the system, read as
  global sections of `𝒪` — the ring homomorphism `R₀ ⟶ Γ(C, 𝒪)` assembled from `sec`.
* `Stacks.Sheaves.PolynomialSystem.coordinates`: the morphism `H ⟶ ∏ⁿ 𝒪` given by a natural
  family of `n`-tuples of sections.

## Main results

* `Stacks.Sheaves.PolynomialSystem.globalSectionRingHom_comp_baseCoefficients`: the coefficients,
  restricted to an object `X` of the site, are the structure map `sec X`.
* `Stacks.Sheaves.PolynomialSystem.isLimitForkOfSolutionEquiv`: a sheaf whose sections are
  naturally the solutions of the system is the equalizer of its row.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped CommRingObj Obj

universe w v u

namespace Stacks.Sheaves.PolynomialSystem

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget CommRingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})]

attribute [local instance] Stacks.sheafCommRingObj

/-! ### The coefficients of a system over a base ring, as global sections -/

section Coefficients

variable (O : Sheaf J CommRingCat.{w}) (R₀ : CommRingCat.{w})
  (sec : ∀ X : Cᵒᵖ, R₀ ⟶ O.obj.obj X)
  (hsec : ∀ {X X' : Cᵒᵖ} (g : X ⟶ X'), sec X ≫ O.obj.map g = sec X')

/-- The section of `𝒪` over every object of the site named by an element of the base ring: the
image of that element under the structure map.  This is a *global* section, i.e. a generalized
element of shape `𝟙`, because the structure maps are compatible with restriction. -/
def baseSection (r : R₀) : 𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O :=
  Sheaf.constHom (fun X => (sec X).hom r) (fun {_X X'} g =>
    congrArg (fun φ : R₀ ⟶ O.obj.obj X' => φ.hom r) (hsec g))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] in
/-- Over an object `X`, the section `baseSection O R₀ sec hsec r` is `sec X r`. -/
@[simp]
theorem sections_map_baseSection (r : R₀) (X : Cᵒᵖ)
    (p : (Sheaf.sectionsFunctor J X).obj (⊤_ (Sheaf J (Type w)))) :
    (Sheaf.sectionsFunctor J X).map (baseSection O R₀ sec hsec r) p = (sec X).hom r :=
  rfl

/-- **The coefficients of a polynomial system over the base ring, as global sections of `𝒪`.**
Taking the global section named by an element of `R₀` is a ring homomorphism, because each
structure map `sec X` is one and the ring operations on generalized elements of `𝒪` are the
sectionwise operations. -/
def baseCoefficients : R₀ →+* (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O) where
  toFun := baseSection O R₀ sec hsec
  map_one' := Sheaf.hom_ext_sections fun X p =>
    (sections_map_baseSection O R₀ sec hsec 1 X p).trans
      ((map_one (sec X).hom).trans (sections_map_one X p).symm)
  map_mul' r s := Sheaf.hom_ext_sections fun X p =>
    (sections_map_baseSection O R₀ sec hsec (r * s) X p).trans
      ((map_mul (sec X).hom r s).trans (sections_map_mul X (baseSection O R₀ sec hsec r)
        (baseSection O R₀ sec hsec s) p).symm)
  map_zero' := Sheaf.hom_ext_sections fun X p =>
    (sections_map_baseSection O R₀ sec hsec 0 X p).trans
      ((map_zero (sec X).hom).trans (sections_map_zero X p).symm)
  map_add' r s := Sheaf.hom_ext_sections fun X p =>
    (sections_map_baseSection O R₀ sec hsec (r + s) X p).trans
      ((map_add (sec X).hom r s).trans (sections_map_add X (baseSection O R₀ sec hsec r)
        (baseSection O R₀ sec hsec s) p).symm)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The coefficients, restricted to an object of the site, are its structure map.** -/
theorem globalSectionRingHom_comp_baseCoefficients (X : Cᵒᵖ) :
    (globalSectionRingHom O X).comp (baseCoefficients O R₀ sec hsec) = (sec X).hom :=
  RingHom.ext fun _r => rfl

end Coefficients

/-! ### The coordinates of a sheaf of solutions -/

section Coordinates

variable (O : Sheaf J CommRingCat.{w}) {H : Sheaf J (Type w)} {n : ℕ}
  (a : ∀ X : Cᵒᵖ, (Sheaf.sectionsFunctor J X).obj H → Fin n → O.obj.obj X)
  (ha : ∀ {X X' : Cᵒᵖ} (g : X ⟶ X') (t : (Sheaf.sectionsFunctor J X).obj H) (i : Fin n),
    (O.obj.map g).hom (a X t i) = a X' (H.obj.map g t) i)

/-- The morphism `H ⟶ ∏ⁿ 𝒪` assembled from a natural family of `n`-tuples of sections. -/
def coordinates : H ⟶ ∏ᶜ fun _ : Fin n => Stacks.underlyingRingSheaf J O :=
  Pi.lift fun i => Sheaf.unaryOpHom (fun X t => a X t i) (fun {_X _X'} g t => ha g t i)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] in
/-- The `i`-th coordinate of `coordinates O a ha` over `X` sends a section `t` to `a X t i`. -/
@[simp]
theorem sections_map_coordinates_comp_π (X : Cᵒᵖ) (i : Fin n)
    (t : (Sheaf.sectionsFunctor J X).obj H) :
    (Sheaf.sectionsFunctor J X).map (coordinates O a ha ≫ Pi.π _ i) t = a X t i :=
  congrArg (fun m => (Sheaf.sectionsFunctor J X).map m t) (Pi.lift_π _ i)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] in
/-- Projecting the image of a section `t` under `coordinates O a ha` to its `i`-th factor gives
`a X t i`. -/
@[simp]
theorem sections_map_π_coordinates (X : Cᵒᵖ) (i : Fin n)
    (t : (Sheaf.sectionsFunctor.{w} J X).obj H) :
    (Sheaf.sectionsFunctor.{w} J X).map (Pi.π _ i)
        ((Sheaf.sectionsFunctor.{w} J X).map (coordinates O a ha) t) = a X t i :=
  ((Sheaf.sectionsFunctor.{w} J X).map_comp_apply _ _ t).symm.trans
    (sections_map_coordinates_comp_π O a ha X i t)

end Coordinates

/-! ### The equalizer presentation -/

section Main

variable (O : Sheaf J CommRingCat.{w}) (R₀ : CommRingCat.{w})
  (sec : ∀ X : Cᵒᵖ, R₀ ⟶ O.obj.obj X)
  (hsec : ∀ {X X' : Cᵒᵖ} (g : X ⟶ X'), sec X ≫ O.obj.map g = sec X')
  {H : Sheaf J (Type w)} {n : ℕ} (P : Fin n → MvPolynomial (Fin n) R₀)
  (e : ∀ X : Cᵒᵖ, (Sheaf.sectionsFunctor J X).obj H ≃
    {b : Fin n → O.obj.obj X // MvPolynomial.IsSolution P (sec X).hom b})
  (he : ∀ {X X' : Cᵒᵖ} (g : X ⟶ X') (t : (Sheaf.sectionsFunctor J X).obj H) (i : Fin n),
    (O.obj.map g).hom ((e X t).1 i) = (e X' (H.obj.map g t)).1 i)

/-- The morphism `H ⟶ ∏ⁿ 𝒪` reading a section of `H` as the solution it names. -/
def solutionCoordinates : H ⟶ ∏ᶜ fun _ : Fin n => Stacks.underlyingRingSheaf J O :=
  coordinates O (fun X t i => (e X t).1 i) (fun {_ _} g t i => he g t i)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] in
/-- The `i`-th coordinate of the image of a section `t` under `solutionCoordinates` is the `i`-th
coordinate of the solution `e X t`. -/
theorem sections_map_π_solutionCoordinates (X : Cᵒᵖ) (i : Fin n)
    (t : (Sheaf.sectionsFunctor.{w} J X).obj H) :
    (Sheaf.sectionsFunctor.{w} J X).map (Pi.π _ i)
        ((Sheaf.sectionsFunctor.{w} J X).map (solutionCoordinates O R₀ sec P e he) t) =
      (e X t).1 i :=
  sections_map_π_coordinates O _ _ X i t

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The coordinates of a section of `H` solve the system: that is the content of `e`. -/
theorem solutionCoordinates_comp_evalSystemHom :
    solutionCoordinates O R₀ sec P e he ≫
        CommRingObj.evalSystemHom _ (baseCoefficients O R₀ sec hsec) (Fin n) P =
      solutionCoordinates O R₀ sec P e he ≫
        CommRingObj.zeroSystemHom _ (Fin n) (Fin n) := by
  refine comp_evalSystemHom_eq_comp_zeroSystemHom O (baseCoefficients O R₀ sec hsec) P
    (solutionCoordinates O R₀ sec P e he) (fun X t => ?_)
  have hfun : (fun i => (Sheaf.sectionsFunctor J X).map
        (solutionCoordinates O R₀ sec P e he ≫
          Pi.π (fun _ : Fin n => Stacks.underlyingRingSheaf J O) i) t) =
      fun i => (e X t).1 i :=
    funext fun i => sections_map_coordinates_comp_π O _ _ X i t
  rw [globalSectionRingHom_comp_baseCoefficients, hfun]
  exact (e X t).2

/-- **The equalizer presentation of a sheaf of solutions of a polynomial system over a base
ring.**  Let `𝒪` be a sheaf of commutative rings whose sections are `R₀`-algebras compatibly with
restriction, let `P₁, …, P_n ∈ R₀[x₁, …, x_n]`, and let `H` be a sheaf whose sections over every
object `X` of the site are, naturally in `X`, the solutions of the system in `Γ(X, 𝒪)`.  Then `H`
is the equalizer of the two legs `∏ⁿ 𝒪 ⇉ ∏ⁿ 𝒪` of the row of the system. -/
def isLimitForkOfSolutionEquiv :
    IsLimit (Fork.ofι (solutionCoordinates O R₀ sec P e he)
      (solutionCoordinates_comp_evalSystemHom O R₀ sec hsec P e he)) := by
  refine isLimitForkOfSections O (baseCoefficients O R₀ sec hsec) P _ (fun X t t' h => ?_)
    (fun X l hl => ?_) _
  · refine (e X).injective (Subtype.ext (funext fun i => ?_))
    have h1 := sections_map_π_solutionCoordinates O R₀ sec P e he X i t
    have h2 := sections_map_π_solutionCoordinates O R₀ sec P e he X i t'
    rw [← h1, ← h2]
    exact congrArg ((Sheaf.sectionsFunctor.{w} J X).map (Pi.π _ i)) h
  · rw [globalSectionRingHom_comp_baseCoefficients] at hl
    refine ⟨(e X).symm ⟨_, hl⟩, ?_⟩
    change (Sheaf.sectionsFunctor.{w} J X).map (solutionCoordinates O R₀ sec P e he)
        ((e X).symm ⟨_, hl⟩) = l
    refine Functor.piObjMk_ext (fun i => ?_)
    rw [sections_map_π_solutionCoordinates O R₀ sec P e he X i, Equiv.apply_symm_apply]

end Main

end Stacks.Sheaves.PolynomialSystem

end
