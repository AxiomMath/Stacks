module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraSheaf
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ExtensionByInitial

/-!
# The stalk of the free algebra sheaf

Let `A` be a sheaf of commutative rings on a topological space `X`, let `E` be a presheaf of
sets on `X` and let `x` be a point of `X`. The stalk at `x` of the free `A`-algebra `A[E]` on
`E` is the polynomial algebra on the stalk of `E` over the stalk of `A`:
`(A[E])ₓ ≅ Aₓ[Eₓ]`.

Sheafification does not change stalks, so the stalk of `A[E]` is the stalk of the presheaf
`U ↦ A(U)[E(U)]`, that is, the filtered colimit of the polynomial rings `A(U)[E(U)]` over the
open neighbourhoods of `x`; the content of the statement is that forming a polynomial algebra
commutes with that colimit in both the coefficients and the variables.

## Main definitions

* `Stacks.Sites.FreeAlgebra.polynomialStalkEval`: evaluation `A(U)[E(U)] → Aₓ[Eₓ]` of a
  polynomial at the germs of its coefficients and of its variables.
* `Stacks.Sites.FreeAlgebra.polynomialStalkHom`: the induced comparison map from the stalk of
  `U ↦ A(U)[E(U)]` to `Aₓ[Eₓ]`.
* `Stacks.Sites.FreeAlgebra.polynomialStalkInv`: the map back, sending a coefficient to the
  germ of a constant polynomial and a variable to the germ of a variable.
* `Stacks.Sites.FreeAlgebra.polynomialPresheafStalkRingEquiv`: the comparison map as an
  isomorphism of rings.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafStalkRingEquiv`: the isomorphism
  `(A[E])ₓ ≅ Aₓ[Eₓ]`.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafStalkIso`: the same isomorphism in `CommRingCat`.

## Main results

* `Stacks.Sites.FreeAlgebra.polynomialStalkHom_germ`: the comparison map sends the germ of a
  polynomial to its evaluation at germs.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafStalkRingEquiv_coefficientMap`: the composite of the
  stalk of the structural morphism `A ⟶ A[E]` with the isomorphism is the coefficient inclusion.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafStalkRingEquiv_variable`: the isomorphism carries the
  germ of the variable `[t]` to the variable indexed by the germ of `t`.

## Implementation notes

The polynomial ring `A(U)[E(U)]` carries two definitionally equal but syntactically different
descriptions: as the type `MvPolynomial (E(U)) (A(U))` with its own ring structure, and as the
underlying type of the object `(polynomialPresheaf J A E).obj (op U)` of `CommRingCat`. Unifying
the two is cheap on morphisms and ruinous on elements, because the ring structure of
`MvPolynomial` is a `Finsupp` construction. Everything below is therefore phrased with bundled
ring homomorphisms between the honest polynomial rings — `polynomialRestrictHom`,
`polynomialGermHom`, `polynomialStalkEval` — and the passage to `CommRingCat` happens only at the
level of morphisms, through `CommRingCat.hom_ext` and `congrArg CommRingCat.Hom.hom`.

That the comparison map is bijective is proved without any combinatorics on monomials: the map
back is produced by the universal property of a polynomial algebra, and the two round trips are
checked on coefficients and on variables, using that every element of a stalk is a germ and that
a morphism out of a stalk is determined by its composites with the germ maps.

## References

* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat.Presheaf

universe u

noncomputable section

namespace Stacks.Sites.FreeAlgebra

variable {X : TopCat.{u}} (A : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (E : X.Presheaf (Type u)) (x : X)

/-- Presheaves of commutative rings on a topological space admit sheafification: the site of
open subsets is small. -/
instance hasSheafifyOpensCommRingCat :
    HasSheafify (Opens.grothendieckTopology X) CommRingCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-! ### Sections of the presheaf of polynomial rings -/

/-- The restriction map `A(U)[E(U)] → A(V)[E(V)]` of the presheaf of polynomial rings along an
inclusion `V ⊆ U`, as a homomorphism between polynomial rings. -/
def polynomialRestrictHom {U V : Opens X} (i : V ⟶ U) :
    MvPolynomial (E.obj (op U)) (ToType (A.obj.obj (op U))) →+*
      MvPolynomial (E.obj (op V)) (ToType (A.obj.obj (op V))) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (A.obj.map i.op).hom)
    (fun e => MvPolynomial.X (E.map i.op e))

/-- The germ at `x` of a polynomial with coefficients and variables defined on an open
neighbourhood `U` of `x`, as a homomorphism to the stalk of the presheaf of polynomial rings. -/
def polynomialGermHom (U : Opens X) (hx : x ∈ U) :
    MvPolynomial (E.obj (op U)) (ToType (A.obj.obj (op U))) →+*
      ToType (stalk (polynomialPresheaf (Opens.grothendieckTopology X) A E) x) :=
  (germ (polynomialPresheaf (Opens.grothendieckTopology X) A E) U x hx).hom

/-- Taking germs at `x` is unchanged by restricting to a smaller neighbourhood of `x`. -/
theorem polynomialGermHom_comp_restrict {U V : Opens X} (i : V ⟶ U) (hV : x ∈ V) :
    (polynomialGermHom A E x V hV).comp (polynomialRestrictHom A E i) =
      polynomialGermHom A E x U (i.le hV) :=
  congrArg CommRingCat.Hom.hom
    (germ_res (polynomialPresheaf (Opens.grothendieckTopology X) A E) i x hV)

/-- The germ of the variable attached to a restricted section is the germ of the variable
attached to the section. -/
theorem polynomialGermHom_X_res {U V : Opens X} (i : V ⟶ U) (hV : x ∈ V) (t : E.obj (op U)) :
    polynomialGermHom A E x V hV (MvPolynomial.X (E.map i.op t)) =
      polynomialGermHom A E x U (i.le hV) (MvPolynomial.X t) := by
  rw [← polynomialGermHom_comp_restrict A E x i hV, RingHom.comp_apply, polynomialRestrictHom,
    MvPolynomial.eval₂Hom_X']

/-! ### The comparison map -/

/-- Evaluation `A(U)[E(U)] → Aₓ[Eₓ]` of a polynomial over an open neighbourhood `U` of `x` at
the germs at `x` of its coefficients and of its variables. -/
def polynomialStalkEval (U : Opens X) (hx : x ∈ U) :
    MvPolynomial (E.obj (op U)) (ToType (A.obj.obj (op U))) →+*
      MvPolynomial (E.stalk x) (ToType (stalk A.obj x)) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (germ A.obj U x hx).hom)
    (fun e => MvPolynomial.X ((E.germ U x hx).hom e))

/-- Evaluation at germs sends a constant polynomial to the constant polynomial on the germ of its
value. -/
@[simp]
theorem polynomialStalkEval_C (U : Opens X) (hx : x ∈ U) (r : ToType (A.obj.obj (op U))) :
    polynomialStalkEval A E x U hx (MvPolynomial.C r) =
      MvPolynomial.C ((germ A.obj U x hx).hom r) := by
  simp [polynomialStalkEval]

/-- Evaluation at germs sends the variable indexed by a section `t` of `E` to the variable indexed
by the germ of `t`. -/
@[simp]
theorem polynomialStalkEval_X (U : Opens X) (hx : x ∈ U) (t : E.obj (op U)) :
    polynomialStalkEval A E x U hx (MvPolynomial.X t) =
      MvPolynomial.X ((E.germ U x hx).hom t) := by
  simp [polynomialStalkEval]

/-- Evaluation at germs is compatible with restriction to a smaller neighbourhood. -/
theorem polynomialStalkEval_comp_restrict {U V : Opens X} (i : V ⟶ U) (hV : x ∈ V) :
    (polynomialStalkEval A E x V hV).comp (polynomialRestrictHom A E i) =
      polynomialStalkEval A E x U (i.le hV) := by
  apply MvPolynomial.ringHom_ext <;> intro a <;> simp [polynomialRestrictHom]

/-- Evaluation at germs, as a morphism of `CommRingCat` out of the sections of the presheaf of
polynomial rings. -/
def polynomialStalkEvalApp (U : Opens X) (hx : x ∈ U) :
    (polynomialPresheaf (Opens.grothendieckTopology X) A E).obj (op U) ⟶
      CommRingCat.of (MvPolynomial (E.stalk x) (ToType (stalk A.obj x))) :=
  CommRingCat.ofHom (polynomialStalkEval A E x U hx)

/-- Evaluation at germs, as a morphism of `CommRingCat`, is compatible with restriction to a
smaller neighbourhood. -/
theorem map_comp_polynomialStalkEvalApp {U V : Opens X} (i : V ⟶ U) (hV : x ∈ V) :
    (polynomialPresheaf (Opens.grothendieckTopology X) A E).map i.op ≫
        polynomialStalkEvalApp A E x V hV = polynomialStalkEvalApp A E x U (i.le hV) :=
  CommRingCat.hom_ext (polynomialStalkEval_comp_restrict A E x i hV)

/-- The polynomial algebra `Aₓ[Eₓ]` on the stalks, as a cocone over the diagram of polynomial
rings whose colimit is the stalk of the presheaf of polynomial rings. -/
def polynomialStalkCocone :
    Cocone ((OpenNhds.inclusion x).op ⋙
      polynomialPresheaf (Opens.grothendieckTopology X) A E) where
  pt := CommRingCat.of (MvPolynomial (E.stalk x) (ToType (stalk A.obj x)))
  ι :=
    { app := fun V => polynomialStalkEvalApp A E x V.unop.1 V.unop.2
      naturality := fun _ W f =>
        (map_comp_polynomialStalkEvalApp A E x ((OpenNhds.inclusion x).map f.unop)
          W.unop.2).trans (Category.comp_id _).symm }

/-- The comparison homomorphism from the stalk of the presheaf `U ↦ A(U)[E(U)]` to the polynomial
algebra `Aₓ[Eₓ]` on the stalks. -/
def polynomialStalkHom :
    ToType (stalk (polynomialPresheaf (Opens.grothendieckTopology X) A E) x) →+*
      MvPolynomial (E.stalk x) (ToType (stalk A.obj x)) :=
  (colimit.desc _ (polynomialStalkCocone A E x)).hom

/-- The composite of the germ map over `U` with the comparison map is evaluation at germs. -/
theorem polynomialStalkHom_comp_germ (U : Opens X) (hx : x ∈ U) :
    (polynomialStalkHom A E x).comp (polynomialGermHom A E x U hx) =
      polynomialStalkEval A E x U hx :=
  congrArg CommRingCat.Hom.hom
    (colimit.ι_desc (polynomialStalkCocone A E x) (op (⟨U, hx⟩ : OpenNhds x)))

/-- The comparison map sends the germ of a polynomial over an open neighbourhood of `x` to its
evaluation at germs. -/
theorem polynomialStalkHom_germ (U : Opens X) (hx : x ∈ U)
    (p : MvPolynomial (E.obj (op U)) (ToType (A.obj.obj (op U)))) :
    polynomialStalkHom A E x (polynomialGermHom A E x U hx p) =
      polynomialStalkEval A E x U hx p :=
  DFunLike.congr_fun (polynomialStalkHom_comp_germ A E x U hx) p

/-! ### The map back -/

/-- The germs of the variables, as a cocone over the diagram of sections of `E` near `x`. -/
def polynomialVariableCocone : Cocone ((OpenNhds.inclusion x).op ⋙ E) where
  pt := ToType (stalk (polynomialPresheaf (Opens.grothendieckTopology X) A E) x)
  ι :=
    { app := fun V => TypeCat.ofHom fun t =>
        polynomialGermHom A E x V.unop.1 V.unop.2 (MvPolynomial.X t)
      naturality := by
        intro _ W f
        ext t
        exact polynomialGermHom_X_res A E x ((OpenNhds.inclusion x).map f.unop) W.unop.2 t }

/-- The map sending the germ of a section of `E` at `x` to the germ of the corresponding
variable. -/
def polynomialVariableStalk :
    E.stalk x → ToType (stalk (polynomialPresheaf (Opens.grothendieckTopology X) A E) x) :=
  (colimit.desc _ (polynomialVariableCocone A E x)).hom

/-- `polynomialVariableStalk` sends the germ of a section `t` of `E` to the germ of the variable
indexed by `t`. -/
theorem polynomialVariableStalk_germ (U : Opens X) (hx : x ∈ U) (t : E.obj (op U)) :
    polynomialVariableStalk A E x ((E.germ U x hx).hom t) =
      polynomialGermHom A E x U hx (MvPolynomial.X t) :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (polynomialVariableCocone A E x) (op (⟨U, hx⟩ : OpenNhds x))) t

/-- The map on stalks induced by the coefficient inclusions `A ⟶ A(-)[E(-)]`. -/
def coefficientStalkHom :
    ToType (stalk A.obj x) →+*
      ToType (stalk (polynomialPresheaf (Opens.grothendieckTopology X) A E) x) :=
  ((stalkFunctor CommRingCat.{u} x).map
    (polynomialCoefficientMap (Opens.grothendieckTopology X) A E)).hom

/-- The composite of the germ map of `A` over `U` with `coefficientStalkHom` is the germ of the
constant polynomial. -/
theorem coefficientStalkHom_comp_germ (U : Opens X) (hx : x ∈ U) :
    (coefficientStalkHom A E x).comp (germ A.obj U x hx).hom =
      (polynomialGermHom A E x U hx).comp MvPolynomial.C :=
  congrArg CommRingCat.Hom.hom (stalkFunctor_map_germ U x hx
    (polynomialCoefficientMap (Opens.grothendieckTopology X) A E))

/-- `coefficientStalkHom` sends the germ of a section `r` of `A` to the germ of the constant
polynomial `r`. -/
theorem coefficientStalkHom_germ (U : Opens X) (hx : x ∈ U) (r : ToType (A.obj.obj (op U))) :
    coefficientStalkHom A E x ((germ A.obj U x hx).hom r) =
      polynomialGermHom A E x U hx (MvPolynomial.C r) :=
  DFunLike.congr_fun (coefficientStalkHom_comp_germ A E x U hx) r

/-- The homomorphism from the polynomial algebra `Aₓ[Eₓ]` on the stalks to the stalk of the
presheaf `U ↦ A(U)[E(U)]`, given by the germs of the coefficients and of the variables. -/
def polynomialStalkInv :
    MvPolynomial (E.stalk x) (ToType (stalk A.obj x)) →+*
      ToType (stalk (polynomialPresheaf (Opens.grothendieckTopology X) A E) x) :=
  MvPolynomial.eval₂Hom (coefficientStalkHom A E x) (polynomialVariableStalk A E x)

/-- `polynomialStalkInv` sends a constant polynomial to the image of its value under
`coefficientStalkHom`. -/
@[simp]
theorem polynomialStalkInv_C (a : ToType (stalk A.obj x)) :
    polynomialStalkInv A E x (MvPolynomial.C a) = coefficientStalkHom A E x a := by
  simp [polynomialStalkInv]

/-- `polynomialStalkInv` sends the variable indexed by `e` to `polynomialVariableStalk` of `e`. -/
@[simp]
theorem polynomialStalkInv_X (e : E.stalk x) :
    polynomialStalkInv A E x (MvPolynomial.X e) = polynomialVariableStalk A E x e := by
  simp [polynomialStalkInv]

/-- Evaluating a polynomial over `U` at germs and reading the result back into the stalk gives
the germ of that polynomial. -/
theorem polynomialStalkInv_comp_eval (U : Opens X) (hx : x ∈ U) :
    (polynomialStalkInv A E x).comp (polynomialStalkEval A E x U hx) =
      polynomialGermHom A E x U hx := by
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, polynomialStalkEval_C, polynomialStalkInv_C,
      coefficientStalkHom_germ]
  · intro t
    rw [RingHom.comp_apply, polynomialStalkEval_X, polynomialStalkInv_X,
      polynomialVariableStalk_germ]

/-- `polynomialStalkInv` followed by `polynomialStalkHom` is the identity of `Aₓ[Eₓ]`. -/
theorem polynomialStalkHom_comp_inv :
    (polynomialStalkHom A E x).comp (polynomialStalkInv A E x) =
      RingHom.id (MvPolynomial (E.stalk x) (ToType (stalk A.obj x))) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    obtain ⟨U, hx, r, rfl⟩ := exists_germ_eq A.obj a
    rw [RingHom.comp_apply, polynomialStalkInv_C, coefficientStalkHom_germ,
      polynomialStalkHom_germ, polynomialStalkEval_C, RingHom.id_apply]
  · intro e
    obtain ⟨U, hx, t, rfl⟩ := exists_germ_eq E e
    rw [RingHom.comp_apply, polynomialStalkInv_X, polynomialVariableStalk_germ,
      polynomialStalkHom_germ, polynomialStalkEval_X, RingHom.id_apply]

/-- `polynomialStalkHom` followed by `polynomialStalkInv` is the identity of the stalk of the
presheaf `U ↦ A(U)[E(U)]`. -/
theorem polynomialStalkInv_comp_hom :
    (polynomialStalkInv A E x).comp (polynomialStalkHom A E x) =
      RingHom.id
        (ToType (stalk (polynomialPresheaf (Opens.grothendieckTopology X) A E) x)) := by
  have key : colimit.desc _ (polynomialStalkCocone A E x) ≫
      CommRingCat.ofHom (polynomialStalkInv A E x) =
      𝟙 (stalk (polynomialPresheaf (Opens.grothendieckTopology X) A E) x) := by
    apply stalk_hom_ext
    intro U hxU
    have h1 : germ (polynomialPresheaf (Opens.grothendieckTopology X) A E) U x hxU ≫
        colimit.desc _ (polynomialStalkCocone A E x) ≫
          CommRingCat.ofHom (polynomialStalkInv A E x) =
        polynomialStalkEvalApp A E x U hxU ≫ CommRingCat.ofHom (polynomialStalkInv A E x) :=
      colimit.ι_desc_assoc (polynomialStalkCocone A E x) (op (⟨U, hxU⟩ : OpenNhds x)) _
    exact h1.trans ((congrArg CommRingCat.ofHom
      (polynomialStalkInv_comp_eval A E x U hxU)).trans (Category.comp_id _).symm)
  exact congrArg CommRingCat.Hom.hom key

/-- `polynomialStalkInv` is a left inverse of `polynomialStalkHom`. -/
theorem polynomialStalkInv_leftInverse :
    Function.LeftInverse (polynomialStalkInv A E x) (polynomialStalkHom A E x) :=
  fun ξ => DFunLike.congr_fun (polynomialStalkInv_comp_hom A E x) ξ

/-- `polynomialStalkInv` is a right inverse of `polynomialStalkHom`. -/
theorem polynomialStalkInv_rightInverse :
    Function.RightInverse (polynomialStalkInv A E x) (polynomialStalkHom A E x) :=
  fun p => DFunLike.congr_fun (polynomialStalkHom_comp_inv A E x) p

/-- **Forming a polynomial algebra commutes with stalks.** The stalk at `x` of the presheaf
`U ↦ A(U)[E(U)]` is the polynomial algebra `Aₓ[Eₓ]` on the stalk of `E` over the stalk of `A`. -/
def polynomialPresheafStalkRingEquiv :
    ToType (stalk (polynomialPresheaf (Opens.grothendieckTopology X) A E) x) ≃+*
      MvPolynomial (E.stalk x) (ToType (stalk A.obj x)) where
  toFun := polynomialStalkHom A E x
  invFun := polynomialStalkInv A E x
  left_inv := polynomialStalkInv_leftInverse A E x
  right_inv := polynomialStalkInv_rightInverse A E x
  map_mul' := map_mul _
  map_add' := map_add _

/-- The isomorphism `polynomialPresheafStalkRingEquiv` acts as `polynomialStalkHom`. -/
@[simp]
theorem polynomialPresheafStalkRingEquiv_apply
    (ξ : ToType (stalk (polynomialPresheaf (Opens.grothendieckTopology X) A E) x)) :
    polynomialPresheafStalkRingEquiv A E x ξ = polynomialStalkHom A E x ξ := rfl

/-- The inverse of `polynomialPresheafStalkRingEquiv` acts as `polynomialStalkInv`. -/
@[simp]
theorem polynomialPresheafStalkRingEquiv_symm_apply
    (p : MvPolynomial (E.stalk x) (ToType (stalk A.obj x))) :
    (polynomialPresheafStalkRingEquiv A E x).symm p = polynomialStalkInv A E x p := rfl

/-- The comparison map sends the image of `a` under `coefficientStalkHom` to the constant
polynomial `a`. -/
theorem polynomialStalkHom_coefficientStalkHom (a : ToType (stalk A.obj x)) :
    polynomialStalkHom A E x (coefficientStalkHom A E x a) = MvPolynomial.C a := by
  simpa using polynomialStalkInv_rightInverse A E x (MvPolynomial.C a)

/-- The comparison map sends the image of `e` under `polynomialVariableStalk` to the variable
indexed by `e`. -/
theorem polynomialStalkHom_polynomialVariableStalk (e : E.stalk x) :
    polynomialStalkHom A E x (polynomialVariableStalk A E x e) = MvPolynomial.X e := by
  simpa using polynomialStalkInv_rightInverse A E x (MvPolynomial.X e)

/-! ### The stalk of the free algebra sheaf -/

open TopCat.Presheaf.ExtensionByInitial in
/-- **The stalk of the free algebra sheaf is the polynomial algebra on the stalks.** For a sheaf
of commutative rings `A` and a presheaf of sets `E` on a topological space, the stalk at `x` of
the free `A`-algebra `A[E]` on `E` is `Aₓ[Eₓ]`. -/
def freeAlgebraSheafStalkRingEquiv :
    ToType (stalk (freeAlgebraSheaf (Opens.grothendieckTopology X) A E).obj x) ≃+*
      MvPolynomial (E.stalk x) (ToType (stalk A.obj x)) :=
  ((stalkSheafifyIso (polynomialPresheaf (Opens.grothendieckTopology X) A E)
    x).symm.commRingCatIsoToRingEquiv).trans (polynomialPresheafStalkRingEquiv A E x)

/-- The isomorphism `(A[E])ₓ ≅ Aₓ[Eₓ]`, as an isomorphism in `CommRingCat`. -/
def freeAlgebraSheafStalkIso :
    stalk (freeAlgebraSheaf (Opens.grothendieckTopology X) A E).obj x ≅
      CommRingCat.of (MvPolynomial (E.stalk x) (ToType (stalk A.obj x))) :=
  (freeAlgebraSheafStalkRingEquiv A E x).toCommRingCatIso

open TopCat.Presheaf.ExtensionByInitial in
/-- On the image of the stalk of the presheaf `U ↦ A(U)[E(U)]` under the unit of sheafification,
the isomorphism is the comparison map. -/
theorem freeAlgebraSheafStalkRingEquiv_sheafify
    (ξ : ToType (stalk (polynomialPresheaf (Opens.grothendieckTopology X) A E) x)) :
    freeAlgebraSheafStalkRingEquiv A E x
        ((stalkSheafifyIso (polynomialPresheaf (Opens.grothendieckTopology X) A E) x).hom.hom ξ) =
      polynomialStalkHom A E x ξ := by
  show polynomialStalkHom A E x
      ((stalkSheafifyIso (polynomialPresheaf (Opens.grothendieckTopology X) A E) x).inv.hom
        ((stalkSheafifyIso (polynomialPresheaf (Opens.grothendieckTopology X) A E) x).hom.hom ξ)) =
    polynomialStalkHom A E x ξ
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

open TopCat.Presheaf.ExtensionByInitial in
/-- The composite of the stalk of the structural morphism `A ⟶ A[E]` with the isomorphism
`(A[E])ₓ ≅ Aₓ[Eₓ]` is the coefficient inclusion. -/
theorem freeAlgebraSheafStalkRingEquiv_coefficientMap (a : ToType (stalk A.obj x)) :
    freeAlgebraSheafStalkRingEquiv A E x
        (((stalkFunctor CommRingCat.{u} x).map
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E).hom).hom a) =
      MvPolynomial.C a := by
  have hmap : (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E).hom =
      polynomialCoefficientMap (Opens.grothendieckTopology X) A E ≫
        (toSheafification (Opens.grothendieckTopology X) CommRingCat.{u}).app
          (polynomialPresheaf (Opens.grothendieckTopology X) A E) := rfl
  have h0 : ((stalkFunctor CommRingCat.{u} x).map
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E).hom).hom a =
      (stalkSheafifyIso (polynomialPresheaf (Opens.grothendieckTopology X) A E) x).hom.hom
        (coefficientStalkHom A E x a) := by
    rw [hmap]
    exact ConcreteCategory.congr_hom
      ((stalkFunctor CommRingCat.{u} x).map_comp
        (polynomialCoefficientMap (Opens.grothendieckTopology X) A E)
        ((toSheafification (Opens.grothendieckTopology X) CommRingCat.{u}).app
          (polynomialPresheaf (Opens.grothendieckTopology X) A E))) a
  rw [h0, freeAlgebraSheafStalkRingEquiv_sheafify, polynomialStalkHom_coefficientStalkHom]

open TopCat.Presheaf.ExtensionByInitial in
/-- The isomorphism `(A[E])ₓ ≅ Aₓ[Eₓ]` carries the germ at `x` of the variable attached to a
section `t` of `E` to the variable indexed by the germ of `t`. -/
theorem freeAlgebraSheafStalkRingEquiv_variable (U : Opens X) (hx : x ∈ U) (t : E.obj (op U)) :
    freeAlgebraSheafStalkRingEquiv A E x
        ((germ (freeAlgebraSheaf (Opens.grothendieckTopology X) A E).obj U x hx).hom
          ((freeAlgebraSheafVariable (Opens.grothendieckTopology X) A E).app (op U) t)) =
      MvPolynomial.X ((E.germ U x hx).hom t) := by
  have h0 : (germ (freeAlgebraSheaf (Opens.grothendieckTopology X) A E).obj U x hx).hom
        ((freeAlgebraSheafVariable (Opens.grothendieckTopology X) A E).app (op U) t) =
      (stalkSheafifyIso (polynomialPresheaf (Opens.grothendieckTopology X) A E) x).hom.hom
        (polynomialGermHom A E x U hx (MvPolynomial.X t)) :=
    (stalkFunctor_map_germ_apply U x hx
      ((toSheafification (Opens.grothendieckTopology X) CommRingCat.{u}).app
        (polynomialPresheaf (Opens.grothendieckTopology X) A E)) (MvPolynomial.X t)).symm
  rw [h0, freeAlgebraSheafStalkRingEquiv_sheafify, polynomialStalkHom_germ,
    polynomialStalkEval_X]

end Stacks.Sites.FreeAlgebra

end

end
