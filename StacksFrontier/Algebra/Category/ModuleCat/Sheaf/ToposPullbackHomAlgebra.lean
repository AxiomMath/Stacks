module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback

/-! # Generalized elements of a sheaf of rings, and their inverse images

Let `(C, J)` be a site, `R` a sheaf of rings on it and `M` a sheaf of `R`-modules.  For a sheaf
of sets `Z` on `C`, a *generalized element* of `R` of shape `Z` is a morphism of sheaves of sets
`Z ⟶ ringSheaf R`, and a generalized element of `M` of shape `Z` is a morphism
`Z ⟶ moduleSheaf R M`.  Because the ring and module operations of `R` and `M` are morphisms of
sheaves of sets (`CategoryTheory.Sheaf.ringAddHom`, `moduleSMulHom`, …), the generalized elements
of shape `Z` form a ring, respectively a module over it: this is the structure already
constructed in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback` for an arbitrary
finite-product-preserving functor to types, applied to `coyoneda.obj (op Z)`.

This file records that structure as an instance, identifies its operations with the evident
composites, and proves the two transport statements the file exists for:

* **evaluation**: applying any finite-product-preserving functor `Q` to types and evaluating at a
  fixed element of `Q.obj Z` is a ring homomorphism, respectively semilinear, onto the structures
  transported along `Q`;
* **inverse image**: for a finite-product-preserving `Φ` between categories of sheaves of sets,
  `Φ.map` followed by precomposition with any morphism is a ring homomorphism, respectively
  semilinear, onto the generalized elements of the *inverse-image* sheaf of rings and module of
  Stacks 03D2.

Together these say that a polynomial identity between generalized elements of `R` and `M`
survives the inverse image, which is what lets a first-order condition on sections — a relation
among sections, a factorization of sections through a finite free module — be transported along a
morphism of topoi, where no description of `f⁻¹` on sections is available.

An auxiliary half of the file extends the binary element calculus of
`CategoryTheory.Functor.prodObjMk` to products indexed by an arbitrary finite type, which is what
a relation or a factorization of a *fixed finite number* of sections is cut out of.

## Main definitions

* `CategoryTheory.Functor.piObjEquiv` and `CategoryTheory.Functor.piObjMk`: for a functor `P` to
  types preserving finite products, the elements of `P (∏ᵢ Aᵢ)` are the families of elements of
  the `P Aᵢ`.
* `CategoryTheory.Sheaf.homRing`, `homAddCommGroup`, `homModule`: the ring of generalized elements
  of a sheaf of rings and the module of generalized elements of a sheaf of modules.
* `CategoryTheory.Sheaf.evalAddHom`: evaluation of a generalized element of a sheaf of modules
  along a finite-product-preserving functor to types, as an additive map.
* `Stacks.Sheaves.ToposPullback.inverseImageAddHom`: the inverse image of a generalized element of
  a sheaf of modules, precomposed with a fixed morphism, as an additive map.

## Main results

* `CategoryTheory.Sheaf.map_hom_add`, `map_hom_mul`, `map_hom_one`, `map_hom_ringZero`,
  `map_hom_moduleAdd`, `map_hom_moduleZero`, `map_hom_smul`: the evaluation statements.
* `CategoryTheory.Sheaf.hom_mul_comm`: generalized elements of a sheaf of rings with commuting
  sections commute; `ringMulHom_comm` and `ringMulObj_comm`: the same commutativity read as an
  identity of morphisms and then transported along a finite-product-preserving functor.
* `CategoryTheory.Sheaf.comp_hom_add`, `comp_hom_mul`, `comp_hom_ringZero`,
  `comp_hom_moduleAdd`, `comp_hom_moduleZero`, `comp_hom_smul`, `comp_hom_sum`: the same for
  precomposition with a fixed morphism, which is the evaluation statement at
  `Q = coyoneda.obj (op Z')`.
* `Stacks.Sheaves.ToposPullback.comp_map_prodLift` and `comp_map_terminalFrom`: the two shapes
  the inverse-image statements are instances of.
* `Stacks.Sheaves.ToposPullback.inverseImageRingElt_add`, `inverseImageRingElt_mul`,
  `inverseImageRingElt_one`, `inverseImageRingElt_zero`, `inverseImageModuleElt_add`,
  `inverseImageModuleElt_zero`, `inverseImageModuleElt_smul`: the inverse-image statements.
* `Stacks.Sheaves.ToposPullback.inverseImageModuleElt_sum` and
  `CategoryTheory.Sheaf.map_hom_sum`: the
  corresponding statements for a finite sum, which is the form a contraction `∑ᵢ aᵢ • sᵢ` is used
  in.

## Implementation notes

**The ring and module structures are instances here, and are `def`s upstream.**
`CategoryTheory.Sheaf.ringObjRing` and `moduleObjModule` are deliberately `def`s, because they
are stated for an arbitrary `P` and as instances would slow down instance search everywhere.  At the specific
`P = coyoneda.obj (op Z)` the carrier is a `Hom` type of a category of sheaves of sets, which no
other instance in the tree claims, so registering them is safe and removes a `letI` from every
statement below.

**Every operation lemma is proved by unfolding, not by rewriting.**  `ringAddObj` and its
companions are *defined* as `P.map (op) (prodObjMk x y)`, and for `P = coyoneda.obj (op Z)` the
functor acts by postcomposition, so `coyoneda_prodObjMk` turns the definition into the composite
with `Limits.prod.lift` on the nose.  The statements below are therefore `rfl` after that single
rewrite, and no transparency lever is needed anywhere in this file.

**The inverse-image statements are stated with a precomposition built in.**  The use site needs
`c ≫ Φ.map h` for `c` a comparison isomorphism out of a product of inverse images, never
`Φ.map h` alone, and the combined statement is no harder: precomposition is handled by
`Limits.prod.comp_lift`, which is also what makes the proofs uniform.  The inverse-image
structure sheaf is spelled `ringSheaf (pullbackRingSheaf J Φ R)` rather than
`Φ.obj (ringSheaf R)`; the two are equal by `rfl` (this was checked before anything here was
written), and only the first spelling lets instance search find the generalized-element ring of
the inverse image.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w v u

namespace CategoryTheory.Functor

variable {D : Type u} [Category.{v} D] [HasFiniteProducts D]

section

variable (P : D ⥤ Type t) [PreservesFiniteProducts P]

/-- For a functor `P` to types preserving finite products, an element of `P (∏ᵢ Aᵢ)` is the same
thing as a family of elements of the `P Aᵢ`.  This is the finitely-indexed analogue of
`CategoryTheory.Functor.prodObjEquiv`. -/
def piObjEquiv {ι : Type} [Finite ι] (A : ι → D) :
    P.obj (∏ᶜ A) ≃ (∀ i, P.obj (A i)) :=
  (PreservesProduct.iso P A).toEquiv.trans (Types.productIso (fun i => P.obj (A i))).toEquiv

/-- The `i`-th component of `piObjEquiv P A x` is the image of `x` under the `i`-th projection. -/
@[simp]
lemma piObjEquiv_apply {ι : Type} [Finite ι] (A : ι → D) (x : P.obj (∏ᶜ A)) (i : ι) :
    piObjEquiv P A x i = P.map (Pi.π A i) x := by
  have h2 := ConcreteCategory.congr_hom (Types.productIso_hom_comp_eval
    (fun i => P.obj (A i)) i) ((PreservesProduct.iso P A).hom x)
  have h3 := ConcreteCategory.congr_hom (piComparison_comp_π P A i) x
  rw [types_comp_apply] at h2 h3
  simp only [piObjEquiv, Equiv.trans_apply, Iso.toEquiv_fun, PreservesProduct.iso_hom] at *
  exact h2.trans h3

end

variable {P : D ⥤ Type t} [PreservesFiniteProducts P]

/-- The element of `P (∏ᵢ Aᵢ)` determined by a family of elements of the `P Aᵢ`. -/
def piObjMk {ι : Type} [Finite ι] {A : ι → D} (a : ∀ i, P.obj (A i)) : P.obj (∏ᶜ A) :=
  (piObjEquiv P A).symm a

/-- The `i`-th projection of `piObjMk a` is `a i`. -/
@[simp]
lemma map_piπ_piObjMk {ι : Type} [Finite ι] {A : ι → D} (a : ∀ i, P.obj (A i)) (i : ι) :
    P.map (Pi.π A i) (piObjMk a) = a i := by
  rw [← piObjEquiv_apply, piObjMk, Equiv.apply_symm_apply]

/-- Two elements of `P (∏ᵢ Aᵢ)` with the same components agree. -/
lemma piObjMk_ext {ι : Type} [Finite ι] {A : ι → D} {x y : P.obj (∏ᶜ A)}
    (h : ∀ i, P.map (Pi.π A i) x = P.map (Pi.π A i) y) : x = y :=
  (piObjEquiv P A).injective (funext fun i => by simpa using h i)

/-- An element of `P (∏ᵢ Aᵢ)` is the element determined by its components. -/
@[simp]
lemma piObjMk_map_piπ {ι : Type} [Finite ι] {A : ι → D} (x : P.obj (∏ᶜ A)) :
    piObjMk (fun i => P.map (Pi.π A i) x) = x :=
  piObjMk_ext (by simp)

/-- The image under `P` of a morphism into a finite product, computed on elements. -/
@[simp]
lemma map_piLift_apply {ι : Type} [Finite ι] {Z : D} {A : ι → D} (g : ∀ i, Z ⟶ A i)
    (z : P.obj Z) : P.map (Pi.lift g) z = piObjMk (fun i => P.map (g i) z) :=
  piObjMk_ext (fun i => by rw [map_piπ_piObjMk, ← P.map_comp_apply, Pi.lift_comp_π])

/-- The product comparison of a functor `Ψ` for a finite product, computed on elements after
applying a finite-product-preserving functor `P` to types. -/
@[simp]
lemma map_piComparison_apply {B : Type*} [Category B] [HasFiniteProducts B] (Ψ : B ⥤ D)
    [PreservesFiniteProducts (Ψ ⋙ P)] {ι : Type} [Finite ι] (A : ι → B)
    (p : P.obj (Ψ.obj (∏ᶜ A))) :
    P.map (Limits.piComparison Ψ A) p =
      piObjMk (P := P) (A := fun i => Ψ.obj (A i)) (fun i => (Ψ ⋙ P).map (Pi.π A i) p) :=
  piObjMk_ext (fun i => by
    rw [map_piπ_piObjMk, ← P.map_comp_apply, Limits.piComparison_comp_π]; rfl)

/-- A natural transformation of finite-product-preserving functors to types commutes with the
element calculus of a finite product. -/
lemma piObjMk_naturality {Q : D ⥤ Type t} [PreservesFiniteProducts Q] (θ : P ⟶ Q)
    {ι : Type} [Finite ι] {A : ι → D} (a : ∀ i, P.obj (A i)) :
    θ.app (∏ᶜ A) (piObjMk a) = piObjMk (fun i => θ.app (A i) (a i)) :=
  piObjMk_ext (fun i => by
    rw [map_piπ_piObjMk, ← types_comp_apply (θ.app _) (Q.map _), ← θ.naturality,
      types_comp_apply, map_piπ_piObjMk])

end CategoryTheory.Functor

/-! ## Generalized elements of a sheaf of rings and of a sheaf of modules -/

namespace CategoryTheory.Sheaf

open CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The element of `(Z ⟶ A ⨯ B)` determined by a pair of morphisms is their lift. -/
lemma coyoneda_prodObjMk {A B Z : Sheaf J (Type w)} (a : Z ⟶ A) (b : Z ⟶ B) :
    prodObjMk (P := coyoneda.obj (op Z)) a b = Limits.prod.lift a b :=
  prodObjMk_ext (by rw [map_fst_prodObjMk]; exact (Limits.prod.lift_fst a b).symm)
    (by rw [map_snd_prodObjMk]; exact (Limits.prod.lift_snd a b).symm)

/-- The element of `(Z ⟶ ∏ᵢ Aᵢ)` determined by a family of morphisms is their lift. -/
lemma coyoneda_piObjMk {ι : Type} [Finite ι] {A : ι → Sheaf J (Type w)} {Z : Sheaf J (Type w)}
    (g : ∀ i, Z ⟶ A i) : piObjMk (P := coyoneda.obj (op Z)) g = Limits.Pi.lift g :=
  piObjMk_ext (fun i => by rw [map_piπ_piObjMk]; exact (Limits.Pi.lift_comp_π g i).symm)

/-- The unique morphism to the terminal sheaf is the distinguished element of the singleton
`(Z ⟶ ⊤)`. -/
lemma coyoneda_default {Z : Sheaf J (Type w)} :
    (default : (coyoneda.obj (op Z)).obj (⊤_ (Sheaf J (Type w)))) = Limits.terminal.from Z :=
  Subsingleton.elim _ _

/-- Evaluating a morphism that factors through the terminal sheaf only sees the factor. -/
private lemma map_terminalFrom_comp_apply {Z E : Sheaf J (Type w)} (Q : Sheaf J (Type w) ⥤ Type t)
    [PreservesFiniteProducts Q] (f : (⊤_ (Sheaf J (Type w))) ⟶ E) (z : Q.obj Z) :
    Q.map (Limits.terminal.from Z ≫ f) z = Q.map f default := by
  rw [Q.map_comp_apply]
  exact congrArg (Q.map f) (Subsingleton.elim _ _)

/-- Inverse image of a binary operation precomposed with `c`, given its transport along the
product comparison. -/
private lemma comp_map_prodLift_comp {D : Type*} [Category* D] {K : GrothendieckTopology D}
    (Φ : Sheaf K (Type t) ⥤ Sheaf J (Type w)) {Z A B F : Sheaf K (Type t)} {W : Sheaf J (Type w)}
    (c : W ⟶ Φ.obj Z) (a : Z ⟶ A) (b : Z ⟶ B) (f : A ⨯ B ⟶ F) (m : Φ.obj A ⨯ Φ.obj B ⟶ Φ.obj F)
    (h : Φ.map f = Limits.prodComparison Φ A B ≫ m) :
    c ≫ Φ.map (Limits.prod.lift a b ≫ f) = Limits.prod.lift (c ≫ Φ.map a) (c ≫ Φ.map b) ≫ m := by
  have : Φ.map (Limits.prod.lift a b) ≫ Limits.prodComparison Φ A B =
      Limits.prod.lift (Φ.map a) (Φ.map b) :=
    Limits.prod.hom_ext (by simp [← Φ.map_comp]) (by simp [← Φ.map_comp])
  rw [Φ.map_comp, h, ← Category.assoc (Φ.map _), this, ← Category.assoc, Limits.prod.comp_lift]

/-- Inverse image of a nullary operation precomposed with `c`, given its transport along the
terminal comparison. -/
private lemma comp_map_terminalFrom_comp {D : Type*} [Category* D] {K : GrothendieckTopology D}
    (Φ : Sheaf K (Type t) ⥤ Sheaf J (Type w)) {Z F : Sheaf K (Type t)} {W : Sheaf J (Type w)}
    (c : W ⟶ Φ.obj Z) (f : (⊤_ (Sheaf K (Type t))) ⟶ F) (m : (⊤_ (Sheaf J (Type w))) ⟶ Φ.obj F)
    (h : Φ.map f = Limits.terminalComparison Φ ≫ m) :
    c ≫ Φ.map (Limits.terminal.from Z ≫ f) = Limits.terminal.from W ≫ m := by
  rw [Φ.map_comp, h, ← Category.assoc (Φ.map _), ← Category.assoc]
  congr 1
  exact Limits.terminal.hom_ext _ _

section Structures

variable [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- The generalized elements of a sheaf of rings of a fixed shape form a ring: the ring
operations of `R` are morphisms of sheaves of sets, so they act on morphisms into the underlying
sheaf of sets of `R`. -/
instance homRing (R : Sheaf J RingCat.{w}) (Z : Sheaf J (Type w)) : Ring (Z ⟶ ringSheaf R) :=
  ringObjRing R (coyoneda.obj (op Z))

/-- The generalized elements of a sheaf of modules of a fixed shape form an additive commutative
group. -/
instance homAddCommGroup {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R)
    (Z : Sheaf J (Type w)) : AddCommGroup (Z ⟶ moduleSheaf R M) :=
  moduleObjAddCommGroup R M (coyoneda.obj (op Z))

/-- The generalized elements of a sheaf of modules of a fixed shape form a module over the
generalized elements of the sheaf of rings of the same shape. -/
instance homModule {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R) (Z : Sheaf J (Type w)) :
    Module (Z ⟶ ringSheaf R) (Z ⟶ moduleSheaf R M) :=
  moduleObjModule R M (coyoneda.obj (op Z))

variable {R : Sheaf J RingCat.{w}} {M : SheafOfModules.{w} R} {Z : Sheaf J (Type w)}

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The sum of two generalized elements of a sheaf of rings is their lift composed with the
addition morphism. -/
lemma hom_add_eq (a b : Z ⟶ ringSheaf R) : a + b = Limits.prod.lift a b ≫ ringAddHom R := by
  rw [← coyoneda_prodObjMk]
  rfl

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The product of two generalized elements of a sheaf of rings is their lift composed with the
multiplication morphism. -/
lemma hom_mul_eq (a b : Z ⟶ ringSheaf R) : a * b = Limits.prod.lift a b ≫ ringMulHom R := by
  rw [← coyoneda_prodObjMk]
  rfl

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The negative of a generalized element of a sheaf of rings is its composite with the negation
morphism. -/
lemma hom_neg_eq (a : Z ⟶ ringSheaf R) : -a = a ≫ ringNegHom R := rfl

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The zero generalized element of a sheaf of rings factors through the terminal sheaf via the
zero morphism. -/
lemma hom_ringZero_eq : (0 : Z ⟶ ringSheaf R) = Limits.terminal.from Z ≫ ringZeroHom R := by
  rw [← coyoneda_default]
  rfl

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The unit generalized element of a sheaf of rings factors through the terminal sheaf via the
unit morphism. -/
lemma hom_one_eq : (1 : Z ⟶ ringSheaf R) = Limits.terminal.from Z ≫ ringOneHom R := by
  rw [← coyoneda_default]
  rfl

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The sum of two generalized elements of a sheaf of modules is their lift composed with the
addition morphism. -/
lemma hom_moduleAdd_eq (x y : Z ⟶ moduleSheaf R M) :
    x + y = Limits.prod.lift x y ≫ moduleAddHom R M := by
  rw [← coyoneda_prodObjMk]
  rfl

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The zero generalized element of a sheaf of modules factors through the terminal sheaf via
the zero morphism. -/
lemma hom_moduleZero_eq :
    (0 : Z ⟶ moduleSheaf R M) = Limits.terminal.from Z ≫ moduleZeroHom R M := by
  rw [← coyoneda_default]
  rfl

/-- The scalar multiple of a generalized element of a sheaf of modules is the lift of the pair
composed with the scalar multiplication morphism. -/
lemma hom_smul_eq (r : Z ⟶ ringSheaf R) (x : Z ⟶ moduleSheaf R M) :
    r • x = Limits.prod.lift r x ≫ moduleSMulHom R M := by
  rw [← coyoneda_prodObjMk]
  rfl

end Structures

/-! ### Evaluating a generalized element along a finite-product-preserving functor -/

section Evaluation

variable [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {R : Sheaf J RingCat.{w}} {M : SheafOfModules.{w} R} {Z : Sheaf J (Type w)}
  (Q : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteProducts Q]

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Evaluating a sum of generalized elements of a sheaf of rings along `Q` is the transported
addition of the evaluations. -/
lemma map_hom_add (a b : Z ⟶ ringSheaf R) (z : Q.obj Z) :
    Q.map (a + b) z = ringAddObj R Q (Q.map a z) (Q.map b z) := by
  rw [hom_add_eq, Q.map_comp_apply, Functor.map_lift_apply, ringAddObj]

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Evaluating a product of generalized elements of a sheaf of rings along `Q` is the
transported multiplication of the evaluations. -/
lemma map_hom_mul (a b : Z ⟶ ringSheaf R) (z : Q.obj Z) :
    Q.map (a * b) z = ringMulObj R Q (Q.map a z) (Q.map b z) := by
  rw [hom_mul_eq, Q.map_comp_apply, Functor.map_lift_apply, ringMulObj]

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Evaluating the zero generalized element of a sheaf of rings along `Q` gives the transported
zero. -/
lemma map_hom_ringZero (z : Q.obj Z) :
    Q.map (0 : Z ⟶ ringSheaf R) z = ringZeroObj R Q := by
  rw [hom_ringZero_eq, map_terminalFrom_comp_apply Q, ringZeroObj]

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Evaluating the unit generalized element of a sheaf of rings along `Q` gives the transported
unit. -/
lemma map_hom_one (z : Q.obj Z) : Q.map (1 : Z ⟶ ringSheaf R) z = ringOneObj R Q := by
  rw [hom_one_eq, map_terminalFrom_comp_apply Q, ringOneObj]

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- Evaluating a sum of generalized elements of a sheaf of modules along `Q` is the transported
addition of the evaluations. -/
lemma map_hom_moduleAdd (x y : Z ⟶ moduleSheaf R M) (z : Q.obj Z) :
    Q.map (x + y) z = moduleAddObj R M Q (Q.map x z) (Q.map y z) := by
  rw [hom_moduleAdd_eq, Q.map_comp_apply, Functor.map_lift_apply, moduleAddObj]

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- Evaluating the zero generalized element of a sheaf of modules along `Q` gives the
transported zero. -/
lemma map_hom_moduleZero (z : Q.obj Z) :
    Q.map (0 : Z ⟶ moduleSheaf R M) z = moduleZeroObj R M Q := by
  rw [hom_moduleZero_eq, map_terminalFrom_comp_apply Q, moduleZeroObj]

/-- Evaluating a scalar multiple of a generalized element of a sheaf of modules along `Q` is the
transported scalar multiplication of the evaluations. -/
lemma map_hom_smul (r : Z ⟶ ringSheaf R) (x : Z ⟶ moduleSheaf R M) (z : Q.obj Z) :
    Q.map (r • x) z = moduleSMulObj R M Q (Q.map r z) (Q.map x z) := by
  rw [hom_smul_eq, Q.map_comp_apply, Functor.map_lift_apply, moduleSMulObj]

/-- Evaluating a generalized element of a sheaf of modules along a finite-product-preserving
functor to types, as an additive map onto the transported additive group. -/
def evalAddHom (z : Q.obj Z) :
    letI := moduleObjAddCommGroup R M Q
    (Z ⟶ moduleSheaf R M) →+ Q.obj (moduleSheaf R M) :=
  letI := moduleObjAddCommGroup R M Q
  { toFun := fun x => Q.map x z
    map_zero' := map_hom_moduleZero Q z
    map_add' := fun x y => map_hom_moduleAdd Q x y z }

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- Evaluation along a finite-product-preserving functor to types commutes with a finite sum of
generalized elements of a sheaf of modules. -/
lemma map_hom_sum {ι : Type*} (s : Finset ι) (c : ι → (Z ⟶ moduleSheaf R M)) (z : Q.obj Z) :
    letI := moduleObjAddCommGroup R M Q
    Q.map (∑ i ∈ s, c i) z = ∑ i ∈ s, Q.map (c i) z :=
  let := moduleObjAddCommGroup R M Q
  map_sum (evalAddHom Q z) c s

/-- Evaluating a generalized element of a sheaf of rings along a finite-product-preserving
functor to types, as an additive map onto the transported additive group. -/
def evalRingAddHom (z : Q.obj Z) :
    letI := ringObjRing R Q
    (Z ⟶ ringSheaf R) →+ Q.obj (ringSheaf R) :=
  letI := ringObjRing R Q
  { toFun := fun a => Q.map a z
    map_zero' := map_hom_ringZero Q z
    map_add' := fun a b => map_hom_add Q a b z }

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Evaluation along a finite-product-preserving functor to types commutes with a finite sum of
generalized elements of a sheaf of rings. -/
lemma map_hom_ringSum {ι : Type*} (s : Finset ι) (c : ι → (Z ⟶ ringSheaf R)) (z : Q.obj Z) :
    letI := ringObjRing R Q
    Q.map (∑ i ∈ s, c i) z = ∑ i ∈ s, Q.map (c i) z :=
  let := ringObjRing R Q
  map_sum (evalRingAddHom Q z) c s

end Evaluation

/-! ### Precomposing a generalized element with a morphism -/

section Precomposition

variable [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {R : Sheaf J RingCat.{w}} {M : SheafOfModules.{w} R} {Z Z' : Sheaf J (Type w)}

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Precomposition with a fixed morphism is additive on generalized elements of a sheaf of
rings.  This is the evaluation statement for `Q = coyoneda.obj (op Z')`. -/
lemma comp_hom_add (g : Z' ⟶ Z) (a b : Z ⟶ ringSheaf R) : g ≫ (a + b) = g ≫ a + g ≫ b :=
  map_hom_add (coyoneda.obj (op Z')) a b g

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Precomposition with a fixed morphism is multiplicative on generalized elements of a sheaf of
rings. -/
lemma comp_hom_mul (g : Z' ⟶ Z) (a b : Z ⟶ ringSheaf R) : g ≫ (a * b) = (g ≫ a) * (g ≫ b) :=
  map_hom_mul (coyoneda.obj (op Z')) a b g

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Precomposition with a fixed morphism kills the zero generalized element of a sheaf of
rings. -/
lemma comp_hom_ringZero (g : Z' ⟶ Z) : g ≫ (0 : Z ⟶ ringSheaf R) = 0 :=
  map_hom_ringZero (coyoneda.obj (op Z')) g

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- Precomposition with a fixed morphism is additive on generalized elements of a sheaf of
modules. -/
lemma comp_hom_moduleAdd (g : Z' ⟶ Z) (x y : Z ⟶ moduleSheaf R M) :
    g ≫ (x + y) = g ≫ x + g ≫ y :=
  map_hom_moduleAdd (coyoneda.obj (op Z')) x y g

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- Precomposition with a fixed morphism kills the zero generalized element of a sheaf of
modules.  This is the form in which the zero morphism of the equalizer presentation of the sheaf
of relations is manipulated: `Sheaf J (Type w)` has no zero morphisms, so
`CategoryTheory.Limits.comp_zero` does not apply to this zero. -/
lemma comp_hom_moduleZero (g : Z' ⟶ Z) : g ≫ (0 : Z ⟶ moduleSheaf R M) = 0 :=
  map_hom_moduleZero (coyoneda.obj (op Z')) g

/-- Precomposition with a fixed morphism is compatible with the scalar action on generalized
elements. -/
lemma comp_hom_smul (g : Z' ⟶ Z) (r : Z ⟶ ringSheaf R) (x : Z ⟶ moduleSheaf R M) :
    g ≫ (r • x) = (g ≫ r) • (g ≫ x) :=
  map_hom_smul (coyoneda.obj (op Z')) r x g

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- Precomposition with a fixed morphism commutes with a finite sum of generalized elements of a
sheaf of modules. -/
lemma comp_hom_sum {ι : Type*} (s : Finset ι) (g : Z' ⟶ Z)
    (c : ι → (Z ⟶ moduleSheaf R M)) : g ≫ (∑ i ∈ s, c i) = ∑ i ∈ s, g ≫ c i :=
  map_hom_sum (coyoneda.obj (op Z')) s c g

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Precomposition with a fixed morphism commutes with a finite sum of generalized elements of a
sheaf of rings. -/
lemma comp_hom_ringSum {ι : Type*} (s : Finset ι) (g : Z' ⟶ Z)
    (c : ι → (Z ⟶ ringSheaf R)) : g ≫ (∑ i ∈ s, c i) = ∑ i ∈ s, g ≫ c i :=
  map_hom_ringSum (coyoneda.obj (op Z')) s c g

end Precomposition

/-! ### Evaluating a generalized element on sections -/

section Sections

variable [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {R : Sheaf J RingCat.{w}} {M : SheafOfModules.{w} R} {Z : Sheaf J (Type w)} (X : Cᵒᵖ)

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- On sections, a sum of generalized elements of a sheaf of rings acts as the sum of their
values. -/
lemma sectionsFunctor_map_hom_add (a b : Z ⟶ ringSheaf R) (z : (sectionsFunctor J X).obj Z) :
    (sectionsFunctor J X).map (a + b) z =
      (sectionsFunctor J X).map a z + (sectionsFunctor J X).map b z :=
  (map_hom_add (sectionsFunctor J X) a b z).trans
    (sectionsFunctor_map_ringAddHom R X _ _)

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- On sections, a product of generalized elements of a sheaf of rings acts as the product of
their values. -/
lemma sectionsFunctor_map_hom_mul (a b : Z ⟶ ringSheaf R) (z : (sectionsFunctor J X).obj Z) :
    (sectionsFunctor J X).map (a * b) z =
      (sectionsFunctor J X).map a z * (sectionsFunctor J X).map b z :=
  (map_hom_mul (sectionsFunctor J X) a b z).trans
    (sectionsFunctor_map_ringMulHom R X _ _)

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- On sections, the zero generalized element of a sheaf of rings takes the value zero. -/
lemma sectionsFunctor_map_hom_ringZero (z : (sectionsFunctor J X).obj Z) :
    (sectionsFunctor J X).map (0 : Z ⟶ ringSheaf R) z = 0 :=
  (map_hom_ringZero (sectionsFunctor J X) z).trans (sectionsFunctor_map_ringZeroHom R X _)

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- On sections, a sum of generalized elements of a sheaf of modules acts as the sum of their
values. -/
lemma sectionsFunctor_map_hom_moduleAdd (x y : Z ⟶ moduleSheaf R M)
    (z : (sectionsFunctor J X).obj Z) :
    (sectionsFunctor J X).map (x + y) z =
      (sectionsFunctor J X).map x z + (sectionsFunctor J X).map y z :=
  (map_hom_moduleAdd (sectionsFunctor J X) x y z).trans
    (sectionsFunctor_map_moduleAddHom R M X _ _)

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- On sections, the zero generalized element of a sheaf of modules takes the value zero. -/
lemma sectionsFunctor_map_hom_moduleZero (z : (sectionsFunctor J X).obj Z) :
    (sectionsFunctor J X).map (0 : Z ⟶ moduleSheaf R M) z = 0 :=
  (map_hom_moduleZero (sectionsFunctor J X) z).trans
    (sectionsFunctor_map_moduleZeroHom R M X _)

/-- On sections, a scalar multiple of generalized elements acts as the scalar multiple of their
values. -/
lemma sectionsFunctor_map_hom_smul (r : Z ⟶ ringSheaf R) (x : Z ⟶ moduleSheaf R M)
    (z : (sectionsFunctor J X).obj Z) :
    (sectionsFunctor J X).map (r • x) z =
      (sectionsFunctor J X).map r z • (sectionsFunctor J X).map x z :=
  (map_hom_smul (sectionsFunctor J X) r x z).trans
    (sectionsFunctor_map_moduleSMulHom R M X _ _)

/-- Evaluation on sections of a generalized element of a sheaf of modules, as an additive map. -/
def sectionsEvalAddHom (z : (sectionsFunctor J X).obj Z) :
    (Z ⟶ moduleSheaf R M) →+ (sectionsFunctor J X).obj (moduleSheaf R M) where
  toFun x := (sectionsFunctor J X).map x z
  map_zero' := sectionsFunctor_map_hom_moduleZero X z
  map_add' x y := sectionsFunctor_map_hom_moduleAdd X x y z

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- On sections, a finite sum of generalized elements of a sheaf of modules acts as the sum of
their values. -/
lemma sectionsFunctor_map_hom_sum {ι : Type*} (s : Finset ι) (c : ι → (Z ⟶ moduleSheaf R M))
    (z : (sectionsFunctor J X).obj Z) :
    (sectionsFunctor J X).map (∑ i ∈ s, c i) z = ∑ i ∈ s, (sectionsFunctor J X).map (c i) z :=
  map_sum (sectionsEvalAddHom X z) c s

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Evaluation on sections of a generalized element of a sheaf of rings, as an additive map. -/
def sectionsEvalRingAddHom (z : (sectionsFunctor J X).obj Z) :
    (Z ⟶ ringSheaf R) →+ (sectionsFunctor J X).obj (ringSheaf R) where
  toFun a := (sectionsFunctor J X).map a z
  map_zero' := sectionsFunctor_map_hom_ringZero X z
  map_add' a b := sectionsFunctor_map_hom_add X a b z

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- On sections, a finite sum of generalized elements of a sheaf of rings acts as the sum of
their values. -/
lemma sectionsFunctor_map_hom_ringSum {ι : Type*} (s : Finset ι)
    (c : ι → (Z ⟶ ringSheaf R)) (z : (sectionsFunctor J X).obj Z) :
    (sectionsFunctor J X).map (∑ i ∈ s, c i) z = ∑ i ∈ s, (sectionsFunctor J X).map (c i) z :=
  map_sum (sectionsEvalRingAddHom X z) c s

end Sections

/-! ### Commutativity -/

section Commutative

variable [J.HasSheafCompose (forget RingCat.{w})] {R : Sheaf J RingCat.{w}}
  {Z : Sheaf J (Type w)}

/-- If the sections of a sheaf of rings commute — as they do when it is the underlying sheaf of
rings of a sheaf of *commutative* rings — then so do its generalized elements of any shape.

Commutativity is a hypothesis rather than an instance for the reason recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRelations`: a `CommRing` instance on the
sections of `R` competes with the `Ring` instance that `RingCat` carries and makes the scalar
action fail to elaborate. -/
lemma hom_mul_comm (hc : ∀ (X : Cᵒᵖ) (x y : (sectionsFunctor J X).obj (ringSheaf R)),
    x * y = y * x) (a b : Z ⟶ ringSheaf R) : a * b = b * a := by
  refine hom_ext_sections fun X z => ?_
  rw [sectionsFunctor_map_hom_mul, sectionsFunctor_map_hom_mul]
  exact hc X _ _

/-- Commutativity of the sections of a sheaf of rings, as an identity between morphisms out of
the square of its underlying sheaf of sets.  This is the form in which commutativity transports
along any finite-product-preserving functor. -/
lemma ringMulHom_comm (hc : ∀ (X : Cᵒᵖ) (x y : (sectionsFunctor J X).obj (ringSheaf R)),
    x * y = y * x) :
    Limits.prod.lift (Limits.prod.snd : ringSheaf R ⨯ ringSheaf R ⟶ ringSheaf R)
        Limits.prod.fst ≫ ringMulHom R =
      ringMulHom R := by
  refine hom_ext_sections fun X z => ?_
  refine Eq.trans ?_ (congrArg (fun p => (sectionsFunctor J X).map (ringMulHom R) p)
    (Functor.prodObjMk_map_fst_map_snd z))
  rw [Functor.map_comp_apply, Functor.map_lift_apply, sectionsFunctor_map_ringMulHom,
    sectionsFunctor_map_ringMulHom]
  exact hc X _ _

/-- The multiplication transported along a finite-product-preserving functor to types is
commutative as soon as the multiplication of the sections of the sheaf of rings is.  This is what
lets the commutativity hypothesis be discharged for an inverse-image sheaf of rings. -/
lemma ringMulObj_comm (hc : ∀ (X : Cᵒᵖ) (x y : (sectionsFunctor J X).obj (ringSheaf R)),
    x * y = y * x) (Q : Sheaf J (Type w) ⥤ Type t)
    [PreservesFiniteProducts Q] (x y : Q.obj (ringSheaf R)) :
    ringMulObj R Q x y = ringMulObj R Q y x := by
  have h := congrArg (fun m => Q.map m (Functor.prodObjMk (P := Q) x y))
    (ringMulHom_comm hc (R := R))
  rw [Q.map_comp_apply, Functor.map_lift_apply, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk] at h
  exact h.symm

end Commutative

end CategoryTheory.Sheaf

/-! ## Inverse images of generalized elements -/

namespace Stacks.Sheaves.ToposPullback

open CategoryTheory Limits Sheaf Functor Opposite

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  {R : Sheaf K RingCat.{ww'}} {M : SheafOfModules.{ww'} R}
  {Z : Sheaf K (Type ww')} {W : Sheaf J (Type ww)}

omit [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- The inverse image of a lift into a binary product, read through the product comparison, is
the lift of the inverse images. -/
lemma map_prodLift_comp_prodComparison {A B : Sheaf K (Type ww')} (a : Z ⟶ A) (b : Z ⟶ B) :
    Φ.map (Limits.prod.lift a b) ≫ Limits.prodComparison Φ A B =
      Limits.prod.lift (Φ.map a) (Φ.map b) := by
  refine Limits.prod.hom_ext ?_ ?_
  · rw [Category.assoc, Limits.prodComparison_fst, ← Φ.map_comp, Limits.prod.lift_fst,
      Limits.prod.lift_fst]
  · rw [Category.assoc, Limits.prodComparison_snd, ← Φ.map_comp, Limits.prod.lift_snd,
      Limits.prod.lift_snd]

omit [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] [PreservesFiniteProducts Φ] in
/-- The inverse image of a lift into a finite product, read through the product comparison, is
the lift of the inverse images. -/
lemma map_piLift_comp_piComparison {ι : Type} [Finite ι] (A : ι → Sheaf K (Type ww'))
    (g : ∀ i, Z ⟶ A i) :
    Φ.map (Limits.Pi.lift g) ≫ Limits.piComparison Φ A =
      Limits.Pi.lift (fun i => Φ.map (g i)) :=
  Limits.Pi.hom_ext _ _ (fun i => by
    rw [Category.assoc, Limits.piComparison_comp_π, ← Φ.map_comp, Limits.Pi.lift_comp_π,
      Limits.Pi.lift_comp_π])

omit [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] [PreservesFiniteProducts Φ] in
/-- The inverse image of the unique morphism to the terminal sheaf, read through the terminal
comparison, is the unique morphism to the terminal sheaf. -/
lemma map_terminalFrom_comp_terminalComparison :
    Φ.map (Limits.terminal.from Z) ≫ Limits.terminalComparison Φ =
      Limits.terminal.from (Φ.obj Z) :=
  Limits.terminal.hom_ext _ _

/-- `Φ` applied to a generalized element of a sheaf of rings, precomposed with a fixed morphism
and read as a generalized element of the inverse-image sheaf of rings.  This is the identity
function: the underlying sheaf of sets of `pullbackRingSheaf J Φ R` is `Φ.obj (ringSheaf R)` on
the nose.  It exists only so that the statements below can be elaborated with the ring structure
of the inverse image in scope. -/
def inverseImageRingElt (c : W ⟶ Φ.obj Z) (a : Z ⟶ ringSheaf R) :
    W ⟶ ringSheaf (pullbackRingSheaf J Φ R) := c ≫ Φ.map a

/-- `Φ` applied to a generalized element of a sheaf of modules, precomposed with a fixed morphism
and read as a generalized element of the inverse-image module.  As for
`Stacks.Sheaves.ToposPullback.inverseImageRingElt`, this is the identity function. -/
def inverseImageModuleElt (c : W ⟶ Φ.obj Z) (x : Z ⟶ moduleSheaf R M) :
    W ⟶ moduleSheaf (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) := c ≫ Φ.map x

omit [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- The inverse image of a lift into a binary product, followed by any morphism out of the
product of the inverse images, is the lift of the inverse images followed by that morphism.  This
is the one shape every statement below is an instance of; it is stated separately because an
associativity rewrite inside it would have to cross the two spellings of the inverse-image sheaf
of rings, which `rw` does not do. -/
lemma comp_map_prodLift {A B : Sheaf K (Type ww')} {E : Sheaf J (Type ww)}
    (c : W ⟶ Φ.obj Z) (a : Z ⟶ A) (b : Z ⟶ B) (m : Φ.obj A ⨯ Φ.obj B ⟶ E) :
    c ≫ Φ.map (Limits.prod.lift a b) ≫ (Limits.prodComparison Φ A B ≫ m) =
      Limits.prod.lift (c ≫ Φ.map a) (c ≫ Φ.map b) ≫ m := by
  rw [← Category.assoc (Φ.map (Limits.prod.lift a b)), map_prodLift_comp_prodComparison J Φ,
    ← Category.assoc, Limits.prod.comp_lift]

omit [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
omit [PreservesFiniteProducts Φ] in
/-- The terminal-object counterpart of
`Stacks.Sheaves.ToposPullback.comp_map_prodLift`. -/
lemma comp_map_terminalFrom {E : Sheaf J (Type ww)} (c : W ⟶ Φ.obj Z)
    (m : (⊤_ (Sheaf J (Type ww))) ⟶ E) :
    c ≫ Φ.map (Limits.terminal.from Z) ≫ (Limits.terminalComparison Φ ≫ m) =
      Limits.terminal.from W ≫ m := by
  rw [← Category.assoc (Φ.map (Limits.terminal.from Z)),
    map_terminalFrom_comp_terminalComparison J Φ, ← Category.assoc]
  exact congrArg (fun g => g ≫ m) (Limits.terminal.hom_ext _ _)

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- The inverse image is additive on generalized elements of a sheaf of rings. -/
lemma inverseImageRingElt_add (c : W ⟶ Φ.obj Z) (a b : Z ⟶ ringSheaf R) :
    inverseImageRingElt J Φ c (a + b) =
      inverseImageRingElt J Φ c a + inverseImageRingElt J Φ c b := by
  simp only [inverseImageRingElt]
  rw [hom_add_eq a b, hom_add_eq]
  exact comp_map_prodLift_comp Φ c a b _ _ (ringAdd_map_aux' J Φ R)

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- The inverse image is multiplicative on generalized elements of a sheaf of rings. -/
lemma inverseImageRingElt_mul (c : W ⟶ Φ.obj Z) (a b : Z ⟶ ringSheaf R) :
    inverseImageRingElt J Φ c (a * b) =
      inverseImageRingElt J Φ c a * inverseImageRingElt J Φ c b := by
  simp only [inverseImageRingElt]
  rw [hom_mul_eq a b, hom_mul_eq]
  exact comp_map_prodLift_comp Φ c a b _ _ (ringMul_map_aux' J Φ R)

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- The inverse image takes the zero generalized element of a sheaf of rings to zero. -/
lemma inverseImageRingElt_zero (c : W ⟶ Φ.obj Z) :
    inverseImageRingElt J Φ c (0 : Z ⟶ ringSheaf R) = 0 := by
  simp only [inverseImageRingElt]
  rw [hom_ringZero_eq, hom_ringZero_eq]
  exact comp_map_terminalFrom_comp Φ c _ _ (ringZero_map_aux J Φ R)

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- The inverse image takes the unit generalized element of a sheaf of rings to the unit. -/
lemma inverseImageRingElt_one (c : W ⟶ Φ.obj Z) :
    inverseImageRingElt J Φ c (1 : Z ⟶ ringSheaf R) = 1 := by
  simp only [inverseImageRingElt]
  rw [hom_one_eq, hom_one_eq]
  exact comp_map_terminalFrom_comp Φ c _ _ (ringOne_map_aux J Φ R)

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The inverse image is additive on generalized elements of a sheaf of modules. -/
lemma inverseImageModuleElt_add (c : W ⟶ Φ.obj Z) (x y : Z ⟶ moduleSheaf R M) :
    inverseImageModuleElt J Φ c (x + y) =
      inverseImageModuleElt J Φ c x + inverseImageModuleElt J Φ c y := by
  simp only [inverseImageModuleElt]
  rw [hom_moduleAdd_eq x y, hom_moduleAdd_eq]
  exact comp_map_prodLift_comp Φ c x y _ _ (moduleAdd_map_aux' J Φ R M)

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The inverse image takes the zero generalized element of a sheaf of modules to zero. -/
lemma inverseImageModuleElt_zero (c : W ⟶ Φ.obj Z) :
    inverseImageModuleElt J Φ c (0 : Z ⟶ moduleSheaf R M) = 0 := by
  simp only [inverseImageModuleElt]
  rw [hom_moduleZero_eq, hom_moduleZero_eq]
  exact comp_map_terminalFrom_comp Φ c _ _ (moduleZero_map_aux J Φ R M)

/-- The inverse image is semilinear on generalized elements: it takes a scalar multiple to the
scalar multiple of the inverse images, over the inverse-image sheaf of rings. -/
lemma inverseImageModuleElt_smul (c : W ⟶ Φ.obj Z) (r : Z ⟶ ringSheaf R)
    (x : Z ⟶ moduleSheaf R M) :
    inverseImageModuleElt J Φ c (r • x) =
      inverseImageRingElt J Φ c r • inverseImageModuleElt J Φ c x := by
  simp only [inverseImageModuleElt, inverseImageRingElt]
  rw [hom_smul_eq r x, hom_smul_eq]
  exact comp_map_prodLift_comp Φ c r x _ _ (moduleSMul_map_aux' J Φ R M)

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- **The sections of an inverse-image sheaf of rings commute if those of the original do.**
Multiplication on the sections of `pullbackRingSheaf J Φ R` over an object is the multiplication
transported along `Φ ⋙ sectionsFunctor J X`, so this is `ringMulObj_comm`. -/
lemma pullback_sections_mul_comm
    (hc : ∀ (Y : Dᵒᵖ) (x y : (sectionsFunctor K Y).obj (ringSheaf R)), x * y = y * x)
    (X : Cᵒᵖ) (x y : (sectionsFunctor J X).obj (ringSheaf (pullbackRingSheaf J Φ R))) :
    x * y = y * x :=
  ringMulObj_comm hc (Φ ⋙ sectionsFunctor J X) x y

/-- The inverse image of a generalized element of a sheaf of modules, precomposed with a fixed
morphism, as an additive map onto the generalized elements of the inverse-image module. -/
def inverseImageAddHom (c : W ⟶ Φ.obj Z) :
    (Z ⟶ moduleSheaf R M) →+
      (W ⟶ moduleSheaf (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M)) where
  toFun x := inverseImageModuleElt J Φ c x
  map_zero' := inverseImageModuleElt_zero J Φ c
  map_add' x y := inverseImageModuleElt_add J Φ c x y

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The inverse image commutes with a finite sum of generalized elements of a sheaf of
modules. -/
lemma inverseImageModuleElt_sum {ι : Type*} (s : Finset ι) (c : W ⟶ Φ.obj Z)
    (g : ι → (Z ⟶ moduleSheaf R M)) :
    inverseImageModuleElt J Φ c (∑ i ∈ s, g i) =
      ∑ i ∈ s, inverseImageModuleElt J Φ c (g i) :=
  map_sum (inverseImageAddHom J Φ c) g s

/-- The inverse image of a generalized element of a sheaf of rings, precomposed with a fixed
morphism, as an additive map onto the generalized elements of the inverse-image sheaf of
rings. -/
def inverseImageRingAddHom (c : W ⟶ Φ.obj Z) :
    (Z ⟶ ringSheaf R) →+ (W ⟶ ringSheaf (pullbackRingSheaf J Φ R)) where
  toFun a := inverseImageRingElt J Φ c a
  map_zero' := inverseImageRingElt_zero J Φ c
  map_add' a b := inverseImageRingElt_add J Φ c a b

omit [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})] in
/-- The inverse image commutes with a finite sum of generalized elements of a sheaf of rings. -/
lemma inverseImageRingElt_sum {ι : Type*} (s : Finset ι) (c : W ⟶ Φ.obj Z)
    (g : ι → (Z ⟶ ringSheaf R)) :
    inverseImageRingElt J Φ c (∑ i ∈ s, g i) =
      ∑ i ∈ s, inverseImageRingElt J Φ c (g i) :=
  map_sum (inverseImageRingAddHom J Φ c) g s

end Stacks.Sheaves.ToposPullback

end

/-! ### Further declarations -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe t w v u
namespace CategoryTheory.Sheaf
open CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
section
variable [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {R : Sheaf J RingCat.{w}} {M : SheafOfModules.{w} R} {Z Z' : Sheaf J (Type w)}

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Precomposition with a fixed morphism takes the unit generalized element of a sheaf of rings
to the unit. -/
lemma comp_hom_one (g : Z' ⟶ Z) : g ≫ (1 : Z ⟶ ringSheaf R) = 1 :=
  map_hom_one (coyoneda.obj (op Z')) g

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Precomposition with a fixed morphism, as a ring homomorphism of generalized elements of a
sheaf of rings.  Its four axioms are `comp_hom_one`, `comp_hom_mul`, `comp_hom_ringZero` and
`comp_hom_add`, the evaluation statements at `Q = coyoneda.obj (op Z')`, whose transported ring
structure is `CategoryTheory.Sheaf.homRing` on the nose. -/
def compRingHom (g : Z' ⟶ Z) : (Z ⟶ ringSheaf R) →+* (Z' ⟶ ringSheaf R) where
  toFun a := g ≫ a
  map_one' := comp_hom_one g
  map_mul' a b := comp_hom_mul g a b
  map_zero' := comp_hom_ringZero g
  map_add' a b := comp_hom_add g a b

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- `compRingHom g` is precomposition with `g`. -/
@[simp]
lemma compRingHom_apply (g : Z' ⟶ Z) (a : Z ⟶ ringSheaf R) : compRingHom g a = g ≫ a := rfl

end
end CategoryTheory.Sheaf
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe t w v u
namespace Stacks.Sheaves.ToposPullback
open CategoryTheory Limits Sheaf Functor Opposite
universe ww ww' vv uu vv' uu'
variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  {R : Sheaf K RingCat.{ww'}} {M : SheafOfModules.{ww'} R}
  {Z : Sheaf K (Type ww')} {W : Sheaf J (Type ww)}

/-- The inverse image of a generalized element of a sheaf of rings, precomposed with a fixed
morphism, as a *ring* homomorphism onto the generalized elements of the inverse-image sheaf of
rings.

This is the statement the file's opening paragraph promises: a polynomial identity between
generalized elements of `R` survives the inverse image, because the inverse image of
generalized elements is a ring homomorphism and not merely an additive one.  All four axioms are
`inverseImageRingElt_add`, `_mul`, `_zero` and `_one`. -/
def inverseImageRingEltRingHom (c : W ⟶ Φ.obj Z) :
    (Z ⟶ ringSheaf R) →+* (W ⟶ ringSheaf (pullbackRingSheaf J Φ R)) where
  toFun a := inverseImageRingElt J Φ c a
  map_one' := inverseImageRingElt_one J Φ c
  map_mul' a b := inverseImageRingElt_mul J Φ c a b
  map_zero' := inverseImageRingElt_zero J Φ c
  map_add' a b := inverseImageRingElt_add J Φ c a b

omit [J.HasSheafCompose (forget AddCommGrpCat)] [K.HasSheafCompose (forget AddCommGrpCat)] in
/-- `inverseImageRingEltRingHom J Φ c` sends `a` to `c ≫ Φ.map a`. -/
@[simp]
theorem inverseImageRingEltRingHom_apply (c : W ⟶ Φ.obj Z) (a : Z ⟶ ringSheaf R) :
    inverseImageRingEltRingHom J Φ c a = c ≫ Φ.map a :=
  rfl

end Stacks.Sheaves.ToposPullback
end
