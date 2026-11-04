module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCriterionConverse
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import StacksCore.Tactic.StacksAttribute

/-!
# The local equational criterion for flatness as local surjectivity of a map of presheaves of sets

Let `(C, J, O)` be a ringed site and `F` a sheaf of `O`-modules.  Part (2) of Stacks 08FC is the
statement that every single relation `∑ᵢ aᵢ • sᵢ = 0` among sections of `F` over an object `U`
admits, locally on `U`, a factorisation of the `sᵢ` through a finite free module by a matrix
annihilating the relation.  As stated in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatRelations.lean` that is a quantifier string
over objects, coverings, ranks and matrices.

This file re-expresses it as a single property of a **map of presheaves of sets** built from `O`
and `F`: local surjectivity of

`relationOfFactorization O F n : factorizationPresheaf O F n ⟶ relationPresheaf O F n`,

whose source has as sections over `U` the finite-free factorisations of `n` sections of `F` over
`U`, and whose target has as sections over `U` the `n`-term relations among sections of `F` over
`U`.

## Main definitions

* `Stacks.SheafOfModules.RelationData`: the sections of the relation presheaf — `n` sections of
  `O`, `n` sections of `F`, and the vanishing of the contraction.
* `Stacks.SheafOfModules.FactorizationData`: the sections of the factorization presheaf at a
  fixed rank — `n` sections of `O`, `l` sections of `F`, and an `l × n` matrix over `O`
  annihilating the coefficient vector.
* `Stacks.SheafOfModules.relationPresheaf`, `Stacks.SheafOfModules.factorizationPresheaf`: the
  two presheaves of sets, and `Stacks.SheafOfModules.relationOfFactorization`, the map reading a
  factorization as the relation it factors.

## Main results

* `Stacks.SheafOfModules.hasLocalSingleRelationFactorizations_iff_isLocallySurjective`: part (2)
  of Stacks 08FC holds for `F` **iff** `relationOfFactorization O F n` is locally surjective for
  every `n`.
* `Stacks.SheafOfModules.isFlat_iff_isLocallySurjective_relationOfFactorization`: the same read
  through the equivalence of parts (1) and (2) of Stacks 08FC, so that flatness itself becomes
  the local surjectivity of a map of presheaves of sets.

## Why this shape

The one route to Stacks 05VD that does not pass through Stacks 03CR needs the criterion in a
form the inverse image of a morphism of sites can be applied to.  What Stacks 00X1
(`CategoryTheory.Functor.IsMorphismOfSites`) supplies is exactness of `f⁻¹` on sheaves of
**sets**; what the source's own argument uses instead is filteredness of
`(StructuredArrow V f.u)ᵒᵖ`, which in the tree
(`StacksFrontier/CategoryTheory/Sites/Presheaf/Functoriality/StructuredArrowFiltered.lean`) needs a
terminal object and pullbacks in the source site — the situation the source reaches only after
Stacks 03CR.

Filteredness is used in the source for exactly one thing: finding a single stage of the colimit
computing `(f⁻¹G)(U)` at which finitely many sections **and** a relation among them are all
visible.  Packaging the coefficients, the sections and the relation as **one** section of a
single presheaf removes that need, because an element of a colimit of sets over an arbitrary
index category is already represented at some one stage.  Left exactness of `f⁻¹` is then what
identifies the relation presheaf of the inverse images with the inverse image of the relation
presheaf, since `relationPresheaf` is cut out of a finite product by one equation.

Both presheaves here are presheaves of **sets**, not of modules, and nothing in this file is
conditional on anything.  `factorizationPresheaf` is deliberately *not* a sheaf: its sections
over `U` are a disjoint union over the rank, a coproduct that sheafification does not compute
sectionwise.  Local surjectivity is a property of a map of presheaves
(`CategoryTheory.Presheaf.IsLocallySurjective`), so no sheaf condition is needed to state the
characterisation or to use it.

## Implementation notes

**The map `relationOfFactorization` needs commutativity of the sections of `O`.** The
factorization's matrix condition is `∑ᵢ Bₖᵢ aᵢ = 0`, with the matrix on the left, which is the
spelling `LocallyFactorsRelations` uses; the relation it has to produce contracts in the other
order.  `Stacks.SheafOfModules.ringSheaf_mul_comm` is the bridge and
`Stacks.SheafOfModules.sum_sum_mul_smul` does the reassociation, both from `FlatRelations`.

**The coefficient vector is part of the factorization data.** Without it
`relationOfFactorization` would not be a map into `relationPresheaf`, since a relation records
its coefficients; with it, the coefficient component of the map is the identity and the whole
content of the map is the second component.

**The rank is a parameter of `FactorizationData`, not a field of it.** With the rank as a field,
`gens` and `matrix` depend on it and the generated extensionality lemma is heterogeneous;
with the rank as a parameter and the disjoint union taken in `factorizationPresheaf.obj`,
every extensionality step below is between structures with no dependent fields.

**`PresheafOfModules` has no pointwise `map_id`.** `PresheafOfModules.map_comp_apply` exists but
its identity counterpart does not, because `map_id` is stated through
`ModuleCat.restrictScalarsId'`.  `val_map_id_apply` below routes around it through the
underlying abelian presheaf `PresheafOfModules.presheaf`, where `map_id` is a plain functor
identity.

**`Type w` is not a category of bare functions.** `CategoryTheory.types` has
`Hom := TypeCat.Hom`, a structure, so the functor fields below are written with `↾`, and a
morphism equation is reduced to a function equation by `TypeCat.homEquiv.injective` rather than
by `funext`.  The `ext` tactic is *not* used for those: it keeps going past the function
equation into `RelationData.ext` and then `funext` again, leaving per-field goals in place of
the one structure equation the restriction lemmas below state.

**Universes are not narrowed here.**  The site keeps independent object and morphism universes
`u` and `v` and the sections of `O` and `F` live in an independent `w`, exactly as in
`FlatRelations`; the two presheaves of sets are `Cᵒᵖ ⥤ Type w`.  The flatness corollary inherits
the `max v w` of `FlatCriterionConverse`, where the free presheaf on the index set `V ⟶ U`
forces it; that narrowing is not chosen here.

**No tag is placed in this file.**  Stacks 08FC's parts are already tagged in `FlatRelations`
and `FlatCriterionConverse`, and nothing here is a further assertion of 08FC.  Nothing here is
an assertion of Stacks 05VD either: both of its clauses concern the unconditional pullback
statement.

## References

* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
* [Stacks Project, Tag 00X3](https://stacks.math.columbia.edu/tag/00X3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

noncomputable section

namespace Stacks.SheafOfModules

section Construction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (O : Sheaf J CommRingCat.{w})
  (F : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O))

/-! ### Pointwise restriction lemmas -/

/-- Restricting a section of the structure sheaf along the identity does nothing. -/
lemma ringSheaf_map_id_apply {U : Cᵒᵖ} (x : (commRingSheafToRingSheaf O).obj.obj U) :
    ((commRingSheafToRingSheaf O).obj.map (𝟙 U)).hom x = x := by
  rw [(commRingSheafToRingSheaf O).obj.map_id]
  rfl

/-- Restricting a section of `F` along the identity does nothing.  `PresheafOfModules` states
`map_id` through `ModuleCat.restrictScalarsId'`, so the pointwise statement is read off the
underlying abelian presheaf instead. -/
lemma val_map_id_apply {U : Cᵒᵖ} (x : F.val.obj U) : (F.val.map (𝟙 U)).hom x = x := by
  rw [← PresheafOfModules.presheaf_map_apply_coe, F.val.presheaf.map_id]
  rfl

/-- Restriction along an arbitrary morphism of `Cᵒᵖ` of a vanishing relation between sections of
`F` is the corresponding vanishing relation between the restricted sections.  This is
`Stacks.SheafOfModules.sum_smul_restrict_eq_zero` with the morphism not presented as an
opposite. -/
lemma sum_smul_map_eq_zero {U V : Cᵒᵖ} (g : U ⟶ V) {n : ℕ}
    (a : Fin n → (commRingSheafToRingSheaf O).obj.obj U) (s : Fin n → F.val.obj U)
    (h : ∑ i : Fin n, a i • s i = 0) :
    ∑ i : Fin n, ((commRingSheafToRingSheaf O).obj.map g).hom (a i) •
      (F.val.map g).hom (s i) = 0 := by
  exact sum_smul_restrict_eq_zero g.unop a s h

/-- Restriction of a matrix identity over the structure sheaf. -/
lemma sum_mul_map_eq_zero {U V : Cᵒᵖ} (g : U ⟶ V) {n : ℕ}
    (b a : Fin n → (commRingSheafToRingSheaf O).obj.obj U)
    (h : ∑ i : Fin n, b i * a i = 0) :
    ∑ i : Fin n, ((commRingSheafToRingSheaf O).obj.map g).hom (b i) *
      ((commRingSheafToRingSheaf O).obj.map g).hom (a i) = 0 := by
  simpa [← map_mul, ← map_sum] using congrArg ((commRingSheafToRingSheaf O).obj.map g).hom h

/-! ### The sections -/

/-- An `n`-term relation among sections of `F` over `U`: `n` sections of the structure sheaf,
`n` sections of `F`, and the vanishing of the contraction. -/
@[ext]
structure RelationData (U : Cᵒᵖ) (n : ℕ) : Type w where
  /-- The coefficients of the relation. -/
  coeffs : Fin n → (commRingSheafToRingSheaf O).obj.obj U
  /-- The sections of `F` the relation is among. -/
  elts : Fin n → F.val.obj U
  /-- The relation. -/
  relation : ∑ i : Fin n, coeffs i • elts i = 0

/-- A rank-`l` finite-free factorization of `n` sections of `F` over `U` annihilating a
coefficient vector: sections `t : Fin l → F(U)` and a matrix `B : Fin l → Fin n → O(U)` with
`∑ᵢ Bₖᵢ aᵢ = 0` for every `k`.  The factored sections are not part of the data: they are
recovered as `∑ₖ Bₖᵢ • tₖ`, which is what `relationOfFactorization` computes. -/
@[ext]
structure FactorizationData (U : Cᵒᵖ) (n l : ℕ) : Type w where
  /-- The coefficient vector the matrix annihilates. -/
  coeffs : Fin n → (commRingSheafToRingSheaf O).obj.obj U
  /-- The sections of `F` generating the finite free module. -/
  gens : Fin l → F.val.obj U
  /-- The factorization matrix. -/
  matrix : Fin l → Fin n → (commRingSheafToRingSheaf O).obj.obj U
  /-- The matrix annihilates the coefficient vector. -/
  matrix_coeffs : ∀ k : Fin l, ∑ i : Fin n, matrix k i * coeffs i = 0

/-- Restriction of a relation along a morphism of the site. -/
def relationRestrict {U V : Cᵒᵖ} (g : U ⟶ V) {n : ℕ} (p : RelationData O F U n) :
    RelationData O F V n where
  coeffs i := ((commRingSheafToRingSheaf O).obj.map g).hom (p.coeffs i)
  elts i := (F.val.map g).hom (p.elts i)
  relation := sum_smul_map_eq_zero O F g p.coeffs p.elts p.relation

/-- Restriction of a factorization along a morphism of the site. -/
def factorizationRestrict {U V : Cᵒᵖ} (g : U ⟶ V) {n l : ℕ}
    (x : FactorizationData O F U n l) : FactorizationData O F V n l where
  coeffs i := ((commRingSheafToRingSheaf O).obj.map g).hom (x.coeffs i)
  gens k := (F.val.map g).hom (x.gens k)
  matrix k i := ((commRingSheafToRingSheaf O).obj.map g).hom (x.matrix k i)
  matrix_coeffs k := sum_mul_map_eq_zero O g (x.matrix k) x.coeffs (x.matrix_coeffs k)

/-- Restricting a relation along the identity gives the same relation. -/
lemma relationRestrict_id {U : Cᵒᵖ} {n : ℕ} (p : RelationData O F U n) :
    relationRestrict O F (𝟙 U) p = p :=
  RelationData.ext (funext fun i => ringSheaf_map_id_apply O (p.coeffs i))
    (funext fun i => val_map_id_apply O F (p.elts i))

/-- Restricting a relation along `g ≫ h` is restricting along `g` and then along `h`. -/
lemma relationRestrict_comp {U V W : Cᵒᵖ} (g : U ⟶ V) (h : V ⟶ W) {n : ℕ}
    (p : RelationData O F U n) :
    relationRestrict O F (g ≫ h) p = relationRestrict O F h (relationRestrict O F g p) :=
  RelationData.ext (funext fun i => ringSheaf_map_comp_apply O g h (p.coeffs i))
    (funext fun i => PresheafOfModules.map_comp_apply _ g h (p.elts i))

/-- Restricting a factorization along the identity gives the same factorization. -/
lemma factorizationRestrict_id {U : Cᵒᵖ} {n l : ℕ} (x : FactorizationData O F U n l) :
    factorizationRestrict O F (𝟙 U) x = x :=
  FactorizationData.ext (funext fun i => ringSheaf_map_id_apply O (x.coeffs i))
    (funext fun k => val_map_id_apply O F (x.gens k))
    (funext fun k => funext fun i => ringSheaf_map_id_apply O (x.matrix k i))

/-- Restricting a factorization along `g ≫ h` is restricting along `g` and then along `h`. -/
lemma factorizationRestrict_comp {U V W : Cᵒᵖ} (g : U ⟶ V) (h : V ⟶ W) {n l : ℕ}
    (x : FactorizationData O F U n l) :
    factorizationRestrict O F (g ≫ h) x =
      factorizationRestrict O F h (factorizationRestrict O F g x) :=
  FactorizationData.ext (funext fun i => ringSheaf_map_comp_apply O g h (x.coeffs i))
    (funext fun k => PresheafOfModules.map_comp_apply _ g h (x.gens k))
    (funext fun k => funext fun i => ringSheaf_map_comp_apply O g h (x.matrix k i))

/-! ### The two presheaves of sets and the map between them -/

/-- The presheaf of sets whose sections over `U` are the `n`-term relations among sections of
`F` over `U`. -/
def relationPresheaf (n : ℕ) : Cᵒᵖ ⥤ Type w where
  obj U := RelationData O F U n
  map g := ↾fun p => relationRestrict O F g p
  map_id _ := TypeCat.homEquiv.injective (funext fun p => relationRestrict_id O F p)
  map_comp g h := TypeCat.homEquiv.injective (funext fun p => relationRestrict_comp O F g h p)

/-- The presheaf of sets whose sections over `U` are the finite-free factorizations, of any
rank, of `n` sections of `F` over `U`. -/
def factorizationPresheaf (n : ℕ) : Cᵒᵖ ⥤ Type w where
  obj U := Σ l : ℕ, FactorizationData O F U n l
  map g := ↾fun x => ⟨x.1, factorizationRestrict O F g x.2⟩
  map_id U := TypeCat.homEquiv.injective <| funext fun x =>
    congrArg (fun y => (⟨x.1, y⟩ : Σ l : ℕ, FactorizationData O F U n l))
      (factorizationRestrict_id O F x.2)
  map_comp {_ _ W} g h := TypeCat.homEquiv.injective <| funext fun x =>
    congrArg (fun y => (⟨x.1, y⟩ : Σ l : ℕ, FactorizationData O F W n l))
      (factorizationRestrict_comp O F g h x.2)

/-- The restriction maps of `relationPresheaf` are `relationRestrict`. -/
@[simp]
lemma relationPresheaf_map_apply {n : ℕ} {U V : Cᵒᵖ} (g : U ⟶ V) (p : RelationData O F U n) :
    ((relationPresheaf O F n).map g) p = relationRestrict O F g p := rfl

/-- The restriction maps of `factorizationPresheaf` keep the rank and apply
`factorizationRestrict`. -/
@[simp]
lemma factorizationPresheaf_map_apply {n : ℕ} {U V : Cᵒᵖ} (g : U ⟶ V)
    (x : Σ l : ℕ, FactorizationData O F U n l) :
    ((factorizationPresheaf O F n).map g) x = ⟨x.1, factorizationRestrict O F g x.2⟩ := rfl

/-- The relation a factorization factors: the coefficients are kept and the sections are
recovered as `∑ₖ Bₖᵢ • tₖ`.  That this is a relation is the matrix condition, reassociated by
`sum_sum_mul_smul`. -/
def relationOfFactorizationApp {U : Cᵒᵖ} {n : ℕ} (x : Σ l : ℕ, FactorizationData O F U n l) :
    RelationData O F U n where
  coeffs := x.2.coeffs
  elts i := ∑ k : Fin x.1, x.2.matrix k i • x.2.gens k
  relation :=
    (sum_sum_mul_smul (ringSheaf_mul_comm O) x.2.matrix x.2.coeffs x.2.gens).symm.trans
      (Finset.sum_eq_zero fun k _ => by rw [x.2.matrix_coeffs k, zero_smul])

/-- Reading a finite-free factorization as the relation it factors, as a map of presheaves of
sets. -/
def relationOfFactorization (n : ℕ) :
    factorizationPresheaf O F n ⟶ relationPresheaf O F n where
  app U := ↾fun x => relationOfFactorizationApp O F x
  naturality {U V} g := by
    apply TypeCat.homEquiv.injective
    funext x
    refine RelationData.ext rfl (funext fun i => ?_)
    change ∑ k : Fin x.1, ((commRingSheafToRingSheaf O).obj.map g).hom (x.2.matrix k i) •
        (F.val.map g).hom (x.2.gens k)
      = (F.val.map g).hom (∑ k : Fin x.1, x.2.matrix k i • x.2.gens k)
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => (PresheafOfModules.map_smul _ _ _ _).symm

/-- The component of `relationOfFactorization` at `U` is `relationOfFactorizationApp`. -/
@[simp]
lemma relationOfFactorization_app_apply {n : ℕ} {U : Cᵒᵖ}
    (x : Σ l : ℕ, FactorizationData O F U n l) :
    ((relationOfFactorization O F n).app U) x = relationOfFactorizationApp O F x := rfl

/-! ### The characterisation -/

/-- **Stacks 08FC part (2) as local surjectivity of a map of presheaves of sets.**  A sheaf of
modules on a ringed site satisfies the single-relation form of the local equational criterion
for flatness exactly when, for every `n`, the map from the presheaf of finite-free
factorizations of `n` sections to the presheaf of `n`-term relations is locally surjective.

The two statements are the same quantifier string: the image sieve of a relation at `U` consists
of the `V ⟶ U` on which the restricted relation admits a factorization, and a sieve containing a
covering sieve is covering. -/
theorem hasLocalSingleRelationFactorizations_iff_isLocallySurjective :
    HasLocalSingleRelationFactorizations O F ↔
      ∀ n : ℕ, Presheaf.IsLocallySurjective J (relationOfFactorization O F n) := by
  refine ⟨fun h n => ⟨fun {U} p => ?_⟩, fun h U n a s ha => ?_⟩
  · obtain ⟨S, hS, hfac⟩ := h U n p.coeffs p.elts p.relation
    refine J.superset_covering (fun V g hg => ?_) hS
    obtain ⟨l, t, B, h₁, h₂⟩ := hfac g hg
    refine ⟨⟨l, { coeffs i := ((commRingSheafToRingSheaf O).obj.map g.op).hom (p.coeffs i)
                  gens := t
                  matrix := B
                  matrix_coeffs k := h₂ k 0 }⟩, ?_⟩
    exact RelationData.ext rfl (funext fun i => (h₁ i).symm)
  · refine ⟨Presheaf.imageSieve (relationOfFactorization O F n)
      ({ coeffs := a, elts := s, relation := ha } : RelationData O F (op U) n),
      (h n).imageSieve_mem _, ?_⟩
    rintro V g ⟨x, hx⟩
    have hx' : relationOfFactorizationApp O F x
        = relationRestrict O F g.op
          ({ coeffs := a, elts := s, relation := ha } : RelationData O F (op U) n) := hx
    have hc := congrArg (fun y => RelationData.coeffs y) hx'
    refine ⟨x.1, x.2.gens, x.2.matrix,
      fun i => (congrArg (fun y => RelationData.elts y i) hx').symm,
      fun k j => Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (x.2.matrix_coeffs k)⟩
    exact congrArg (fun y => x.2.matrix k i * y) (congrFun hc i).symm

end Construction

section Flat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max v w} RingCat.{max v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v w}]
  [HasWeakSheafify J AddCommGrpCat.{max v w}]

/-- **Flatness of a sheaf of modules on a ringed site is the local surjectivity of a map of
presheaves of sets.**  This is
`hasLocalSingleRelationFactorizations_iff_isLocallySurjective` composed with the equivalence of
parts (1) and (2) of Stacks 08FC. -/
theorem isFlat_iff_isLocallySurjective_relationOfFactorization
    (O : Sheaf J CommRingCat.{max v w})
    (F : _root_.SheafOfModules.{max v w} (commRingSheafToRingSheaf O)) :
    IsFlat F ↔
      ∀ n : ℕ, Presheaf.IsLocallySurjective J (relationOfFactorization O F n) :=
  (isFlat_iff_hasLocalSingleRelationFactorizations F).trans
    (hasLocalSingleRelationFactorizations_iff_isLocallySurjective O F)

end Flat

end Stacks.SheafOfModules

end

end
