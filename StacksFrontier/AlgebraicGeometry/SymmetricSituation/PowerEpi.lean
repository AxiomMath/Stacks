module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricConstruction
public import StacksFrontier.AlgebraicGeometry.SymmetricSituation.SliceRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise

/-!
# Symmetric powers of an epimorphism, and symmetric powers after sheafification

Tag 01CJ asserts that a presentation `F₂ ⟶ F₁ ⟶ F ⟶ 0` of a sheaf of modules induces, in every
positive degree `n`, an exact sequence

`F₂ ⊗ Sym^{n-1}(F₁) ⟶ Symⁿ(F₁) ⟶ Symⁿ(F) ⟶ 0`.

Its two maps and the fact that they compose to zero are built in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences`; **this file proves
that the second map is an epimorphism**, in every degree and over an arbitrary ringed site, and
proves the comparison that identifies a symmetric power of a sheafification.

Both results rest on the same observation about the construction: the degree-`n` piece of
`SheafOfModules.sheafifiedSymmetricAlgebra` is the sheafification of the presheaf of
*sectionwise* symmetric powers `U ↦ Symⁿ_{O(U)}(F(U))`
(`Stacks.GradedAlgebra.sheafify_piece`), so a statement about it can be reduced to a sectionwise
statement about `SymmetricAlgebra` plus a local argument.

## The epimorphy half of Tag 01CJ

`SymPow.symmetricPower n R M` is the `n`-th power of the range of `SymmetricAlgebra.ι` and is
therefore *spanned* by the products of `n` degree-one generators
(`SymmetricAlgebra.symmetricPower_eq_span_prod_ι`). So a local section of `Symⁿ F` is, locally, a
finite sum of products of `n` local sections of `F`, and if `p : F₁ ⟶ F` is an epimorphism —
equivalently locally surjective, `Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective` —
each of those finitely many local sections lifts along `p` after a further refinement. Hence
`Symⁿ(p)` is locally surjective, hence an epimorphism. No stalk, and no exactness, is involved.

## Symmetric powers and sheafification

`SheafOfModules.symmetricPieceSheafifyIso` identifies the degree-`n` piece of the sheafification
of the sectionwise symmetric algebra of an arbitrary presheaf of modules `Q` with the degree-`n`
symmetric power of the sheaf of modules `Q` sheafifies to. This is the comparison that lets a
*sectionwise* exact sequence be sheafified and then read as a sequence of symmetric powers of
sheaves; see the implementation notes for what it is not.

## Main definitions

* `PresheafOfModules.symmetricAlgebraPieceMap`: the degree-`n` sectionwise symmetric power of a
  morphism of presheaves of modules, `Symⁿ_{O(U)}(φ_U)` for each `U`.
* `SheafOfModules.symmetricDescFamily`: that map followed by the sheafification unit, the
  degreewise datum the universal property of the sheafified algebra consumes.
* `SheafOfModules.symmetricDescHom`: the induced unital homomorphism of graded algebras
  `Sym(F₁) ⟶ Sym(F)`.
* `SheafOfModules.symmetricPieceSheafifyIso`: the degree-`n` symmetric power of a sheafification.

## Main results

* `PresheafOfModules.exists_covering_finite_lift`: **finitely many local sections lift along a
  locally surjective morphism on one common covering sieve.** The binary intersection of
  covering sieves is all the locality this file needs, iterated over a `Fin k`.
* `PresheafOfModules.isLocallySurjective_symmetricAlgebraPieceMap`: **the sectionwise symmetric
  powers of a locally surjective morphism of presheaves of modules are locally surjective**, in
  every integer degree.
* `SheafOfModules.symmetricDescHom_eq_descComp`: `symmetricDescHom` is the homomorphism the
  universal property of the symmetric algebra produces from `p`, so the result below is about
  the second map of the sequence of Tag 01CJ and not about some other map.
* `SheafOfModules.epi_descComp_app_symmetric`: **the degree-`n` symmetric power of an
  epimorphism of sheaves of modules is an epimorphism.** This is the epimorphy half of
  Tag 01CJ, in every degree.
* `SheafOfModules.presentation_sheafifiedSymmetricPiece_of_sheafifyIso` and
  `isQuasicoherent_sheafifiedSymmetricPiece_of_sheafifyIso`: a presentation, respectively
  quasi-coherence, of the sheafified sectionwise symmetric power of a presheaf transfers to the
  symmetric power of the sheaf it sheafifies to.

## Implementation notes

**No `@[stacks]` tag.** Tag 01CJ asserts exactness at the middle term *and* epimorphy of the
second map; only the second is proved here, so a tag — even a clause tag — would report the tag
as covered when its principal content is not. This follows the deliberate choice recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences`. What remains is
exactness at the middle term; see below for the route the comparison here opens.

**Epimorphy in every degree, not only in degree one.**
`SheafOfModules.GradedAlgebra.IsUniversal.epi_descComp_app_one` reaches degree one from the
universal property alone and records that higher degrees need the target algebra to be
*generated in degree one*, which the universal property supplies only through a construction.
`SheafOfModules.sheafifiedSymmetricAlgebra` is such a construction, and generation in degree one
is exactly `SymmetricAlgebra.symmetricPower_eq_span_prod_ι` read through the sheafification
unit — which is how the restriction to degree one is lifted here.

**What `symmetricPieceSheafifyIso` is, and what it is not.** It is *not* Tag 01CH: no stalk
appears in it and it holds over an arbitrary site. It is the degreewise form of the known
statement that the sheafification of the sectionwise symmetric algebra of a presheaf of
modules `Q` satisfies the universal property of the symmetric algebra *of the sheafification of
`Q`* (`PresheafOfModules.isSymmetricAlgebra_sheafify_symmetricAlgebra`, which is stated for an
arbitrary presheaf of modules and not only for the underlying presheaf of a sheaf), combined
with the uniqueness of a symmetric algebra up to canonical isomorphism
(`SheafOfModules.GradedAlgebra.IsSymmetricAlgebra.pieceIso`). In particular the passage from
`Symⁿ` of a presheaf to `Symⁿ` of its sheafification — the step whose natural proof is a stalk
computation — is available without one.

**Degrees are `ℤ`.** `SymPow.symmetricPowerInt` is `SymPow.symmetricPower` in a nonnegative
degree and `⊥` in a negative one, so the local-surjectivity argument splits on the sign of the
degree: in a negative degree the pieces are zero modules and every morphism between them is
surjective on sections.

## References

* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 00DO](https://stacks.math.columbia.edu/tag/00DO)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe v u w a

namespace PresheafOfModules

/-! ### The sectionwise symmetric powers of a morphism of presheaves of modules -/

section Map

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F G : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}

/-- Base change of the symmetric algebra along a restriction map commutes with base change along
a morphism of presheaves of modules: the naturality of the sectionwise symmetric powers, before
they are cut down to a homogeneous piece. -/
theorem mapₛₗ_restrictₛₗ_comm (φ : F ⟶ G) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    SymmetricAlgebra.mapₛₗ (RingHom.id ((O ⋙ forget₂ _ RingCat).obj Y)) (Hom.app φ Y).hom
        (SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) x) =
      SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (G.restrictₛₗ f)
        (SymmetricAlgebra.mapₛₗ (RingHom.id ((O ⋙ forget₂ _ RingCat).obj X))
          (Hom.app φ X).hom x) :=
  let v := ((Hom.app φ Y).hom).comp (F.restrictₛₗ f)
  ((SymmetricAlgebra.mapₛₗ_eq_comp (F.restrictₛₗ f) ((Hom.app φ Y).hom) v
      (fun _ => rfl) (fun _ => rfl) x).symm.trans
    (SymmetricAlgebra.mapₛₗ_eq_comp ((Hom.app φ X).hom) (G.restrictₛₗ f) v
      (fun _ => rfl) (fun m => restrictₛₗ_naturality_apply φ f m) x))

/-- **The degree-`n` sectionwise symmetric power of a morphism of presheaves of modules.** -/
noncomputable def symmetricAlgebraPieceMap (n : ℤ) (φ : F ⟶ G) :
    symPowInt n F ⟶ symPowInt n G where
  app X := ModuleCat.ofHom
    (SymPow.symMapIntₛₗ n (RingHom.id ((O ⋙ forget₂ _ RingCat).obj X))
      (Hom.app φ X).hom)
  naturality {X _Y} f := ModuleCat.hom_ext (LinearMap.ext fun x =>
    Subtype.ext (mapₛₗ_restrictₛₗ_comm φ f (symPowIntVal x)))

/-- On sections over `X`, the degree-`n` symmetric power of `φ` is the restriction of the map of
symmetric algebras induced by `φ` over `X`. -/
@[simp]
theorem symPowIntVal_pieceMap (n : ℤ) (φ : F ⟶ G) (X : Cᵒᵖ)
    (x : (symPowInt n F).obj X) :
    symPowIntVal (Hom.app (symmetricAlgebraPieceMap n φ) X x) =
      SymmetricAlgebra.mapₛₗ (RingHom.id ((O ⋙ forget₂ _ RingCat).obj X)) (Hom.app φ X).hom
        (symPowIntVal x) := rfl

/-- The sectionwise symmetric powers of a morphism of presheaves of modules are multiplicative
for the grading. -/
theorem symmetricAlgebraPieceMap_mul (φ : F ⟶ G) (i j : ℤ) (X : Cᵒᵖ)
    (x : (symPowInt i F).obj X) (y : (symPowInt j F).obj X) :
    Hom.app (symmetricAlgebraPieceMap (i + j) φ) X
        (((symPowIntGradedAlgebra F).mul i j).app X x y) =
      ((symPowIntGradedAlgebra G).mul i j).app X
        (Hom.app (symmetricAlgebraPieceMap i φ) X x)
        (Hom.app (symmetricAlgebraPieceMap j φ) X y) := by
  refine symPowIntVal_injective (i + j) G ?_
  rw [symPowIntVal_pieceMap, symPowIntGradedAlgebra_mul,
    symPowIntGradedAlgebra_mul, symPowIntVal_mul,
    symPowIntVal_mul, symPowIntVal_pieceMap,
    symPowIntVal_pieceMap, map_mul]

/-- The sectionwise symmetric powers of a morphism of presheaves of modules carry the unit of the
graded algebra to the unit. -/
theorem symmetricAlgebraPieceMap_one (φ : F ⟶ G) (X : Cᵒᵖ) :
    Hom.app (symmetricAlgebraPieceMap 0 φ) X ((symPowIntOne F).eval X) =
      (symPowIntOne G).eval X := by
  refine symPowIntVal_injective 0 G ?_
  rw [symPowIntVal_pieceMap, symPowIntVal_one,
    symPowIntVal_one, map_one]

/-- In degree one the sectionwise symmetric power of a morphism of presheaves of modules is the
morphism itself, read through the degree-one generators. -/
theorem symmetricAlgebraPieceMap_gen (φ : F ⟶ G) (X : Cᵒᵖ) (m : F.obj X) :
    Hom.app (symmetricAlgebraPieceMap 1 φ) X (Hom.app (symPowIntGen F) X m) =
      Hom.app (symPowIntGen G) X (Hom.app φ X m) := by
  refine symPowIntVal_injective 1 G ?_
  rw [symPowIntVal_pieceMap, symPowIntVal_gen,
    symPowIntVal_gen, SymmetricAlgebra.mapₛₗ_ι]

end Map

/-! ### Local surjectivity of the sectionwise symmetric powers -/

section LocallySurjective

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F G : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (J : GrothendieckTopology C) (φ : F ⟶ G)

/-- **Finitely many local sections lift along a locally surjective morphism of presheaves of
modules on one common covering sieve.** -/
theorem exists_covering_finite_lift
    (hφ : Presheaf.IsLocallySurjective J ((toPresheaf (O ⋙ forget₂ _ RingCat)).map φ))
    (k : ℕ) {U : C} (s : Fin k → G.obj (op U)) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ ⦃V : C⦄ (g : V ⟶ U), S g →
      ∃ t : Fin k → F.obj (op V), ∀ i, Hom.app φ (op V) (t i) = G.map g.op (s i) := by
  have := hφ
  induction k with
  | zero => exact ⟨⊤, J.top_mem U, fun V g _ => ⟨Fin.elim0, fun i => i.elim0⟩⟩
  | succ k ih =>
      obtain ⟨S, hS, hlift⟩ := ih (fun i => s i.succ)
      refine ⟨Presheaf.imageSieve ((toPresheaf (O ⋙ forget₂ _ RingCat)).map φ) (s 0) ⊓ S,
        J.intersection_covering
          (Presheaf.imageSieve_mem J ((toPresheaf (O ⋙ forget₂ _ RingCat)).map φ) (s 0)) hS, ?_⟩
      rintro V g ⟨⟨t₀, ht₀⟩, hg⟩
      obtain ⟨t, ht⟩ := hlift g hg
      refine ⟨Fin.cons t₀ t, fun i => ?_⟩
      induction i using Fin.cases with
      | zero => exact ht₀
      | succ j => exact ht j

/-- Local liftability in degree `k`, along `φ`, of an element of the symmetric algebra of the
sections of `G`: on a covering sieve its restriction is the image of a degree-`k` element. -/
private def LocLift (k : ℕ) {U : C}
    (y : SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj (op U)) (G.obj (op U))) : Prop :=
  ∃ S : Sieve U, S ∈ J U ∧ ∀ ⦃V : C⦄ (g : V ⟶ U), S g →
    ∃ z ∈ SymPow.symmetricPower k ((O ⋙ forget₂ _ RingCat).obj (op V)) (F.obj (op V)),
      SymmetricAlgebra.mapₛₗ (RingHom.id _) (Hom.app φ (op V)).hom z =
        SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map g.op).hom (G.restrictₛₗ g.op) y

private theorem locLift_zero (k : ℕ) {U : C} : LocLift J φ k (U := U) 0 :=
  ⟨⊤, J.top_mem U, fun V g _ => ⟨0, Submodule.zero_mem _, by rw [map_zero, map_zero]⟩⟩

private theorem locLift_add {k : ℕ} {U : C}
    {y y' : SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj (op U)) (G.obj (op U))}
    (h : LocLift J φ k y) (h' : LocLift J φ k y') : LocLift J φ k (y + y') := by
  obtain ⟨S, hS, hz⟩ := h
  obtain ⟨S', hS', hz'⟩ := h'
  refine ⟨S ⊓ S', J.intersection_covering hS hS', fun V g hg => ?_⟩
  obtain ⟨z, hzmem, hzeq⟩ := hz g hg.1
  obtain ⟨z', hzmem', hzeq'⟩ := hz' g hg.2
  exact ⟨z + z', Submodule.add_mem _ hzmem hzmem', by rw [map_add, map_add, hzeq, hzeq']⟩

private theorem locLift_smul {k : ℕ} {U : C}
    (r : (O ⋙ forget₂ _ RingCat).obj (op U))
    {y : SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj (op U)) (G.obj (op U))}
    (h : LocLift J φ k y) : LocLift J φ k (r • y) := by
  obtain ⟨S, hS, hz⟩ := h
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨z, hzmem, hzeq⟩ := hz g hg
  refine ⟨((O ⋙ forget₂ _ RingCat).map g.op).hom r • z, Submodule.smul_mem _ _ hzmem, ?_⟩
  rw [SymmetricAlgebra.mapₛₗ_smul, SymmetricAlgebra.mapₛₗ_smul, hzeq, RingHom.id_apply]

private theorem locLift_prod_ι
    (hφ : Presheaf.IsLocallySurjective J ((toPresheaf (O ⋙ forget₂ _ RingCat)).map φ))
    (k : ℕ) {U : C} (s : Fin k → G.obj (op U)) :
    LocLift J φ k (∏ i : Fin k, SymmetricAlgebra.ι _ (G.obj (op U)) (s i)) := by
  obtain ⟨S, hS, hlift⟩ := exists_covering_finite_lift J φ hφ k s
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨t, ht⟩ := hlift g hg
  refine ⟨∏ i : Fin k, SymmetricAlgebra.ι _ (F.obj (op V)) (t i),
    SymmetricAlgebra.prod_ι_mem _ t, ?_⟩
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [SymmetricAlgebra.mapₛₗ_ι, SymmetricAlgebra.mapₛₗ_ι, ht i]
  rfl

private theorem locLift_of_mem
    (hφ : Presheaf.IsLocallySurjective J ((toPresheaf (O ⋙ forget₂ _ RingCat)).map φ))
    (k : ℕ) {U : C}
    {y : SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj (op U)) (G.obj (op U))}
    (hy : y ∈ SymPow.symmetricPower k ((O ⋙ forget₂ _ RingCat).obj (op U)) (G.obj (op U))) :
    LocLift J φ k y := by
  rw [SymmetricAlgebra.symmetricPower_eq_span_prod_ι] at hy
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨s, rfl⟩ := hy; exact locLift_prod_ι J φ hφ k s
  | zero => exact locLift_zero J φ k
  | add y z _ _ hy hz => exact locLift_add J φ hy hz
  | smul r y _ hy => exact locLift_smul J φ r hy

/-- **The sectionwise symmetric powers of a locally surjective morphism of presheaves of modules
are locally surjective**, in every integer degree. -/
theorem isLocallySurjective_symmetricAlgebraPieceMap
    (hφ : Presheaf.IsLocallySurjective J ((toPresheaf (O ⋙ forget₂ _ RingCat)).map φ))
    (n : ℤ) :
    Presheaf.IsLocallySurjective J
      ((toPresheaf (O ⋙ forget₂ _ RingCat)).map (symmetricAlgebraPieceMap n φ)) where
  imageSieve_mem {U} y := by
    cases n with
    | negSucc k =>
        refine J.superset_covering (fun V g _ => ⟨0, ?_⟩) (J.top_mem U)
        exact (symPowInt_eq_zero_of_neg (Int.negSucc k) G (Int.negSucc_lt_zero k) (op V) _).trans
          (symPowInt_eq_zero_of_neg (Int.negSucc k) G (Int.negSucc_lt_zero k) (op V) _).symm
    | ofNat k =>
        have hy2 : (y.1 : SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj (op U))
            (G.obj (op U))) ∈
            SymPow.symmetricPower k ((O ⋙ forget₂ _ RingCat).obj (op U)) (G.obj (op U)) := y.2
        obtain ⟨S, hS, hz⟩ := locLift_of_mem J φ hφ k hy2
        refine J.superset_covering (fun V g hg => ?_) hS
        obtain ⟨z, hzmem, hzeq⟩ := hz g hg
        exact ⟨⟨z, hzmem⟩, Subtype.ext hzeq⟩

end LocallySurjective

end PresheafOfModules

namespace SheafOfModules

open PresheafOfModules Stacks Stacks.GradedAlgebra

/-! ### The symmetric powers of a morphism of sheaves of modules -/

section Epi

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {M₁ M : SheafOfModules.{w} (toRingCat J Osharp)} (p : M₁ ⟶ M)

/-- The degreewise morphism out of the sectionwise symmetric algebra of `M₁` into the symmetric
algebra of `M`: the sectionwise degree-`n` symmetric power of `p`, followed by the sheafification
unit. -/
noncomputable def symmetricDescFamily (n : ℤ) :
    symPowInt n M₁.val ⟶
      sheafifyRestrict (𝟙 (toRingCat J Osharp).obj) (symPowInt n M.val) :=
  symmetricAlgebraPieceMap n p.val ≫
    sheafifyUnit (𝟙 (toRingCat J Osharp).obj) (symPowInt n M.val)

/-- On sections, `SheafOfModules.symmetricDescFamily` is the sectionwise symmetric power of `p`
followed by the sheafification unit. -/
private theorem symmetricDescFamily_app (n : ℤ) (X : Cᵒᵖ) (x : (symPowInt n M₁.val).obj X) :
    Hom.app (symmetricDescFamily J p n) X x =
      Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj) (symPowInt n M.val)) X
        (Hom.app (symmetricAlgebraPieceMap n p.val) X x) := rfl

/-- `SheafOfModules.symmetricDescFamily` is multiplicative for the grading. -/
theorem symmetricDescFamily_mul (i j : ℤ) (X : Cᵒᵖ)
    (x : (symPowInt i M₁.val).obj X) (y : (symPowInt j M₁.val).obj X) :
    Hom.app (symmetricDescFamily J p (i + j)) X
        (((PresheafOfModules.symPowIntGradedAlgebra M₁.val).mul i j).app X x y) =
      ((sheafifiedSymmetricAlgebra J M).mul i j).app X
        (Hom.app (symmetricDescFamily J p i) X x) (Hom.app (symmetricDescFamily J p j) X y) := by
  rw [symmetricDescFamily_app, symmetricAlgebraPieceMap_mul]
  exact ((PresheafOfModules.symPowIntGradedAlgebra M.val).sheafify_mul_unit
    (𝟙 (toRingCat J Osharp).obj) i j X _ _).symm

/-- `SheafOfModules.symmetricDescFamily` carries the unit to the unit. -/
theorem symmetricDescFamily_one (X : Cᵒᵖ) :
    Hom.app (symmetricDescFamily J p 0) X
        ((PresheafOfModules.symPowIntGradedAlgebra M₁.val).one.eval X) =
      (sheafifiedSymmetricAlgebra J M).one.eval X := by
  rw [symmetricDescFamily_app]
  refine (congrArg _ (symmetricAlgebraPieceMap_one p.val X)).trans ?_
  exact ((PresheafOfModules.symPowIntGradedAlgebra M.val).sheafify_one_eval
    (𝟙 (toRingCat J Osharp).obj) X).symm

/-- **The symmetric powers of a morphism of sheaves of modules**, as the unique unital
homomorphism of graded algebras `Sym(M₁) ⟶ Sym(M)` extending the sectionwise symmetric powers of
`p` on unit images of local sections. -/
noncomputable def symmetricDescHom :
    GradedAlgebra.UnitalHom (sheafifiedSymmetricAlgebra J M₁) (sheafifiedSymmetricAlgebra J M) :=
  (Stacks.GradedAlgebra.existsUnique_desc (𝟙 (toRingCat J Osharp).obj)
    (PresheafOfModules.symPowIntGradedAlgebra M₁.val)
    (B := sheafifiedSymmetricAlgebra J M) (symmetricDescFamily J p)
    (symmetricDescFamily_mul J p) (symmetricDescFamily_one J p)).choose

/-- `SheafOfModules.symmetricDescHom` is the sectionwise symmetric power of `p` on the unit image
of a homogeneous local section. -/
theorem symmetricDescHom_unit (n : ℤ) (X : Cᵒᵖ)
    (s : (symPowInt n M₁.val).obj X) :
    ((symmetricDescHom J p).app n).val.app X
        (Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (symPowInt n M₁.val)) X s) =
      Hom.app (symmetricDescFamily J p n) X s :=
  (Stacks.GradedAlgebra.existsUnique_desc (𝟙 (toRingCat J Osharp).obj)
    (PresheafOfModules.symPowIntGradedAlgebra M₁.val)
    (B := sheafifiedSymmetricAlgebra J M) (symmetricDescFamily J p)
    (symmetricDescFamily_mul J p) (symmetricDescFamily_one J p)).choose_spec.1 n X s

/-- **The degree-`n` symmetric power of an epimorphism of sheaves of modules is an
epimorphism.** -/
theorem epi_symmetricDescHom_app [Epi p] (n : ℤ) : Epi ((symmetricDescHom J p).app n) := by
  have hp : Presheaf.IsLocallySurjective J
      ((toPresheaf (toRingCat J Osharp).obj).map p.val) :=
    Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi p
  have hpm := PresheafOfModules.isLocallySurjective_symmetricAlgebraPieceMap J p.val hp n
  have hls : Presheaf.IsLocallySurjective J
      ((toPresheaf (toRingCat J Osharp).obj).map (symmetricDescFamily J p n)) := by
    show Presheaf.IsLocallySurjective J ((toPresheaf (toRingCat J Osharp).obj).map
      (symmetricAlgebraPieceMap n p.val ≫
        sheafifyUnit (𝟙 (toRingCat J Osharp).obj) (symPowInt n M.val)))
    rw [Functor.map_comp]
    infer_instance
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective
    ((symmetricDescHom J p).app n) ⟨fun {U} x => ?_⟩
  refine J.superset_covering ?_ (hls.imageSieve_mem x)
  rintro V g ⟨t, ht⟩
  exact ⟨Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
    (symPowInt n M₁.val)) (op V) t,
    (symmetricDescHom_unit J p n (op V) t).trans ht⟩

/-- **The degree-one generator of `Sym(F)` on sections**: it carries a local section of `F` to
the unit image of its sectionwise degree-one generator. This is the symmetric counterpart of
`SheafOfModules.sheafifiedTensorGenerator_apply`. -/
theorem sheafifiedSymmetricGenerator_apply (F : SheafOfModules.{w} (toRingCat J Osharp))
    (U : Cᵒᵖ) (s : F.val.obj U) :
    (sheafifiedSymmetricGenerator J F).val.app U s =
      Hom.app (sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
        (symPowInt 1 F.val)) U (Hom.app (symPowIntGen F.val) U s) := by
  rw [show (sheafifiedSymmetricGenerator J F).val.app U s =
      Hom.app (((PresheafOfModules.symPowIntGradedAlgebra F.val).sheafifyGen
          (𝟙 (toRingCat J Osharp).obj) (symPowIntGen F.val)).val) U
        ((sheafifiedValIso J F).inv.val.app U s) from rfl,
    sheafifiedValIso_inv_apply]
  exact (PresheafOfModules.symPowIntGradedAlgebra F.val).sheafifyGen_unit
    (𝟙 (toRingCat J Osharp).obj) (symPowIntGen F.val) U s

/-- `SheafOfModules.symmetricDescHom` extends `p` on the degree-one generators. -/
theorem symmetricDescHom_gen :
    sheafifiedSymmetricGenerator J M₁ ≫ (symmetricDescHom J p).app 1 =
      p ≫ sheafifiedSymmetricGenerator J M := by
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
  show ((symmetricDescHom J p).app 1).val.app U
      ((sheafifiedSymmetricGenerator J M₁).val.app U s) =
    (sheafifiedSymmetricGenerator J M).val.app U (p.val.app U s)
  rw [sheafifiedSymmetricGenerator_apply, symmetricDescHom_unit,
    sheafifiedSymmetricGenerator_apply]
  rw [symmetricDescFamily_app, PresheafOfModules.symmetricAlgebraPieceMap_gen]

/-- **`SheafOfModules.symmetricDescHom` is the homomorphism of graded algebras that the universal
property of the symmetric algebra produces from `p`**, which is the second map of the sequence of
Tag 01CJ. -/
theorem symmetricDescHom_eq_descComp :
    symmetricDescHom J p =
      (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J M₁).isUniversal.descComp p
        (sheafifiedSymmetricGenerator J M)
        (GradedAlgebra.pairwiseCommutes_comp p
          (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J M).isUniversal.1) :=
  GradedAlgebra.IsUniversal.descComp_unique _ p _ _ (symmetricDescHom_gen J p)

/-- **The second map of the sequence of Tag 01CJ is an epimorphism in every degree**: the
degree-`n` symmetric power of an epimorphism of sheaves of modules is an epimorphism. Exactness
at the middle term is not proved; see the module documentation. -/
theorem epi_descComp_app_symmetric [Epi p] (n : ℤ) :
    Epi (((isSymmetricAlgebra_sheafifiedSymmetricAlgebra J M₁).isUniversal.descComp
      p (sheafifiedSymmetricGenerator J M)
      (GradedAlgebra.pairwiseCommutes_comp p
        (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J M).isUniversal.1)).app n) := by
  rw [← symmetricDescHom_eq_descComp]
  exact epi_symmetricDescHom_app J p n

end Epi

/-! ### Symmetric powers of a sheafification -/

section Sheafify

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The degree-`n` piece of the sheafification of the sectionwise symmetric algebra of a
presheaf of modules `Q` is the degree-`n` symmetric power of the sheaf of modules `Q` sheafifies
to.** Both are symmetric algebras of `G` in the sense of
`SheafOfModules.GradedAlgebra.IsSymmetricAlgebra`, and a symmetric algebra is unique up to a
canonical isomorphism in every degree. -/
noncomputable def symmetricPieceSheafifyIso
    (Q : PresheafOfModules.{w} ((toRingCat J Osharp).obj))
    (G : SheafOfModules.{w} (toRingCat J Osharp))
    (e : G ≅ (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj Q) (n : ℤ) :
    ((PresheafOfModules.symPowIntGradedAlgebra Q).sheafify
        (𝟙 (toRingCat J Osharp).obj)).piece n ≅
      (sheafifiedSymmetricAlgebra J G).piece n :=
  (GradedAlgebra.isSymmetricAlgebra_ofIso e
    (PresheafOfModules.isSymmetricAlgebra_sheafify_symmetricAlgebra
      (𝟙 (toRingCat J Osharp).obj) Q)).pieceIso
    (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J G) n

/-- A presentation of the sheafified sectionwise symmetric power of a presheaf of modules is a
presentation of the symmetric power of the sheaf it sheafifies to. -/
noncomputable def presentation_sheafifiedSymmetricPiece_of_sheafifyIso
    [HasSheafify J AddCommGrpCat.{w}]
    (Q : PresheafOfModules.{w} ((toRingCat J Osharp).obj))
    (G : SheafOfModules.{w} (toRingCat J Osharp))
    (e : G ≅ (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj Q) (n : ℤ)
    (hQ : (((PresheafOfModules.symPowIntGradedAlgebra Q).sheafify
      (𝟙 (toRingCat J Osharp).obj)).piece n).Presentation) :
    ((sheafifiedSymmetricAlgebra J G).piece n).Presentation :=
  SheafOfModules.Presentation.ofIsIso (symmetricPieceSheafifyIso J Q G e n).hom hQ

/-- Quasi-coherence of the sheafified sectionwise symmetric power of a presheaf of modules is
quasi-coherence of the symmetric power of the sheaf it sheafifies to. -/
theorem isQuasicoherent_sheafifiedSymmetricPiece_of_sheafifyIso
    [HasBinaryProducts C] [HasSheafify J AddCommGrpCat.{w}]
    [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{w}]
    [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{w}]
    [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (Q : PresheafOfModules.{w} ((toRingCat J Osharp).obj))
    (G : SheafOfModules.{w} (toRingCat J Osharp))
    (e : G ≅ (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj Q) (n : ℤ)
    (hQ : (((PresheafOfModules.symPowIntGradedAlgebra Q).sheafify
      (𝟙 (toRingCat J Osharp).obj)).piece n).IsQuasicoherent) :
    ((sheafifiedSymmetricAlgebra J G).piece n).IsQuasicoherent :=
  (isQuasicoherent (toRingCat J Osharp)).prop_of_iso (symmetricPieceSheafifyIso J Q G e n) hQ

end Sheafify

end SheafOfModules

end
