module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineSections
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineStalk
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSheafAffine
public import StacksFrontier.RingTheory.NaiveCotangent.LocalizationBaseAndTarget

/-!
# The comparison map of Stacks 0D0I on sections, and its germ at a point

Let `f : X ⟶ Y` be a morphism of schemes, let `U` be an open of `Y` and `V` an open of `X` with
`V ⊆ f^{-1}U`, and write `R = Γ(Y, U)` and `A = Γ(X, V)`.  This file builds the canonical map of
two-term complexes of `A`-modules

`NL_{A/R} ⟶ NL_{X/Y}(V)`

whose adjoint is the canonical map `(NL_{A/R})~ ⟶ NL_{X/Y}|_V` of Stacks 0D0I, and the
morphism of extensions which is its germ at a point of `V`.

The comparison `Stacks.NaiveCotangentAffineSections.sectionsComparison` starts not from
`NL_{A/R}` but from `NL_{A/(f^{-1}𝒪_Y)(V)}`: the naive cotangent complex `NL_{X/Y}` is the one
of the structural morphism `f^{-1}𝒪_Y ⟶ 𝒪_X`, so taking sections over `V` produces the base ring
`(f^{-1}𝒪_Y)(V)` and not `R`.  What is added here is the missing leg, the change of base along
the canonical ring map `R ⟶ (f^{-1}𝒪_Y)(V)`, together with the identification of the composite
`R ⟶ (f^{-1}𝒪_Y)(V) ⟶ A` with `f.appLE U V` that makes the two legs composable.

At the stalks the same device supplies the canonical morphism of extensions, built from the
commuting square of germ maps, at which the quasi-isomorphy statement of
`Stacks.NaiveCotangentAffineStalk` — which holds for *every* morphism of extensions, any two being
homotopic — is instantiated.

## Main definitions

* `Stacks.NaiveCotangentAffineComparison.baseChangeSelfHom` is the morphism of extensions
  `Generators.self R A ⟶ Generators.self R' A` along a change of base `R ⟶ R'`, for `A` an
  `R'`-algebra with the tower `R → R' → A`, and
  `Stacks.NaiveCotangentAffineComparison.nlBaseChangeSelf` is the chain map
  `NL_{A/R} ⟶ NL_{A/R'}` it induces.
* `Stacks.NaiveCotangentAffineComparison.squareRingHom` and
  `Stacks.NaiveCotangentAffineComparison.selfSquareHom` are the same for a commutative square of
  rings `R → S`, `R → R'`, `R' → S'`, `S → S'`, where the target algebra changes too: the
  morphism of extensions `Generators.self R S ⟶ Generators.self R' S'`.  All of these are stated
  over abstract rings: no concrete polynomial ring occurs in them, which is what keeps the
  `Algebra` instances on the extension's ring findable.
* `Stacks.NaiveCotangentAffineComparison.baseSectionHom` is the canonical ring map
  `Γ(Y, U) ⟶ (f^{-1}𝒪_Y)(V)`, the unit of `f^{-1} ⊣ f_*` on sections restricted to `V`, and
  `Stacks.NaiveCotangentAffineComparison.algebraBaseSection` is the algebra structure it gives;
  `Stacks.NaiveCotangentAffineComparison.algebraAppLE'` is the algebra structure of `Γ(Y, U)` on
  `Γ(X, V)` through `f.appLE`, declared at the spelling of the section ring that the site-level
  comparison uses.
* `Stacks.NaiveCotangentAffineComparison.sectionsBaseComparison` is the comparison map
  `NL_{Γ(X,V)/Γ(Y,U)} ⟶ NL_{X/Y}(V)` of `Γ(X, V)`-modules.
* `Stacks.NaiveCotangentAffineComparison.canonicalStalkHom` is the morphism of extensions
  `Generators.self Γ(Y,U) Γ(X,V) ⟶ Generators.self (f^{-1}𝒪_Y)_x 𝒪_{X,x}` at a point `x ∈ V`
  with `f x ∈ U`, the germ at `x` of the comparison of Stacks 0D0I.

## Main results

* `Stacks.NaiveCotangentAffineComparison.structureMap_baseSectionHom`: the structural map
  `f^{-1}𝒪_Y ⟶ 𝒪_X` carries the canonical section of `f^{-1}𝒪_Y` attached to `r ∈ Γ(Y, U)` to
  the image of `r` under `f.appLE U V`.  This is `Stacks.Smooth`'s computation of the unit, and
  it is what makes the tower `Γ(Y, U) → (f^{-1}𝒪_Y)(V) → Γ(X, V)` hold.
* `Stacks.NaiveCotangentAffineComparison.isScalarTower_baseSection`: that tower.
* `Stacks.NaiveCotangentAffineComparison.aeval_id_squareRingHom`: evaluation of polynomials
  commutes with a commutative square of rings.  This is the one computation behind
  `selfSquareHom`.
* `Stacks.NaiveCotangentAffineComparison.sectionsBaseComparison_f₁` and
  `Stacks.NaiveCotangentAffineComparison.sectionsBaseComparison_f₀`: the two components of the
  comparison are the functorial maps `Algebra.Extension.Cotangent.map` and
  `Algebra.Extension.CotangentSpace.map` of the change of base, followed by the two components
  of the comparison on sections.  Together with
  `Stacks.SheafOfModules.sectionsConormalComparison_mk` and
  `Stacks.SheafOfModules.sectionsTensorComparison_tmul` they pin the comparison down: in degree
  `-1` the class of a polynomial `g` over `R` in the kernel of `R[A] ⟶ A` goes to the conormal
  class of the section `λ(g)` of the kernel of `f^{-1}𝒪_Y[𝒪_X] ⟶ 𝒪_X` over `V`, the coefficients
  of `g` being first carried into `(f^{-1}𝒪_Y)(V)`; in degree `0` the element `b ⊗ d p` goes to
  `b • (1 ⊗ d (λ p))`.
* `Stacks.NaiveCotangentAffineComparison.isQuasiIso_nlExtensionBaseChangeMap_canonicalStalkHom`:
  for `U` and `V` affine, the canonical map
  `NL_{A/R} ⊗_A 𝒪_{X,x} ⟶ NL_{𝒪_{X,x}/(f^{-1}𝒪_Y)_x}` is a quasi-isomorphism.  This is
  `Stacks.NaiveCotangentAffineStalk.isQuasiIso_nlExtensionBaseChangeMap_stalkInverseImage` with
  its universally quantified morphism of extensions instantiated at `canonicalStalkHom`.

## Implementation notes

**Two readings of the section ring.**  `Γ(X, V)` means `X.presheaf.obj (op V)`, while the
site-level comparison is stated over `X.sheaf.obj.obj (op V)`.  The two are the same term up to
`rfl` but not syntactically, and an `Algebra` instance declared at one of them is not found for
the other: instance search reports a missing `SMul`.  The comparison on sections is therefore
stated in the second spelling, and
`Stacks.NaiveCotangentAffineComparison.algebraAppLE'` is
`Stacks.NaiveCotangentAffineStalk.algebraAppLE` declared at it.  The equality of the two
spellings is recorded as `section_eq_sheaf_section`, by `rfl`.  The stalk statements keep the
first spelling, which is the one `Stacks.NaiveCotangentAffineStalk` uses.

**Why the changes of base are stated abstractly.**  The underlying map of
`baseChangeSelfHom` is `MvPolynomial.map (algebraMap R R')` and that of `selfSquareHom` is an
`MvPolynomial.eval₂Hom`, but both are stated for abstract rings: with the scheme-theoretic rings
substituted, the `Algebra (Generators.self R A).toExtension.Ring A` instance needed to even state
the two conditions of `Algebra.Extension.Hom` is not found by instance search, the polynomial
ring being reached only through `Algebra.Extension.Ring`.  For the same reason the evaluation
computation is isolated as `aeval_id_squareRingHom`, where the two polynomial rings are visible
as `MvPolynomial`: stated through `Algebra.Extension.Ring` the goal is rejected as not
type-correct under the implicit transparency level, and the second condition of `selfSquareHom`
is then discharged by an explicit `Eq.trans` of `Algebra.Generators.algebraMap_apply` rather than
by a rewrite.

**The sheaf-level map.**  The map `(NL_{A/R})~ ⟶ NL_{X/Y}|_V` of Stacks 0D0I is the adjoint of
the `A`-linear comparison of complexes built here: by `AlgebraicGeometry.tilde.adjunction`
(Stacks 01I7), equivalently by `Stacks.AssociatedSheaf.associatedSheafAdjunction` (Stacks 01BH,
clause (4)), a map out of `(NL_{A/R})~` in each degree is exactly an `A`-linear map of `NL_{A/R}`
into the sections, which is what `Stacks.NaiveCotangentAffineComparison.sectionsBaseComparison`
provides; and the germ of that map is `canonicalStalkHom`, at which the stalkwise
quasi-isomorphy is recorded above.

## References

* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I), of whose proof this is
  a step.
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW), the naive cotangent
  complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7), the mapping property of
  the sheaf associated to a module on an affine scheme.
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH), the sheaf associated to
  a module and a ring map to global sections.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.Sheaves.RingedSpaceDifferentials

universe u

noncomputable section

namespace Stacks.NaiveCotangentAffineComparison

/-! ### The change of base of the canonical presentation -/

section BaseChangeSelf

variable {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
  [Algebra R A] [Algebra R R'] [Algebra R' A] [IsScalarTower R R' A]

/-- **The canonical presentation of `A` over `R` maps to the one over `R'`.**  For a tower
`R → R' → A` the morphism of extensions `Generators.self R A ⟶ Generators.self R' A` which is
the identity on the variables: on the polynomial rings it is `MvPolynomial.map` of the structural
map `R → R'`. -/
def baseChangeSelfHom :
    (Algebra.Generators.self R A).toExtension.Hom
      (Algebra.Generators.self R' A).toExtension where
  toRingHom := MvPolynomial.map (algebraMap R R')
  toRingHom_algebraMap _ := MvPolynomial.map_C _ _
  algebraMap_toRingHom _ := MvPolynomial.aeval_map_algebraMap _ _ _

/-- The underlying map of polynomial rings of
`Stacks.NaiveCotangentAffineComparison.baseChangeSelfHom` is `MvPolynomial.map` of the structural
map `R → R'`. -/
theorem baseChangeSelfHom_toRingHom :
    (baseChangeSelfHom (R := R) (R' := R') (A := A)).toRingHom =
      MvPolynomial.map (algebraMap R R') :=
  rfl

/-- **The naive cotangent complex of a change of base of the canonical presentation.**  The
chain map `NL_{A/R} ⟶ NL_{A/R'}` of two-term complexes of `A`-modules induced by
`Stacks.NaiveCotangentAffineComparison.baseChangeSelfHom`.  Both complexes are complexes of
`A`-modules, so neither a restriction of scalars nor a tensor product is involved. -/
def nlBaseChangeSelf :
    NaiveCotangent.ChainMap (NaiveCotangent.NL (Algebra.Generators.self R A))
      (NaiveCotangent.NL (Algebra.Generators.self R' A)) :=
  NaiveCotangent.nlExtensionOverMap (baseChangeSelfHom (R := R) (R' := R') (A := A))

/-- **The change of base in degree `-1`** is `Algebra.Extension.Cotangent.map`, so by
`Algebra.Extension.Cotangent.map_mk` the class of an element `g` of the kernel of `R[A] ⟶ A`
goes to the class of the image of `g` in the kernel of `R'[A] ⟶ A`. -/
theorem nlBaseChangeSelf_f₁ :
    (nlBaseChangeSelf (R := R) (R' := R') (A := A)).f₁ =
      Algebra.Extension.Cotangent.map (baseChangeSelfHom (R := R) (R' := R') (A := A)) :=
  rfl

/-- **The change of base in degree `0`** is `Algebra.Extension.CotangentSpace.map`, so by
`Algebra.Extension.CotangentSpace.map_tmul` the element `b ⊗ d p` goes to `b ⊗ d` of the image
of `p`. -/
theorem nlBaseChangeSelf_f₀ :
    (nlBaseChangeSelf (R := R) (R' := R') (A := A)).f₀ =
      Algebra.Extension.CotangentSpace.map (baseChangeSelfHom (R := R) (R' := R') (A := A)) :=
  rfl

end BaseChangeSelf

/-! ### The morphism of canonical presentations attached to a square of rings -/

section SelfSquare

variable {R R' S S' : Type u} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
  [Algebra R S] [Algebra R' S'] [Algebra R R'] [Algebra S S']

/-- **The polynomial map of a square of rings.**  The map `R[S] ⟶ R'[S']` sending the variable
`X_s` to `X_{s'}`, for `s'` the image of `s`, and acting on coefficients by `R ⟶ R'`. -/
def squareRingHom : MvPolynomial S R →+* MvPolynomial S' R' :=
  MvPolynomial.eval₂Hom ((MvPolynomial.C : R' →+* MvPolynomial S' R').comp (algebraMap R R'))
    (fun s : S => (MvPolynomial.X (algebraMap S S' s) : MvPolynomial S' R'))

/-- **Evaluation commutes with the square.**  Evaluating the image of `p` under
`Stacks.NaiveCotangentAffineComparison.squareRingHom` at the variables of `S'` is the image under
`S ⟶ S'` of the evaluation of `p` at the variables of `S`, provided the square of rings
commutes.  This is the computation behind
`Stacks.NaiveCotangentAffineComparison.selfSquareHom`. -/
theorem aeval_id_squareRingHom
    (hsq : ∀ r : R, algebraMap S S' (algebraMap R S r) = algebraMap R' S' (algebraMap R R' r))
    (p : MvPolynomial S R) :
    MvPolynomial.aeval (R := R') (id : S' → S') (squareRingHom (R := R) (S := S) p) =
      algebraMap S S' (MvPolynomial.aeval (R := R) (id : S → S) p) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    simp only [squareRingHom, MvPolynomial.eval₂Hom_C, RingHom.coe_comp, Function.comp_apply,
      MvPolynomial.aeval_C]
    exact (hsq r).symm
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s hp =>
    simp only [squareRingHom, map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.aeval_X, id_eq] at *
    rw [hp]

/-- **The morphism of canonical presentations attached to a commutative square of rings.**  For
a square `R → S`, `R → R'`, `R' → S'`, `S → S'` which commutes on `R`, the morphism of
extensions `Generators.self R S ⟶ Generators.self R' S'`.

This is the morphism of extensions whose induced comparison
`NL_{S/R} ⊗_S S' ⟶ NL_{S'/R'}` the quasi-isomorphism statements about
`NaiveCotangent.nlExtensionBaseChangeMap` are about; those statements are quantified over every
such morphism, any two being homotopic, so this construction is what makes them applicable. -/
def selfSquareHom
    (hsq : ∀ r : R, algebraMap S S' (algebraMap R S r) = algebraMap R' S' (algebraMap R R' r)) :
    (Algebra.Generators.self R S).toExtension.Hom
      (Algebra.Generators.self R' S').toExtension where
  toRingHom := squareRingHom
  toRingHom_algebraMap r := MvPolynomial.eval₂Hom_C _ _ r
  algebraMap_toRingHom p :=
    Eq.trans (Algebra.Generators.algebraMap_apply (Algebra.Generators.self R' S') _)
      (Eq.trans (aeval_id_squareRingHom hsq p)
        (congrArg (algebraMap S S')
          (Algebra.Generators.algebraMap_apply (Algebra.Generators.self R S) p).symm))

end SelfSquare


variable {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (hVU : V ≤ f ⁻¹ᵁ U)

/-! ### The canonical map `Γ(Y, U) ⟶ (f^{-1}𝒪_Y)(V)` -/

/-- **The two readings of the section ring agree.**  `Γ(X, V)`, which is
`X.presheaf.obj (op V)`, is the ring `X.sheaf.obj.obj (op V)` over which the site-level
comparison of `Stacks.SheafOfModules.sectionsNaiveCotangentComparison` is stated.  The two are
not syntactically equal, so an `Algebra` instance declared at one of them is not found at the
other; this records that no mathematics separates them. -/
theorem section_eq_sheaf_section : X.presheaf.obj (op V) = X.sheaf.obj.obj (op V) := rfl

/-- **The canonical ring map `Γ(Y, U) ⟶ (f^{-1}𝒪_Y)(V)`** for `V ⊆ f^{-1}U`: the unit of the
adjunction `f^{-1} ⊣ f_*` of sheaves of rings, evaluated on `U` and restricted to `V`.  Its
underlying function is `Stacks.Smooth.inverseImageSection`. -/
def baseSectionHom :
    Γ(Y, U) →+* ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).obj.obj (op V)) :=
  ((inverseImageSheaf (Stacks.Smooth.ringedSpaceHom f)).obj.map (homOfLE hVU).op).hom.comp
    ((Stacks.Smooth.inverseImageUnit f).hom.app (op U)).hom

/-- `Stacks.NaiveCotangentAffineComparison.baseSectionHom` is
`Stacks.Smooth.inverseImageSection`. -/
theorem baseSectionHom_apply (r : Γ(Y, U)) :
    baseSectionHom f hVU r = Stacks.Smooth.inverseImageSection f V hVU r :=
  rfl

/-- **`(f^{-1}𝒪_Y)(V)` as an algebra over `Γ(Y, U)`**, through
`Stacks.NaiveCotangentAffineComparison.baseSectionHom`.  This is the base of the change of base
that the comparison of Stacks 0D0I needs. -/
abbrev algebraBaseSection :
    Algebra Γ(Y, U)
      ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).obj.obj (op V)) :=
  (baseSectionHom f hVU).toAlgebra

/-- **`Γ(X, V)` as an algebra over `Γ(Y, U)`**, through the restriction `f.appLE` of `f` to the
two opens.  This is `Stacks.NaiveCotangentAffineStalk.algebraAppLE` declared at the ring
`X.sheaf.obj.obj (op V)`, the spelling the site-level comparison uses. -/
abbrev algebraAppLE' : Algebra Γ(Y, U) ↑(X.sheaf.obj.obj (op V)) :=
  (f.appLE U V hVU).hom.toAlgebra

/-- **The structural map carries the canonical section to the restriction of `f`.**  The
structural morphism `f^{-1}𝒪_Y ⟶ 𝒪_X` sends the canonical section over `V` attached to
`r ∈ Γ(Y, U)` to the image of `r` under `f.appLE U V`.  This is
`Stacks.Smooth.inverseImageStructureMap_inverseImageSection`, and it is the triangle that makes
the change of base of the canonical presentation composable with the comparison on sections. -/
theorem structureMap_baseSectionHom (r : Γ(Y, U)) :
    ((AlgebraicGeometry.inverseImageStructureMap f).hom.app (op V)).hom
        (baseSectionHom f hVU r) = (f.appLE U V hVU).hom r :=
  Stacks.Smooth.inverseImageStructureMap_inverseImageSection f V hVU r

/-- **The scalar tower `Γ(Y, U) → (f^{-1}𝒪_Y)(V) → Γ(X, V)`**, which is
`Stacks.NaiveCotangentAffineComparison.structureMap_baseSectionHom`. -/
theorem isScalarTower_baseSection :
    letI := algebraAppLE' f hVU
    letI := algebraBaseSection f hVU
    letI := Stacks.NaiveCotangentAffineSections.algebraSections f V
    IsScalarTower Γ(Y, U)
      ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).obj.obj (op V))
      ↑(X.sheaf.obj.obj (op V)) := by
  let := algebraAppLE' f hVU
  let := algebraBaseSection f hVU
  let := Stacks.NaiveCotangentAffineSections.algebraSections f V
  exact IsScalarTower.of_algebraMap_eq fun r => (structureMap_baseSectionHom f hVU r).symm

/-! ### The comparison map on sections -/

/-- **The comparison map `NL_{Γ(X,V)/Γ(Y,U)} ⟶ NL_{X/Y}(V)`**, whose adjoint is the canonical
map `(NL_{A/R})~ ⟶ NL_{X/Y}|_V` of Stacks 0D0I.  It is the change of base of the canonical
presentation of `Γ(X, V)` along `Γ(Y, U) ⟶ (f^{-1}𝒪_Y)(V)`, followed by the comparison on
sections `Stacks.NaiveCotangentAffineSections.sectionsComparison` of the naive cotangent complex
of the structural morphism `f^{-1}𝒪_Y ⟶ 𝒪_X`.

No affineness of `U` or of `V` is needed: as in
`Stacks.NaiveCotangentAffineSections.sectionsComparison`, the construction uses only the
inclusion `V ⊆ f^{-1}U`. -/
def sectionsBaseComparison :
    letI := algebraAppLE' f hVU
    letI := algebraBaseSection f hVU
    letI := Stacks.NaiveCotangentAffineSections.algebraSections f V
    haveI := isScalarTower_baseSection f hVU
    NaiveCotangent.ChainMap
      (NaiveCotangent.NL (Algebra.Generators.self Γ(Y, U) ↑(X.sheaf.obj.obj (op V))))
      (Stacks.NaiveCotangentAffineSections.naiveCotangentSections f V) := by
  let := algebraAppLE' f hVU
  let := algebraBaseSection f hVU
  let := Stacks.NaiveCotangentAffineSections.algebraSections f V
  have _ := isScalarTower_baseSection f hVU
  exact (Stacks.NaiveCotangentAffineSections.sectionsComparison f V).comp nlBaseChangeSelf

/-- **The comparison in degree `-1`.**  It is the functorial map of the change of base of the
canonical presentation followed by the degree `-1` comparison on sections; combined with
`Algebra.Extension.Cotangent.map_mk` and
`Stacks.SheafOfModules.sectionsConormalComparison_mk` this says that the class of a polynomial
`g` over `Γ(Y, U)` in the kernel of `Γ(Y,U)[A] ⟶ A` goes to the conormal class of the section
`λ(g)` of the kernel of `f^{-1}𝒪_Y[𝒪_X] ⟶ 𝒪_X` over `V`. -/
theorem sectionsBaseComparison_f₁ :
    letI := algebraAppLE' f hVU
    letI := algebraBaseSection f hVU
    letI := Stacks.NaiveCotangentAffineSections.algebraSections f V
    haveI := isScalarTower_baseSection f hVU
    (sectionsBaseComparison f hVU).f₁ =
      Stacks.NaiveCotangentAffineSections.sectionsConormalComparison f V ∘ₗ
        Algebra.Extension.Cotangent.map (baseChangeSelfHom
          (R := Γ(Y, U))
          (R' := ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).obj.obj (op V)))
          (A := ↑(X.sheaf.obj.obj (op V)))) := by
  rfl

/-- **The comparison in degree `0`.**  It is the functorial map of the change of base of the
canonical presentation followed by the degree `0` comparison on sections; combined with
`Algebra.Extension.CotangentSpace.map_tmul` and
`Stacks.SheafOfModules.sectionsTensorComparison_tmul` this says that `b ⊗ d p` goes to
`b • (1 ⊗ d (λ p))`, the coefficients of `p` being first carried into `(f^{-1}𝒪_Y)(V)`. -/
theorem sectionsBaseComparison_f₀ :
    letI := algebraAppLE' f hVU
    letI := algebraBaseSection f hVU
    letI := Stacks.NaiveCotangentAffineSections.algebraSections f V
    haveI := isScalarTower_baseSection f hVU
    (sectionsBaseComparison f hVU).f₀ =
      Stacks.NaiveCotangentAffineSections.sectionsTensorComparison f V ∘ₗ
        Algebra.Extension.CotangentSpace.map (baseChangeSelfHom
          (R := Γ(Y, U))
          (R' := ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).obj.obj (op V)))
          (A := ↑(X.sheaf.obj.obj (op V)))) := by
  rfl

/-! ### The morphism of extensions at a point of an affine open -/

section Stalk

variable {x : X} (hx : x ∈ V) (hfx : f x ∈ U)

/-- **The canonical morphism of extensions at a point.**  For `x ∈ V` with `f x ∈ U`, the
morphism of extensions

`Generators.self Γ(Y, U) Γ(X, V) ⟶ Generators.self (f^{-1}𝒪_Y)_x 𝒪_{X,x}`

attached to the square of rings `Γ(Y, U) → Γ(X, V) → 𝒪_{X,x}` and
`Γ(Y, U) → (f^{-1}𝒪_Y)_x → 𝒪_{X,x}`, which commutes by
`Stacks.NaiveCotangentAffineStalk.germ_comp_appLE_inverseImage`.

This is the morphism of extensions whose comparison
`NL_{Γ(X,V)/Γ(Y,U)} ⊗_{Γ(X,V)} 𝒪_{X,x} ⟶ NL_{𝒪_{X,x}/(f^{-1}𝒪_Y)_x}` is the germ at `x` of the
map of Stacks 0D0I.  `Stacks.NaiveCotangentAffineStalk`'s stalk statement is quantified over
every such morphism — any two are homotopic, so quasi-isomorphy does not depend on the choice —
and this is the canonical one, which is what makes that statement applicable. -/
def canonicalStalkHom :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f hfx
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x)
    (Algebra.Generators.self Γ(Y, U) Γ(X, V)).toExtension.Hom
      (Algebra.Generators.self
        ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x)
        ↑(X.presheaf.stalk x)).toExtension := by
  let := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  let := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f hfx
  let := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x)
  exact selfSquareHom fun r => DFunLike.congr_fun
    (Stacks.NaiveCotangentAffineStalk.germ_comp_appLE_inverseImage f hVU hx hfx) r

/-- **The stalkwise step of Stacks 0D0I at the canonical morphism of extensions.**  Let
`f : X ⟶ Y` be a morphism of schemes, let `Spec R = U ⊆ Y` and `Spec A = V ⊆ X` be affine opens
with `V ⊆ f^{-1}U`, and let `x ∈ V`.  Then the canonical map of two-term complexes of
`𝒪_{X,x}`-modules

`NL_{A/R} ⊗_A 𝒪_{X,x} ⟶ NL_{𝒪_{X,x}/(f^{-1}𝒪_Y)_x}`

is a quasi-isomorphism.

This is
`Stacks.NaiveCotangentAffineStalk.isQuasiIso_nlExtensionBaseChangeMap_stalkInverseImage` with its
universally quantified morphism of extensions instantiated at
`Stacks.NaiveCotangentAffineComparison.canonicalStalkHom`, which is the germ at `x` of the
comparison of Stacks 0D0I. -/
theorem isQuasiIso_nlExtensionBaseChangeMap_canonicalStalkHom
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
    letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImage f hfx
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkOfAppLE f hVU hx
    letI := Stacks.NaiveCotangentAffineStalk.algebraStalkInverseImageStructureMap f (x := x)
    haveI : IsScalarTower Γ(Y, U) Γ(X, V) ↑(X.presheaf.stalk x) :=
      Stacks.NaiveCotangentAffineStalk.isScalarTower_appLE f hVU hx
    haveI : IsScalarTower Γ(Y, U)
        ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).presheaf.stalk x)
        ↑(X.presheaf.stalk x) :=
      Stacks.NaiveCotangentAffineStalk.isScalarTower_stalkInverseImage f hVU hx hfx
    NaiveCotangent.IsQuasiIso
      (NaiveCotangent.nlExtensionBaseChangeMap (T := ↑(X.presheaf.stalk x))
        (canonicalStalkHom f hVU hx hfx)) := by
  exact Stacks.NaiveCotangentAffineStalk.isQuasiIso_nlExtensionBaseChangeMap_stalkInverseImage
    f hVU hx hfx hU hV _

end Stalk

end Stacks.NaiveCotangentAffineComparison

end

end
