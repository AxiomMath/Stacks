module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.AffineCase
public import StacksFrontier.RingTheory.Etale.StandardPresentationSolutions

/-!
# A representable functor on an affine base, as the equalizer of two maps of structure sheaves

Let `Y = Spec B` be an affine scheme and let `V = Spec C` be an affine scheme over `Y` equipped
with a *standard presentation* `C = B[x₁, …, x_n]/(P₁, …, P_n)` over `B`.  For any scheme `U`
over `Y` the set of `Y`-morphisms `U ⟶ V` is then

`Hom_Y(U, V) ≃ {a : Fin n → Γ(U, ⊤) // ∀ j, (Pⱼ)(a) = 0}`,

the solutions over `Γ(U, ⊤)` of the system obtained from the `Pⱼ` by pushing their coefficients
along `Γ(Y, ⊤) ⟶ Γ(U, ⊤)`, and this bijection is natural in `U`.  Equivalently: the functor
`U ↦ Hom_Y(U, V)` is the *equalizer* of the two maps `∏ᵢ 𝒪_Y ⇉ ∏ⱼ 𝒪_Y` given by
`a ↦ (Pⱼ(a))ⱼ` and by the zero section.

This is step (2) of the proof of [Stacks Project, Tag 04I6]: restricted to étale charts `U` of
`Y`, the representable sheaf `h_V` on `Y_étale` is the equalizer of two maps `∏ᵢ 𝒪_Y ⇉ ∏ⱼ 𝒪_Y`.

Étaleness of `V ⟶ Y` is not assumed. The standard presentation is supplied as data; for `V ⟶ Y`
étale it exists by [Stacks Project, Tag 00U9], available as Mathlib's
`Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`.

## Main definitions

* `Stacks.EtaleCohomology.homOverEquivAppTopOver` — the relative form of [Stacks Project,
  Tag 01I1] for an affine base: `Y`-morphisms `U ⟶ V` into an affine `V` are the ring maps
  `Γ(V, ⊤) ⟶ Γ(U, ⊤)` compatible with the two structure maps from `Γ(Y, ⊤)`.
* `Stacks.EtaleCohomology.homOverEquivSolutions` — **the equalizer presentation**: with a
  standard presentation of `Γ(V, ⊤)` over `Γ(Y, ⊤)` supplied, `Y`-morphisms `U ⟶ V` are the
  solutions over `Γ(U, ⊤)` of the presented system.

## Main results

* `Stacks.EtaleCohomology.homOverEquivSolutions_naturality` — the presentation is natural in the
  chart `U`: precomposing a `Y`-morphism with `k : U' ⟶ U` applies `k` to the solution it names,
  coordinatewise.  This is what makes the presentation one of the representable *sheaf* and not
  merely of one of its sets of sections.
* `Stacks.EtaleCohomology.isSolution_iff_eq_zero` — the solution condition is the equation
  between the two maps `Γ(U, ⊤)ⁿ ⇉ Γ(U, ⊤)ⁿ` whose equalizer the source names.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.EtaleCohomology

variable {Y : Scheme.{u}} [IsAffine Y]

/-- **The relative form of [Stacks Project, Tag 01I1] over an affine base.**  For `U` and `V`
schemes over an affine `Y` with `V` affine, the morphisms `U ⟶ V` over `Y` are exactly the ring
maps `Γ(V, ⊤) ⟶ Γ(U, ⊤)` which carry the structure map of `V` to that of `U`.

Both affineness hypotheses are used: that of `V` to turn a ring map into a morphism of schemes,
and that of `Y` to see that a morphism of schemes over `Y` is determined, among morphisms to `Y`,
by what it does on global functions. -/
def homOverEquivAppTopOver (U V : Scheme.{u}) [IsAffine V] (pV : V ⟶ Y) (pU : U ⟶ Y) :
    {f : U ⟶ V // f ≫ pV = pU} ≃
      {φ : Γ(V, ⊤) ⟶ Γ(U, ⊤) // pV.appTop ≫ φ = pU.appTop} where
  toFun f := ⟨f.1.appTop, by rw [← Scheme.Hom.comp_appTop, f.2]⟩
  invFun φ := ⟨schemeHomOfAppTop U V φ.1, by
    refine (schemeHomEquivAppTop U Y).injective ?_
    rw [schemeHomEquivAppTop_apply, schemeHomEquivAppTop_apply, Scheme.Hom.comp_appTop,
      appTop_schemeHomOfAppTop]
    exact φ.2⟩
  left_inv f := Subtype.ext (schemeHomOfAppTop_appTop U V f.1)
  right_inv φ := Subtype.ext (appTop_schemeHomOfAppTop U V φ.1)

/-- The ring map attached to a `Y`-morphism `f : U ⟶ V` by `homOverEquivAppTopOver` is
`f.appTop`. -/
@[simp]
theorem homOverEquivAppTopOver_apply_coe (U V : Scheme.{u}) [IsAffine V] (pV : V ⟶ Y) (pU : U ⟶ Y)
    (f : {f : U ⟶ V // f ≫ pV = pU}) :
    (homOverEquivAppTopOver U V pV pU f).1 = f.1.appTop :=
  rfl

/-- The `Y`-morphism attached to a compatible ring map `φ` by the inverse of
`homOverEquivAppTopOver` is `schemeHomOfAppTop U V φ`. -/
@[simp]
theorem homOverEquivAppTopOver_symm_apply_coe (U V : Scheme.{u}) [IsAffine V] (pV : V ⟶ Y)
    (pU : U ⟶ Y) (φ : {φ : Γ(V, ⊤) ⟶ Γ(U, ⊤) // pV.appTop ≫ φ = pU.appTop}) :
    ((homOverEquivAppTopOver U V pV pU).symm φ).1 = schemeHomOfAppTop U V φ.1 :=
  rfl

section Presentation

variable (U V : Scheme.{u}) [IsAffine V] (pV : V ⟶ Y) (pU : U ⟶ Y) {n : ℕ}
  (P : Fin n → MvPolynomial (Fin n) Γ(Y, ⊤))

/-- A **standard presentation** of `V` over `Y`: an isomorphism of the global functions of `V`
with `Γ(Y, ⊤)[x₁, …, x_n]/(P₁, …, P_n)` carrying the structure map of `V ⟶ Y` to the structure
map of the presented ring.

This is the datum `C = B[x₁, …, x_n]/(P₁, …, P_n)` of step (2) of the proof of Stacks 04I6.  For
`V ⟶ Y` étale it exists by [Stacks Project, Tag 00U9]; nothing below needs to know that. -/
structure StandardPresentationOver where
  /-- The isomorphism identifying `Γ(V, ⊤)` with the presented ring. -/
  iso : Γ(V, ⊤) ≅ CommRingCat.of (MvPolynomial (Fin n) Γ(Y, ⊤) ⧸ Ideal.span (Set.range P))
  /-- The isomorphism is one of `Γ(Y, ⊤)`-algebras. -/
  comp_iso_hom : pV.appTop ≫ iso.hom =
    CommRingCat.ofHom (MvPolynomial.quotientSpanRangeStructureMap P)

namespace StandardPresentationOver

variable {U V pV pU P}

/-- Reading a compatible ring map `Γ(V, ⊤) ⟶ Γ(U, ⊤)` as a point of the presented ring. -/
def toHomOver (pres : StandardPresentationOver V pV P)
    (φ : {φ : Γ(V, ⊤) ⟶ Γ(U, ⊤) // pV.appTop ≫ φ = pU.appTop}) :
    MvPolynomial.HomOver P pU.appTop.hom :=
  ⟨(pres.iso.inv ≫ φ.1).hom, by
    have h : CommRingCat.ofHom (MvPolynomial.quotientSpanRangeStructureMap P) ≫
        pres.iso.inv ≫ φ.1 = pU.appTop := by
      rw [← pres.comp_iso_hom, Category.assoc, Iso.hom_inv_id_assoc]
      exact φ.2
    have := congrArg CommRingCat.Hom.hom h
    rwa [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at this⟩

/-- Reading a point of the presented ring as a compatible ring map `Γ(V, ⊤) ⟶ Γ(U, ⊤)`. -/
def ofHomOver (pres : StandardPresentationOver V pV P)
    (ψ : MvPolynomial.HomOver P pU.appTop.hom) :
    {φ : Γ(V, ⊤) ⟶ Γ(U, ⊤) // pV.appTop ≫ φ = pU.appTop} :=
  ⟨pres.iso.hom ≫ CommRingCat.ofHom ψ.1, by
    rw [← Category.assoc, pres.comp_iso_hom, ← CommRingCat.ofHom_comp, ψ.2]
    exact (CommRingCat.ofHom_hom _).symm⟩

/-- A compatible ring map `Γ(V, ⊤) ⟶ Γ(U, ⊤)` is the same thing as a point of the presented
ring. -/
def homOverEquiv (pres : StandardPresentationOver V pV P) :
    {φ : Γ(V, ⊤) ⟶ Γ(U, ⊤) // pV.appTop ≫ φ = pU.appTop} ≃
      MvPolynomial.HomOver P pU.appTop.hom where
  toFun := pres.toHomOver (pU := pU)
  invFun := pres.ofHomOver (pU := pU)
  left_inv φ := by
    refine Subtype.ext ?_
    change pres.iso.hom ≫ CommRingCat.ofHom (pres.iso.inv ≫ φ.1).hom = φ.1
    rw [CommRingCat.ofHom_hom, Iso.hom_inv_id_assoc]
  right_inv ψ := by
    refine Subtype.ext ?_
    change (pres.iso.inv ≫ pres.iso.hom ≫ CommRingCat.ofHom ψ.1).hom = ψ.1
    rw [Iso.inv_hom_id_assoc, CommRingCat.hom_ofHom]

end StandardPresentationOver

/-- **The equalizer presentation of a representable functor over an affine base, Stacks 04I6
step (2).**  Let `Y` be affine, let `V` be affine over `Y` with a standard presentation
`Γ(V, ⊤) = Γ(Y, ⊤)[x₁, …, x_n]/(P₁, …, P_n)`, and let `U` be any scheme over `Y`.  Then the
`Y`-morphisms `U ⟶ V` are exactly the tuples `a : Fin n → Γ(U, ⊤)` at which every `Pⱼ`, with its
coefficients pushed along `Γ(Y, ⊤) ⟶ Γ(U, ⊤)`, vanishes.

Read as `U` varies over the small étale site of `Y` this is the source's presentation of `h_V` as
the equalizer of `∏ᵢ 𝒪_Y ⇉ ∏ⱼ 𝒪_Y`: the two maps are `a ↦ (Pⱼ(a))ⱼ` and the zero section, the
vanishing condition is the equation between them
(`Stacks.EtaleCohomology.isSolution_iff_eq_zero`), and the identification is natural in `U`
(`Stacks.EtaleCohomology.homOverEquivSolutions_naturality`). -/
def homOverEquivSolutions (pres : StandardPresentationOver V pV P) :
    {f : U ⟶ V // f ≫ pV = pU} ≃
      {a : Fin n → Γ(U, ⊤) // MvPolynomial.IsSolution P pU.appTop.hom a} :=
  (homOverEquivAppTopOver U V pV pU).trans
    ((pres.homOverEquiv (pU := pU)).trans
      (MvPolynomial.quotientSpanRangeHomOverEquiv pU.appTop.hom))

/-- The `i`-th coordinate of the solution naming a `Y`-morphism `f : U ⟶ V` is the image of the
class of `xᵢ` under the ring map `Γ(Y, ⊤)[x₁, …, x_n]/(P₁, …, P_n) ≅ Γ(V, ⊤) ⟶ Γ(U, ⊤)`. -/
theorem homOverEquivSolutions_apply_coe (pres : StandardPresentationOver V pV P)
    (f : {f : U ⟶ V // f ≫ pV = pU}) (i : Fin n) :
    (homOverEquivSolutions U V pV pU P pres f).1 i =
      (pres.iso.inv ≫ f.1.appTop).hom
        (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i)) :=
  rfl

end Presentation

/-- The solution condition of `Stacks.EtaleCohomology.homOverEquivSolutions` is the equation
between the two maps `Γ(U, ⊤)ⁿ ⇉ Γ(U, ⊤)ⁿ` whose equalizer the proof of Stacks 04I6 takes:
`a ↦ (Pⱼ(a))ⱼ` and the zero section. -/
theorem isSolution_iff_eq_zero {R A : Type u} [CommRing R] [CommRing A] {n : ℕ}
    (P : Fin n → MvPolynomial (Fin n) R) (g : R →+* A) (a : Fin n → A) :
    MvPolynomial.IsSolution P g a ↔
      (fun j => MvPolynomial.eval a (MvPolynomial.map g (P j))) = (0 : Fin n → A) :=
  ⟨fun h => funext fun j => h j, fun h j => congrFun h j⟩

section Naturality

variable {U U' V : Scheme.{u}} [IsAffine V] {pV : V ⟶ Y} {pU : U ⟶ Y} {pU' : U' ⟶ Y} {n : ℕ}
  {P : Fin n → MvPolynomial (Fin n) Γ(Y, ⊤)}

/-- **The equalizer presentation is natural in the chart.**  If `k : U' ⟶ U` is a morphism over
`Y`, then the solution naming the `Y`-morphism `k ≫ f : U' ⟶ V` is the image under `k` of the
solution naming `f`, coordinatewise.

This is the naturality the source needs in order to read
`Stacks.EtaleCohomology.homOverEquivSolutions` as a presentation of the *sheaf* `h_V` on the
small étale site of `Y`, rather than of its sections over a single chart. -/
theorem homOverEquivSolutions_naturality (pres : StandardPresentationOver V pV P)
    (k : U' ⟶ U) (hk : k ≫ pU = pU') (f : {f : U ⟶ V // f ≫ pV = pU}) (i : Fin n) :
    (homOverEquivSolutions U' V pV pU' P pres
        ⟨k ≫ f.1, by rw [Category.assoc, f.2, hk]⟩).1 i =
      k.appTop ((homOverEquivSolutions U V pV pU P pres f).1 i) := by
  rw [homOverEquivSolutions_apply_coe, homOverEquivSolutions_apply_coe]
  have h : pres.iso.inv ≫ (k ≫ f.1).appTop = (pres.iso.inv ≫ f.1.appTop) ≫ k.appTop := by
    rw [Scheme.Hom.comp_appTop, Category.assoc]
  exact congrArg (fun φ : CommRingCat.of
      (MvPolynomial (Fin n) Γ(Y, ⊤) ⧸ Ideal.span (Set.range P)) ⟶ Γ(U', ⊤) =>
    φ.hom (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i))) h

end Naturality

end Stacks.EtaleCohomology

end
