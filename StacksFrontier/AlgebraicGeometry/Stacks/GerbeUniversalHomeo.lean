module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatOpenPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatness
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphismAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# A gerbe of algebraic stacks is a universal homeomorphism (Stacks 06R9)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which exhibits `𝒳` as a gerbe over
`𝒴` for the localized big fppf topology, in the sense of Stacks 06QC. Then `f` is a *universal
homeomorphism* (**Stacks 0CI7**): every 2-fibre-product base change of `f` induces a
homeomorphism on the topological spaces of points of Stacks 04XG and Stacks 04XL.

## Main results

* `AlgebraicGeometry.Stack.injective_pointsMap_of_isGerbeOver`: a gerbe 1-morphism is injective
  on points.
* `AlgebraicGeometry.Stack.isHomeomorph_pointsMap_of_isGerbeOver`: a gerbe 1-morphism is a
  homeomorphism on points.
* `AlgebraicGeometry.Stack.universalHomeomorphism_of_isGerbeOver`: **Stacks 06R9**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.universalHomeomorphism_of_isGerbeOver`: the same
  statement for the canonical-square form of Stacks 0CI7.

## Implementation notes

The gerbe condition is stable under base change (**Stacks 06QE**), so the universal statement
reduces to the absolute one; the reduction exchanges the two legs of the square with
`CategoryTheory.Bicategory.TwoCommSq.swap`, since Stacks 06QE is stated for the second
projection.

The absolute statement has four halves. Continuity is
`AlgebraicGeometry.Stack.continuous_pointsMap`, one of the characterizing properties of the
topology of Stacks 04XL. Surjectivity is the proved clause of **Stacks 06QI**,
`AlgebraicGeometry.Stack.isSurjective_of_isGerbeOver`. Injectivity is proved here from clause
(2)(b) of **Stacks 06P1**, where the source writes "details omitted": two field-valued points
`p`, `q` of `𝒳` whose images agree in `|𝒴|` admit a field-valued point `r` of `𝒴` with arrows to
both images; lifting the two base morphisms of `r` through `𝒳` and using that a 1-morphism of
categories fibred in groupoids carries every morphism to a strongly cartesian one
(`CategoryTheory.CatFiberedInGroupoids.isStronglyCartesian_map`) factors the two arrows of `r`
through those lifts by isomorphisms of the fibre over `r`; their composite is a fibre
automorphism between two `f`-images, so clause (2)(b) makes it the `f`-image of a morphism of
`𝒳` after restriction along a covering sieve, and
`AlgebraicGeometry.Stack.exists_isFieldObject_arrow_of_mem_topology` picks a member of that sieve
whose source is again a field spectrum. Openness is **Stacks 06R7** applied to the base change.

Stacks 06R7 needs the base change to be flat and locally of finite presentation; these are the
two remaining clauses of Stacks 06QI,
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver`,
applied to the base change, which is again a gerbe.

The notion of universal homeomorphism used is `AlgebraicGeometry.Stack.UniversalHomeomorphism`,
which quantifies over *every* 2-fibre product of the cospan, rather than
`AlgebraicGeometry.Stack.AlgebraicStacks.UniversalHomeomorphism`, which tests only the canonical
one: the proof produces the condition at an arbitrary square, which is the stronger-looking of
the two forms, and the canonical form follows by instantiating it.

## References

* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 06P1](https://stacks.math.columbia.edu/tag/06P1)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
* [Stacks Project, Tag 06Q4](https://stacks.math.columbia.edu/tag/06Q4)
* [Stacks Project, Tag 06QE](https://stacks.math.columbia.edu/tag/06QE)
* [Stacks Project, Tag 06QI](https://stacks.math.columbia.edu/tag/06QI)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
* [Stacks Project, Tag 06R9](https://stacks.math.columbia.edu/tag/06R9)
* [Stacks Project, Tag 0CI7](https://stacks.math.columbia.edu/tag/0CI7)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v t w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The base of a field-valued point of a category over the big fppf site of `S` is an object of
the site whose underlying scheme is the spectrum of a field. -/
private theorem isFieldObject_p_obj {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    (r : FieldValuedPoint B S hS 𝒳) : IsFieldObject B S hS (𝒳.p.obj r.obj) :=
  ⟨r.carrier, r.field,
    ⟨eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj r.over) ≪≫ r.isSpec⟩⟩

/-- Two morphisms over the same base morphism with a common target have the same image under
`p`, up to the identification of the bases of their sources. -/
theorem eqToHom_comp_map_eq_map_of_isHomLift {𝒳 𝒮 : Type*} [Category 𝒳] [Category 𝒮]
    (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} (f : R ⟶ S) {a a' b : 𝒳} (φ : a' ⟶ b) (ψ : a ⟶ b)
    (hφ : p.IsHomLift f φ) (hψ : p.IsHomLift f ψ) (h : p.obj a = p.obj a') :
    eqToHom h ≫ p.map φ = p.map ψ := by
  rw [IsHomLift.fac' p f φ, IsHomLift.fac' p f ψ]
  simp

/-- **A gerbe 1-morphism of algebraic stacks over `S` is injective on points.** This is the
injectivity half of Stacks 06R9, where the source writes "details omitted"; the content is
clause (2)(b) of **Stacks 06P1**.

If two field-valued points `p`, `q` of `𝒳` have the same image in `|𝒴|` then their images admit
a common field-valued refinement `r`. Lifting the two base morphisms of `r` to arrows into `p`
and `q` and factoring the arrows of `r` through the `f`-images of those lifts — possible because
a 1-morphism of categories fibred in groupoids carries every morphism to a strongly cartesian
one — produces an automorphism of the fibre of `𝒴` over the base of `r` between two `f`-images.
Clause (2)(b) of Stacks 06P1 exhibits it as an `f`-image after restriction along a covering
sieve, and such a sieve of a field spectrum contains an arrow from a field spectrum, so the
restricted lift is a common field-valued refinement of `p` and `q`. -/
theorem injective_pointsMap_of_isGerbeOver {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsGerbeOver B S hS f) :
    Function.Injective (AlgebraicStacks.pointsMap B S hS f) := by
  classical
  intro z z' hzz'
  obtain ⟨p, rfl⟩ := Quotient.exists_rep z
  obtain ⟨q, rfl⟩ := Quotient.exists_rep z'
  refine (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val.val
    (Classical.choose 𝒳.property) p q).2 ?_
  obtain ⟨r, ⟨α⟩, ⟨β⟩⟩ := (class_eq_class_iff_hasCommonExtension B S hS 𝒴.val.val
    (Classical.choose 𝒴.property)
    (fieldValuedPointMap B S hS 𝒳.val.val f.hom.hom p)
    (fieldValuedPointMap B S hS 𝒳.val.val f.hom.hom q)).1 hzz'
  set F := CatFiberedInGroupoids.homFunctor f.hom
  set qX := 𝒳.val.val.p
  set qY := 𝒴.val.val.p
  set u := qY.obj r.obj
  -- Lift an arrow `r ⟶ F a` to an arrow into `a`, and factor it through the `f`-image of the lift
  -- by an isomorphism lying over an identity.
  have key : ∀ (a : _) (α : r.obj ⟶ F.obj a), ∃ (a₁ : _) (i : a₁ ⟶ a) (γ : r.obj ⟶ F.obj a₁),
      IsIso γ ∧ qY.IsHomLift (𝟙 u) γ := by
    intro a α
    have hFa : qY.obj (F.obj a) = qX.obj a := BasedFunctor.w_obj f.hom.hom a
    set base : u ⟶ qX.obj a := qY.map α ≫ eqToHom hFa
    obtain ⟨a₁, i, hi⟩ := (Classical.choose 𝒳.property).exists_lift base a rfl
    have hFi : qY.IsHomLift base (F.map i) := BasedFunctor.preserves_isHomLift f.hom.hom base i
    have hαLift : qY.IsHomLift base α := IsHomLift.of_fac qY base α rfl hFa rfl
    have hFa₁ : qY.obj (F.obj a₁) = u := IsHomLift.domain_eq qY base (F.map i)
    obtain ⟨γ, ⟨hγmap, -⟩, -⟩ := hf.base_isFiberedInGroupoids.unique_lift (F.map i) α
      (eqToHom hFa₁.symm) (eqToHom_comp_map_eq_map_of_isHomLift qY base (F.map i) α hFi hαLift
        hFa₁.symm)
    have hγlift : qY.IsHomLift (𝟙 u) γ :=
      IsHomLift.of_fac' qY (𝟙 u) γ rfl hFa₁ (by rw [hγmap]; simp)
    exact ⟨a₁, i, γ, hf.base_isFiberedInGroupoids.isIso_of_isHomLift_id γ hγlift, hγlift⟩
  obtain ⟨p₁, i₁, γ₁, _, hγ₁lift⟩ := key p.obj α
  obtain ⟨q₁, i₂, γ₂, _, hγ₂lift⟩ := key q.obj β
  -- The fibre automorphism to which Stacks 06P1 (2)(b) is applied.
  obtain ⟨R, hR, hcover⟩ := hf.locally_full (inv γ₁ ≫ γ₂)
    (by simpa using IsHomLift.comp qY (𝟙 u) (𝟙 u) (inv γ₁) γ₂)
  obtain ⟨V, fV, ⟨K, hKfield, ⟨eSpec⟩⟩, hfV⟩ :=
    exists_isFieldObject_arrow_of_mem_topology B S hS (U := u) (isFieldObject_p_obj B S hS r) hR
  obtain ⟨x₁, x₁', ξ, ξ', a, hξ, -, -, -⟩ := hcover fV hfV
  exact ⟨{ carrier := K
           field := hKfield
           base := V
           isSpec := eSpec
           obj := x₁
           «over» := (BasedFunctor.w_obj f.hom.hom x₁).symm.trans
             (IsHomLift.domain_eq (F ⋙ qY) fV ξ) }, ⟨ξ ≫ i₁⟩, ⟨a ≫ ξ' ≫ i₂⟩⟩

/-- **A gerbe 1-morphism of algebraic stacks over `S` is a homeomorphism on points.** It is
continuous by Stacks 04XL, surjective by **Stacks 06QI**, injective by
`AlgebraicGeometry.Stack.injective_pointsMap_of_isGerbeOver`, and open by **Stacks 06R7**, being
flat and locally of finite presentation by Stacks 06QI. -/
theorem isHomeomorph_pointsMap_of_isGerbeOver {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsGerbeOver B S hS f) :
    @IsHomeomorph _ _ (pointTopology B S hS 𝒳.val) (pointTopology B S hS 𝒴.val)
      (AlgebraicStacks.pointsMap B S hS f) := by
  let _ := pointTopology B S hS 𝒳.val
  let _ := pointTopology B S hS 𝒴.val
  obtain ⟨hflat, hlfp⟩ :=
    AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver B S hS f hf
  exact ⟨continuous_pointsMap B S hS 𝒳.val 𝒴.val f.hom.hom,
    AlgebraicStacks.isOpenMap_pointsMap B S hS f hflat hlfp,
    injective_pointsMap_of_isGerbeOver B S hS f hf,
    isSurjective_of_isGerbeOver B S hS f hf⟩

/-- **Stacks 06R9.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` which exhibits `𝒳` as
a gerbe over `𝒴` is a universal homeomorphism in the sense of Stacks 0CI7.

The gerbe condition base changes (Stacks 06QE), so each projection `|𝒵 ×_𝒴 𝒳| → |𝒵|` is a
homeomorphism by `AlgebraicGeometry.Stack.isHomeomorph_pointsMap_of_isGerbeOver`. -/
@[stacks 06R9]
theorem universalHomeomorphism_of_isGerbeOver {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsGerbeOver B S hS f) :
    UniversalHomeomorphism B S hS f := fun _ _ P hP =>
  isHomeomorph_pointsMap_of_isGerbeOver B S hS P.fst
    (AlgebraicStacks.isGerbeOver_of_isTwoFibreProduct B S hS P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hf)

/-- **Stacks 06R9** in the form of
`AlgebraicGeometry.Stack.AlgebraicStacks.UniversalHomeomorphism`, which tests only the canonical
2-fibre product of Stacks 04T2: a gerbe 1-morphism of algebraic stacks over `S` is a universal
homeomorphism. -/
theorem AlgebraicStacks.universalHomeomorphism_of_isGerbeOver
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsGerbeOver B S hS f) :
    AlgebraicStacks.UniversalHomeomorphism B S hS f := fun 𝒵 g =>
  Stack.universalHomeomorphism_of_isGerbeOver B S hS f hf 𝒵 g
    (twoFibreProductSquareAlgebraicStacks B S hS g f)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f)

end AlgebraicGeometry.Stack

end
