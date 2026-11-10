module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.QuadrupleClass
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleUnique

/-!
# The classifying map of Tag 01O4 is injective

`Stacks.AlgebraicGeometry.ProjRepresentsF1.quadrupleClass` sends a strict isomorphism class of
invertible degree-one quotients of `f^*𝒜` to a strict equivalence class of the quadruples of
Section 01NS; composed with the relative universal property
`Stacks.AlgebraicGeometry.ProjRepresentsF1.quadrupleClassEquiv` it is the morphism to relative
`Proj` classified by a class of pairs, `pairClassifyingHom`. Both maps are injective: a pair is
recovered from the morphism it classifies, up to strict isomorphism.

Injectivity rests on the converse of
`Stacks.AlgebraicGeometry.ProjRepresentsF1.strictlyEquivalent_quadruple`: a strict equivalence of
the quadruples two pairs determine is a strict isomorphism of the pairs. The two notions of strict
equivalence compare a *Laurent* algebra `⨁_{n ∈ ℤ} L^{⊗ n}` and a *tensor* algebra `T(L)`
respectively, and both comparisons are determined by their degree-one components: the Laurent one
by `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurent_app_eq_of_app_one`, the tensor one by
the universal property of the tensor algebra.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorCongrUnitalHom` and `tensorCongrIso`: the
  comparison of the tensor algebras of two isomorphic modules, as a unital homomorphism and as an
  isomorphism of sheaves of graded algebras.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.laurentCongrIso_eq_of_pieceOneIso`: an isomorphism of
  the Laurent algebras whose degree-one component is the one an isomorphism `β` of the invertible
  modules induces *is* the isomorphism `β` induces, in every integral degree.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackMap_comp_tensorCongr`: the adjoint transposes
  of two strictly equivalent quadruples' pairs are matched by the tensor comparison, in every
  integral degree.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.strictlyEquivalent_of_quadruple`: strictly equivalent
  quadruples of Section 01NS come from strictly isomorphic pairs of Tag 01O4, the converse of
  `strictlyEquivalent_quadruple`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.strictlyEquivalent_iff_quadruple`: the two notions of
  strict equivalence agree.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.quadrupleClass_injective` and
  `pairClassifyingHom_injective`: the classifying map of Tag 01O4 is injective.

## Implementation notes

The field of `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.StrictlyEquivalent` that
records the comparison `γ` of Laurent algebras requires
`γ.hom.app 1 = (Quadruple.pieceOneIso β).hom`, so `γ` is identified in degree one by definition and
in every other degree by
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurent_app_eq_of_app_one`; surjectivity of the
degree-one component of `ψ` is not needed.

The clause of `StrictlyEquivalent` quantifies over all of `ℤ`, but in a negative degree the source
`f^*𝒜_n` of the adjoint transpose is a zero object,
`Stacks.AlgebraicGeometry.ProjRepresentsF1.isZero_pullbackPiece_of_neg`, so the equation holds
there for any two morphisms. In a nonnegative degree the comparison `T(L)_n ⟶ L^{⊗ n}` is an
isomorphism, by `isIso_tensorToLaurent_app`, and the equation is obtained by cancelling it.

The Laurent algebra and the tensor algebra reach the same category by different routes, as
`AlgebraicGeometry.Scheme.Modules` and as
`SheafOfModules (Stacks.RingedSpace.structureRingSheaf _)`. The two cancellation steps
`comp_inv_comp_hom` and `eq_of_isoHom_comp_comp_isoHom` are therefore stated in an arbitrary
category with every object and morphism free, so that the instance is taken from the goal rather
than from either spelling.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback
open Stacks.RingedSpace

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-! ### The two cancellations, in an arbitrary category -/

/-- Cancelling an isomorphism that follows a composite on the right. -/
private theorem comp_inv_comp_hom {C : Type*} [Category C] {W X Y Z : C} (a : W ⟶ X) (g : X ⟶ Z)
    (b : Y ≅ Z) : (a ≫ g ≫ b.inv) ≫ b.hom = a ≫ g :=
  Eq.trans (Category.assoc a (g ≫ b.inv) b.hom)
    (congrArg (fun z : X ⟶ Z => a ≫ z)
      (Eq.trans (Category.assoc g b.inv b.hom)
        (Eq.trans (congrArg (fun z : Z ⟶ Z => g ≫ z) b.inv_hom_id) (Category.comp_id g))))

/-- Two morphisms sandwiched between the same pair of isomorphisms are equal as soon as the two
sandwiches are. -/
private theorem eq_of_isoHom_comp_comp_isoHom {C : Type*} [Category C] {W X Y Z : C}
    (e : W ≅ X) {a b : X ⟶ Y} (u : Y ≅ Z)
    (h : e.hom ≫ a ≫ u.hom = e.hom ≫ b ≫ u.hom) : a = b :=
  (Iso.cancel_iso_hom_right a b u).mp ((Iso.cancel_iso_hom_left e _ _).mp h)

variable {S T : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})
  (f : T ⟶ S)

/-! ### The comparison of the tensor algebras of two isomorphic modules -/

/-- **The comparison of the tensor algebras of two isomorphic modules**, as a unital homomorphism:
the unique one extending the given isomorphism on the degree-one generators. -/
public def tensorCongrUnitalHom (L L' : T.Modules) (e : L ≅ L') :
    SheafOfModules.GradedAlgebra.UnitalHom (TA T L).tensor (TA T L').tensor :=
  (TA T L).tensor_isTensorAlgebra.descAny (TA T L').tensor
    (e.hom ≫ (TA T L').tensorGenerator)

/-- The comparison extends the isomorphism on the degree-one generators. -/
public theorem tensorCongrUnitalHom_extends (L L' : T.Modules) (e : L ≅ L') :
    (TA T L).tensorGenerator ≫ (tensorCongrUnitalHom TA L L' e).app 1 =
      e.hom ≫ (TA T L').tensorGenerator :=
  (TA T L).tensor_isTensorAlgebra.descAny_extends (TA T L').tensor
    (e.hom ≫ (TA T L').tensorGenerator)

/-- **The comparisons of an isomorphism and of its inverse are mutually inverse.** -/
public theorem tensorCongrUnitalHom_comp (L L' : T.Modules) (e : L ≅ L') :
    (tensorCongrUnitalHom TA L L' e).comp (tensorCongrUnitalHom TA L' L e.symm) =
      SheafOfModules.GradedAlgebra.UnitalHom.id _ := by
  refine (TA T L).tensorHom_ext ?_
  change (TA T L).tensorGenerator ≫
      (tensorCongrUnitalHom TA L L' e).app 1 ≫ (tensorCongrUnitalHom TA L' L e.symm).app 1 =
    (TA T L).tensorGenerator ≫ 𝟙 _
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans
    (congrArg (fun z : L ⟶ (TA T L').tensor.piece 1 =>
      z ≫ (tensorCongrUnitalHom TA L' L e.symm).app 1)
      (tensorCongrUnitalHom_extends TA L L' e)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans
    (congrArg (fun z : L' ⟶ (TA T L).tensor.piece 1 => e.hom ≫ z)
      (tensorCongrUnitalHom_extends TA L' L e.symm)) ?_
  exact Eq.trans (e.hom_inv_id_assoc _) (Category.comp_id _).symm

/-- **The comparison of the tensor algebras of two isomorphic modules**, as an isomorphism of
sheaves of graded algebras. -/
public def tensorCongrIso (L L' : T.Modules) (e : L ≅ L') :
    (TA T L).tensor ≅ (TA T L').tensor where
  hom := (tensorCongrUnitalHom TA L L' e).toHom
  inv := (tensorCongrUnitalHom TA L' L e.symm).toHom
  hom_inv_id := SheafOfModules.GradedAlgebra.Hom.ext fun n =>
    congrArg
      (fun g : SheafOfModules.GradedAlgebra.UnitalHom (TA T L).tensor (TA T L).tensor => g.app n)
      (tensorCongrUnitalHom_comp TA L L' e)
  inv_hom_id := SheafOfModules.GradedAlgebra.Hom.ext fun n =>
    congrArg
      (fun g : SheafOfModules.GradedAlgebra.UnitalHom (TA T L').tensor (TA T L').tensor =>
        g.app n)
      (tensorCongrUnitalHom_comp TA L' L e.symm)

/-- The degree-`n` component of the isomorphism `tensorCongrIso` is the degree-`n` component of the
unital homomorphism `tensorCongrUnitalHom`. -/
@[simp]
public theorem tensorCongrIso_hom_app (L L' : T.Modules) (e : L ≅ L') (n : ℤ) :
    (tensorCongrIso TA L L' e).hom.app n = (tensorCongrUnitalHom TA L L' e).app n :=
  rfl

/-! ### The comparison of Laurent algebras in a strict equivalence is the induced one -/

/-- **An isomorphism `γ` of the Laurent algebras whose degree-one component is the one an
isomorphism `β` of the invertible modules induces agrees with `laurentCongrIso β` in every integral
degree.** -/
public theorem laurentCongrIso_eq_of_pieceOneIso {P Q : F1Pair A TA f}
    (β : P.L ≅ Q.L)
    (γ : letI := P.invertible; letI := Q.invertible; laurent P.L ≅ laurent Q.L)
    (h1 : letI := P.invertible; letI := Q.invertible;
      γ.hom.app 1 = (Quadruple.pieceOneIso (P := P.quadruple A TA f)
        (Q := Q.quadruple A TA f) β).hom) (n : ℤ) :
    letI := P.invertible; letI := Q.invertible
    γ.hom.app n = (laurentCongrIso β).hom.app n := by
  let := P.invertible
  let := Q.invertible
  have key : ∀ z : (laurent P.L).piece 1 ⟶ (laurent Q.L).piece 1,
      z = (oneIsoL P.L).hom ≫ β.hom ≫ (oneIsoL Q.L).inv →
        z ≫ (oneIsoL Q.L).hom = (oneIsoL P.L).hom ≫ β.hom := fun z hz =>
    hz ▸ comp_inv_comp_hom (oneIsoL P.L).hom β.hom (oneIsoL Q.L)
  exact laurent_app_eq_of_app_one (e := β) (key _ h1) (key _ (laurentCongrIso_app_one β)) n

/-! ### The adjoint transposes are matched by the tensor comparison -/

/-- **The tensor comparison carries one pair's adjoint transpose to the other's**, in every
integral degree, as soon as the induced comparison of Laurent algebras does. -/
public theorem pullbackMap_comp_tensorCongr {P Q : F1Pair A TA f} (β : P.L ≅ Q.L)
    (h : ∀ n : ℤ, letI := P.invertible; letI := Q.invertible;
      P.laurentApp A TA f n ≫ (laurentCongrIso β).hom.app n = Q.laurentApp A TA f n)
    (n : ℤ) :
    P.pullbackMap A TA n ≫ (tensorCongrUnitalHom TA P.L Q.L β).app n =
      Q.pullbackMap A TA n := by
  let := P.invertible
  let := Q.invertible
  rcases lt_or_ge n 0 with hn | hn
  · exact (isZero_pullbackPiece_of_neg A f hn).eq_of_src _ _
  · have : IsIso ((tensorToLaurent Q.L (TA T Q.L)).app n) :=
      isIso_tensorToLaurent_app Q.L (TA T Q.L) n hn
    refine eq_of_isoHom_comp_comp_isoHom
      (eqToIso (congrArg (fun k : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj (A.piece k))
        (mul_one n)))
      (asIso ((tensorToLaurent Q.L (TA T Q.L)).app n)) ?_
    exact Eq.trans
      (laurentAppOf_comp_laurentCongrIso A TA f P.L Q.L β
        (tensorCongrUnitalHom TA P.L Q.L β) (tensorCongrUnitalHom_extends TA P.L Q.L β)
        (P.pullbackMap A TA)
        (fun i => P.pullbackMap A TA i ≫ (tensorCongrUnitalHom TA P.L Q.L β).app i)
        (fun _ => rfl) n).symm
      (h n)

/-! ### A strict equivalence of quadruples is a strict isomorphism of pairs -/

/-- A matched pair of adjoint transposes is a matched pair of graded maps: the clause
`∀ n, ψ_n ≫ f_*(γ_n) = ψ'_n` of `Stacks.AlgebraicGeometry.ProjRepresentsF1.StrictlyEquivalent`. -/
private theorem psi_comp_of_pullbackMap_comp {P Q : F1Pair A TA f} (n : ℤ)
    (g : (TA T P.L).tensor.piece n ⟶ (TA T Q.L).tensor.piece n)
    (h : P.pullbackMap A TA n ≫ g = Q.pullbackMap A TA n) :
    P.ψ n ≫ (Scheme.Modules.pushforward f).map g = Q.ψ n :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm.injective
    (Eq.trans
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right_symm
        (P.ψ n) g) h)

/-- **Strictly equivalent quadruples of Section 01NS come from strictly isomorphic pairs of Tag
01O4** — the converse of `Stacks.AlgebraicGeometry.ProjRepresentsF1.strictlyEquivalent_quadruple`.
-/
public theorem strictlyEquivalent_of_quadruple {P Q : F1Pair A TA f}
    (h : Quadruple.StrictlyEquivalent (P.quadruple A TA f) (Q.quadruple A TA f)) :
    StrictlyEquivalent A TA P Q := by
  let := P.invertible
  let := Q.invertible
  obtain ⟨β, γ, h1, hψ⟩ := h
  refine ⟨β, tensorCongrIso TA P.L Q.L β, tensorCongrUnitalHom_extends TA P.L Q.L β,
    (tensorCongrUnitalHom TA P.L Q.L β).sectionsMap_one, fun n => ?_⟩
  refine psi_comp_of_pullbackMap_comp A TA f n _
    (pullbackMap_comp_tensorCongr A TA f β (fun i => ?_) n)
  exact Eq.trans
    (congrArg (fun z : (laurent P.L).piece i ⟶ (laurent Q.L).piece i =>
      P.laurentApp A TA f i ≫ z)
      (laurentCongrIso_eq_of_pieceOneIso A TA f β γ h1 i).symm) (hψ i)

/-- **The two notions of strict equivalence agree.** Two pairs of Tag 01O4 are strictly isomorphic
exactly when the quadruples of Section 01NS they determine are strictly equivalent. -/
public theorem strictlyEquivalent_iff_quadruple (P Q : F1Pair A TA f) :
    StrictlyEquivalent A TA P Q ↔
      Quadruple.StrictlyEquivalent (P.quadruple A TA f) (Q.quadruple A TA f) :=
  ⟨strictlyEquivalent_quadruple A TA f, strictlyEquivalent_of_quadruple A TA f⟩

/-! ### Injectivity -/

/-- **The map from Tag 01O4's functor `F_1` to Section 01NS's `F_d` at `d = 1` is injective.** -/
public theorem quadrupleClass_injective : Function.Injective (quadrupleClass A TA f) :=
  Quot.ind fun P => Quot.ind fun Q => fun hcc =>
    (quot_mk_eq_iff_strictlyEquivalent A TA P Q).mpr
      (strictlyEquivalent_of_quadruple A TA f (Quotient.exact hcc))

variable (X : RelativeProjData A)

/-- **Tag 01O4.** For a quasi-coherent graded `𝒪_S`-algebra generated in degree one, distinct
strict isomorphism classes of invertible degree-one quotients of `f^*𝒜` classify distinct morphisms
to the relative homogeneous spectrum over the base: a class of pairs is recovered from the morphism
it classifies. -/
public theorem pairClassifyingHom_injective (hgen : IsGeneratedInDegreeOne A) :
    Function.Injective (pairClassifyingHom A TA f X hgen) :=
  Function.Injective.comp (quadrupleClassEquiv A X hgen f).injective
    (quadrupleClass_injective A TA f)

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
