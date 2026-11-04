module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.QuadrupleFromPair
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.RelativeDegreeOne
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr

/-!
# A strict isomorphism class of pairs is a strict equivalence class of quadruples

`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair.quadruple` is the quadruple of Section 01NS at
`d = 1` built from a pair `(ℒ, ψ)` of
Tag 01O4. This file proves that the construction **respects the two notions of
strict equivalence**: strictly isomorphic pairs give strictly equivalent quadruples, so it
descends to the quotients and sends a point of Tag 01O4's functor `F_1` to a point of
Section 01NS's `F_d` at `d = 1`.

Composed with the relative universal property
`Stacks.AlgebraicGeometry.ProjRepresentsF1.quadrupleClassEquiv`, this produces **the morphism
to relative `Proj` classified by an invertible degree-one quotient**, with nothing assumed beyond
generation in degree one.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorToLaurent_congr`: **the comparison of the
  tensor algebra of an invertible module with its Laurent algebra is natural** in the module: an
  isomorphism `e : L ≅ L'` and a unital homomorphism of the two tensor algebras extending it on
  the degree-one generators commute with the two comparisons in every degree.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.laurentAppOf_comp_laurentCongrIso`: hence the family
  `Stacks.AlgebraicGeometry.ProjRepresentsF1.laurentAppOf` is natural in the invertible module.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.strictlyEquivalent_quadruple`: **strictly isomorphic
  pairs of Tag 01O4 give strictly equivalent quadruples of Section 01NS.**
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.quadrupleClass`: hence the map from Tag 01O4's
  functor `F_1` to the strict equivalence classes of quadruples.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pairClassifyingHom`: **the morphism to relative
  `Proj` over the base classified by a point of Tag 01O4's functor**, for an algebra generated in
  degree one.

## Implementation notes

**The naturality is proved by uniqueness, not by computation.** Both composites
`T(L) ⟶ ⨁_n L^{⊗ n} ⟶ ⨁_n (L')^{⊗ n}` and `T(L) ⟶ T(L') ⟶ ⨁_n (L')^{⊗ n}` are unital
homomorphisms of sheaves of graded algebras out of a tensor algebra, and they agree on the
degree-one generator; `SheafOfModules.GradedAlgebra.IsTensorAlgebra.descAny_unique` makes them
equal. That they agree on the generator is `laurentGenerator_comp_laurentCongrIso`, which holds
because the generator of the Laurent algebra is the inverse of the identification `L^{⊗ 1} = L`
of Tag 01CU, and that identification is the left unit constraint of Tag 01CA — so the agreement
is the naturality of that constraint. The identification is *not* the unitor by `rfl`: it is the
unitor read through the comparison of the localized tensor product with the tensor product
sheaf, which is `Stacks.SheafOfModules.Invertible.tensorPowerOneIso_hom_eq`.

**The induced comparison of Laurent algebras is unital for free.** The degree-zero piece of the
Laurent algebra of `L` does not depend on `L` — it is the unit object — and
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso_zero` says the degree-zero
component of the comparison is the identity, so the unit clause of
`SheafOfModules.GradedAlgebra.UnitalHom` holds by `rfl`, and so does the equality of the two
units.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
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

/-! ### The induced comparison of Laurent algebras, as a unital homomorphism -/

section Congr

variable {T : Scheme.{u}} {L L' : T.Modules}
  [hL : Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L]
  [hL' : Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L']

/-- **The comparison of Laurent algebras induced by an isomorphism of invertible modules is
unital.** The degree-zero piece of a Laurent algebra is the unit object, independently of the
module, and the degree-zero component of the comparison is the identity by
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso_zero`. -/
public def laurentCongrUnitalHom (e : L ≅ L') :
    SheafOfModules.GradedAlgebra.UnitalHom (laurent L) (laurent L') :=
  SheafOfModules.GradedAlgebra.UnitalHom.ofHom (laurentCongrIso e).hom rfl

/-- In each degree the induced unital homomorphism of Laurent algebras is the corresponding
component of the comparison isomorphism. -/
@[simp]
public theorem laurentCongrUnitalHom_app (e : L ≅ L') (n : ℤ) :
    (laurentCongrUnitalHom e).app n = (laurentCongrIso e).hom.app n :=
  rfl

section Generator

open CategoryTheory.MonoidalCategory

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-- **The degree-one generator of the Laurent algebra inverts the left unit constraint of Tag
01CA.** The generator is the inverse of the identification `L^{⊗ 1} = L` of Tag 01CU, and
`Stacks.SheafOfModules.Invertible.tensorPowerOneIso_hom_eq` computes that identification as the
left unitor read through the comparison of the localized tensor product with the tensor product
sheaf; the comparison cancels because the strict unitor is that very composite. -/
private theorem laurentGenerator_eq_leftUnitor_inv
    (M : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 M] :
    laurentGenerator M = (λ_ M).inv :=
  congrArg Iso.inv (Iso.ext
    (@Stacks.SheafOfModules.Invertible.tensorPowerOneIso_hom_eq _ _ _ _ _ _ _ M
      (laurentSituation M).invertible))

/-- **The induced comparison carries the degree-one generator of one Laurent algebra to that of
the other.** In degree one the comparison is the given isomorphism whiskered by the unit object
(`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso_one`), and the generator
is the inverse of the identification `L^{⊗ 1} = L` of Tag 01CU, which
`Stacks.SheafOfModules.Invertible.tensorPowerOneIso_hom_eq` identifies with the left unit
constraint of Tag 01CA; so this is the naturality of that constraint. -/
public theorem laurentGenerator_comp_laurentCongrIso (e : L ≅ L') :
    laurentGenerator L ≫ (laurentCongrIso e).hom.app 1 = e.hom ≫ laurentGenerator L' := by
  refine Eq.trans (congrArg (fun z : (laurent L).piece 1 ⟶ (laurent L').piece 1 =>
      laurentGenerator L ≫ z)
    (Eq.trans (laurentCongrIso_app e 1) (LaurentCongr.congrIso_one e))) ?_
  refine Eq.trans (congrArg (fun z => z ≫ _) (laurentGenerator_eq_leftUnitor_inv L))
    (Eq.trans (MonoidalCategory.leftUnitor_inv_naturality
        (C := SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) e.hom).symm
      (congrArg (fun z => e.hom ≫ z) (laurentGenerator_eq_leftUnitor_inv L').symm))

end Generator

variable (B : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥T) L)
  (B' : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥T) L')

/-- **The comparison of the tensor algebra of an invertible module with its Laurent algebra is
natural in the module.** Let `e : L ≅ L'` be an isomorphism of invertible modules and `γ` a
unital homomorphism of their tensor algebras extending `e` on the degree-one generators. Then in
every degree the comparison of `L` followed by the comparison of Laurent algebras induced by `e`
is `γ` followed by the comparison of `L'`.

Both composites are unital homomorphisms out of a tensor algebra agreeing on the degree-one
generator, so they are equal. -/
public theorem tensorToLaurent_congr (e : L ≅ L')
    (γ : SheafOfModules.GradedAlgebra.UnitalHom B.tensor B'.tensor)
    (hγ : B.tensorGenerator ≫ γ.app 1 = e.hom ≫ B'.tensorGenerator) (n : ℤ) :
    (tensorToLaurent L B).app n ≫ (laurentCongrIso e).hom.app n =
      γ.app n ≫ (tensorToLaurent L' B').app n := by
  have h1 : B.tensorGenerator ≫ ((tensorToLaurent L B).comp (laurentCongrUnitalHom e)).app 1 =
      laurentGenerator L ≫ (laurentCongrIso e).hom.app 1 :=
    Eq.trans (Category.assoc B.tensorGenerator ((tensorToLaurent L B).app 1)
        ((laurentCongrIso e).hom.app 1)).symm
      (congrArg (fun z : L ⟶ (laurent L).piece 1 => z ≫ (laurentCongrIso e).hom.app 1)
        (tensorGenerator_comp_tensorToLaurent L B))
  have h2 : B.tensorGenerator ≫ (γ.comp (tensorToLaurent L' B')).app 1 =
      laurentGenerator L ≫ (laurentCongrIso e).hom.app 1 :=
    Eq.trans
      (Eq.trans (Category.assoc B.tensorGenerator (γ.app 1)
          ((tensorToLaurent L' B').app 1)).symm
        (Eq.trans
          (congrArg (fun z : L ⟶ B'.tensor.piece 1 =>
              z ≫ (tensorToLaurent L' B').app 1) hγ)
          (Eq.trans (Category.assoc e.hom B'.tensorGenerator ((tensorToLaurent L' B').app 1))
            (congrArg (fun z : L' ⟶ (laurent L').piece 1 => e.hom ≫ z)
              (tensorGenerator_comp_tensorToLaurent L' B')))))
      (laurentGenerator_comp_laurentCongrIso e).symm
  have hEq : (tensorToLaurent L B).comp (laurentCongrUnitalHom e) =
      γ.comp (tensorToLaurent L' B') :=
    Eq.trans (B.tensor_isTensorAlgebra.descAny_unique (laurent L') _ h1)
      (B.tensor_isTensorAlgebra.descAny_unique (laurent L') _ h2).symm
  exact congrArg (fun g : SheafOfModules.GradedAlgebra.UnitalHom B.tensor (laurent L') =>
    g.app n) hEq

end Congr

/-! ### The family a degreewise map determines is natural in the invertible module -/

variable {S T : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})
  (f : T ⟶ S)

/-- **The family `Stacks.AlgebraicGeometry.ProjRepresentsF1.laurentAppOf` is natural in the
invertible module.** An isomorphism of invertible modules, a unital homomorphism of their tensor
algebras extending it on the degree-one generators, and two degreewise families matched by that
homomorphism give the same family into the two Laurent algebras, up to the induced comparison. -/
public theorem laurentAppOf_comp_laurentCongrIso (L L' : T.Modules)
    [Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L]
    [Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L'] (e : L ≅ L')
    (γ : SheafOfModules.GradedAlgebra.UnitalHom (TA T L).tensor (TA T L').tensor)
    (hγ : (TA T L).tensorGenerator ≫ γ.app 1 = e.hom ≫ (TA T L').tensorGenerator)
    (φ : ∀ n : ℤ, (Scheme.Modules.pullback f).obj (A.piece n) ⟶ (TA T L).tensor.piece n)
    (φ' : ∀ n : ℤ, (Scheme.Modules.pullback f).obj (A.piece n) ⟶ (TA T L').tensor.piece n)
    (hφ : ∀ n : ℤ, φ n ≫ γ.app n = φ' n) (i : ℤ) :
    laurentAppOf A TA f L φ i ≫ (laurentCongrIso e).hom.app i =
      laurentAppOf A TA f L' φ' i := by
  have key : (φ i ≫ (tensorToLaurent L (TA T L)).app i) ≫ (laurentCongrIso e).hom.app i =
      φ' i ≫ (tensorToLaurent L' (TA T L')).app i :=
    Eq.trans (Category.assoc (φ i) ((tensorToLaurent L (TA T L)).app i)
        ((laurentCongrIso e).hom.app i))
      (Eq.trans
        (congrArg (fun z : (TA T L).tensor.piece i ⟶ (laurent L').piece i => φ i ≫ z)
          (tensorToLaurent_congr (TA T L) (TA T L') e γ hγ i))
        (Eq.trans (Category.assoc (φ i) (γ.app i)
            ((tensorToLaurent L' (TA T L')).app i)).symm
          (congrArg
            (fun z : (Scheme.Modules.pullback f).obj (A.piece i) ⟶ (TA T L').tensor.piece i =>
              z ≫ (tensorToLaurent L' (TA T L')).app i) (hφ i))))
  exact Eq.trans
    (Category.assoc
      (eqToHom (congrArg (fun k : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj (A.piece k))
        (mul_one i)))
      (φ i ≫ (tensorToLaurent L (TA T L)).app i) ((laurentCongrIso e).hom.app i))
    (congrArg
      (fun z : (pullbackFunctor (ringedSpaceHom f)).obj (A.piece i) ⟶ (laurent L').piece i =>
        eqToHom (congrArg (fun k : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj (A.piece k))
          (mul_one i)) ≫ z)
      key)

/-! ### A strict isomorphism of pairs is a strict equivalence of quadruples -/

/-- **A strict isomorphism of pairs carries one adjoint transpose to the other.** The clause
`∀ n, ψ_n ≫ f_*(γ_n) = ψ'_n` of `Stacks.AlgebraicGeometry.ProjRepresentsF1.StrictlyEquivalent`,
transposed across the pullback–pushforward adjunction. -/
public theorem pullbackMap_comp_app {P Q : F1Pair A TA f}
    (γ : (TA T P.L).tensor ≅ (TA T Q.L).tensor)
    (hψ : ∀ n, P.ψ n ≫ (Scheme.Modules.pushforward f).map (γ.hom.app n) = Q.ψ n) (n : ℤ) :
    P.pullbackMap A TA n ≫ γ.hom.app n = Q.pullbackMap A TA n :=
  Eq.trans
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right_symm
      (P.ψ n) (γ.hom.app n)).symm
    (congrArg ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (hψ n))

/-- **Strictly isomorphic pairs of Tag 01O4 give strictly equivalent quadruples of
Section 01NS.** The witness is the comparison of Laurent algebras induced by the isomorphism of
the invertible modules; by
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_iff_exists_hom` that
comparison is all that has to be produced. -/
public theorem strictlyEquivalent_quadruple {P Q : F1Pair A TA f}
    (h : StrictlyEquivalent A TA P Q) :
    Quadruple.StrictlyEquivalent (P.quadruple A TA f) (Q.quadruple A TA f) := by
  obtain ⟨β, γ, hgen, hone, hψ⟩ := h
  let := P.invertible
  let := Q.invertible
  exact (Quadruple.strictlyEquivalent_iff_exists_hom _ _).2
    ⟨laurentCongrIso β, laurentAppOf_comp_laurentCongrIso A TA f P.L Q.L β
      (SheafOfModules.GradedAlgebra.UnitalHom.ofHom γ.hom hone) hgen
      (P.pullbackMap A TA) (Q.pullbackMap A TA) (pullbackMap_comp_app A TA f γ hψ)⟩

/-! ### The induced map on classes -/

/-- **A point of Tag 01O4's functor `F_1` is a point of Section 01NS's `F_d` at `d = 1`.** The
quadruple a pair determines, read in the quotient by strict equivalence; well defined by
`strictlyEquivalent_quadruple`. -/
public def quadrupleClass :
    F1 A TA f → Quotient (Quadruple.setoid f (situationAlgebra A) (1 : ℤ)) :=
  Quot.lift (fun P => Quotient.mk _ (P.quadruple A TA f)) <| by
    intro P Q h
    induction h with
    | rel _ _ hxy => exact Quotient.sound (strictlyEquivalent_quadruple A TA f hxy)
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The class attached to the class of a pair is the class of the quadruple that pair
determines. -/
@[simp]
public theorem quadrupleClass_mk (P : F1Pair A TA f) :
    quadrupleClass A TA f (Quot.mk _ P) = Quotient.mk _ (P.quadruple A TA f) :=
  rfl

/-! ### The morphism to relative `Proj` classified by an invertible degree-one quotient -/

variable (X : RelativeProjData A)

/-- **The morphism to relative `Proj` over the base classified by a point of Tag 01O4's
functor.** For a quasi-coherent graded `𝒪_S`-algebra generated in degree one and an arbitrary
relative homogeneous spectrum `X` of it, a strict isomorphism class of invertible degree-one
quotients of `f^*𝒜` determines a morphism `T ⟶ X` over `S`: the class of quadruples it becomes
under `quadrupleClass`, fed to the relative universal property
`Stacks.AlgebraicGeometry.ProjRepresentsF1.quadrupleClassEquiv`. -/
public def pairClassifyingHom (hgen : IsGeneratedInDegreeOne A) (c : F1 A TA f) :
    {g : T ⟶ X.scheme // g ≫ X.toBase = f} :=
  quadrupleClassEquiv A X hgen f (quadrupleClass A TA f c)

/-- The classified morphism lies over the given morphism to the base. -/
public theorem pairClassifyingHom_comp_toBase (hgen : IsGeneratedInDegreeOne A) (c : F1 A TA f) :
    (pairClassifyingHom A TA f X hgen c).1 ≫ X.toBase = f :=
  (pairClassifyingHom A TA f X hgen c).2

/-- The morphism classified by the class of a pair is the morphism the class of the quadruple
that pair determines classifies. -/
public theorem pairClassifyingHom_mk (hgen : IsGeneratedInDegreeOne A) (P : F1Pair A TA f) :
    (pairClassifyingHom A TA f X hgen (Quot.mk _ P)).1 =
      classifyingHom A X ⟨f, Quotient.mk _ (P.quadruple A TA f)⟩ :=
  rfl

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
