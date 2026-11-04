module

public import StacksFrontier.AlgebraicGeometry.Quot.DerivedRelHomDegreeZero

/-!
# The degree-zero step of the relative Hom functor as a bijection

Let `P` be a pullback pseudofunctor datum of additive functors between abelian categories, with
left derived functors `L f` and comparisons `c f : Q ∘ L f ⟶ Q ∘ f^*`.  For `α : E ⟶ F[0]` with
`L(κ i)^*E` concentrated in degrees `≤ 0` and `α` inducing isomorphisms `H⁰(L(κ i)^*E) ≅ (κ i)^*F`,
the morphism `CategoryTheory.PullbackData.relHomDegreeZero` of relative Hom functors sends `ψ` to
the image of `ψ ≫ singleComparison` under a bijection
`Hom(L(κ i)^*E, ((κ i)^*G)[0]) ≃ Hom((κ i)^*F, (κ i)^*G)`: degree-zero cohomology
(`Stacks.Sites.FibredCategory.homologyHomEquiv`) followed by precomposition with the inverse of
the comparison `H⁰(L(κ i)^*E) ≅ (κ i)^*F`.

The comparison `singleComparison` of the left derived functor at an object placed in degree zero
is the comparison `complexComparison` at the complex `N[0]` of the derived and the degreewise
pullback, followed by the identification of the degreewise pullback of `N[0]` with `(f^*N)[0]`.

These are steps of the identification `Hom(F_T, G_T) = H⁰(T, Lg^*K)` in the proof of
Stacks 08JY.

## Main definitions

* `CategoryTheory.PullbackData.complexComparison`: the comparison `L f (K) ⟶ f^*K` of the left
  derived functor at a complex.
* `CategoryTheory.PullbackData.degreeZeroHomEquiv`: the bijection
  `Hom(L(κ i)^*E, ((κ i)^*G)[0]) ≃ Hom((κ i)^*F, (κ i)^*G)`.

## Main results

* `CategoryTheory.PullbackData.singleComparison_eq_complexComparison_comp`.
* `mapHomologicalComplex_hom_app_single_comp_singleMapHomologicalComplex_hom_app` (in the
  namespace `HomologicalComplex`): a natural isomorphism of functors commutes with placing an
  object in a single degree.
* `CategoryTheory.Iso.bijective_comp_comp_hom_iff`.
* `CategoryTheory.PullbackData.relHomDegreeZero_app_apply`: `relHomDegreeZero` is
  `degreeZeroHomEquiv` after composing with `singleComparison`.
* `CategoryTheory.PullbackData.bijective_relHomDegreeZero_app_iff`.

## References

* [Stacks Project, Tag 08JY](https://stacks.math.columbia.edu/tag/08JY)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace HomologicalComplex

/-- **A natural isomorphism of functors commutes with placing an object in a single degree**:
the degreewise image of `X[j]` under `e : F ≅ G`, read through `F(X[j]) ≅ (F X)[j]` and
`G(X[j]) ≅ (G X)[j]`, is `e_X[j]`. -/
theorem mapHomologicalComplex_hom_app_single_comp_singleMapHomologicalComplex_hom_app
    {W₁ W₂ : Type*} [Category* W₁] [Category* W₂] [HasZeroMorphisms W₁] [HasZeroMorphisms W₂]
    [HasZeroObject W₁] [HasZeroObject W₂] {F G : W₁ ⥤ W₂} [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (e : F ≅ G) {ι : Type*} (c : ComplexShape ι) [DecidableEq ι]
    (j : ι) (X : W₁) :
    (NatIso.mapHomologicalComplex e c).hom.app ((single W₁ c j).obj X) ≫
        (singleMapHomologicalComplex G c j).hom.app X =
      (singleMapHomologicalComplex F c j).hom.app X ≫ (single W₂ c j).map (e.hom.app X) := by
  apply to_single_hom_ext
  simp [singleMapHomologicalComplex_hom_app_self, single_map_f_self]

end HomologicalComplex

/-- **Composing with a morphism followed by an isomorphism is bijective exactly when composing
with the morphism is.** -/
theorem CategoryTheory.Iso.bijective_comp_comp_hom_iff {C : Type*} [Category* C] {Z X Y Y' : C}
    (f : X ⟶ Y) (e : Y ≅ Y') :
    Function.Bijective (fun ψ : Z ⟶ X => ψ ≫ f ≫ e.hom) ↔
      Function.Bijective (fun ψ : Z ⟶ X => ψ ≫ f) := by
  have h : (fun ψ : Z ⟶ X => ψ ≫ f ≫ e.hom) = e.homToEquiv ∘ (fun ψ : Z ⟶ X => ψ ≫ f) :=
    funext fun ψ => (Category.assoc _ _ _).symm
  rw [h]
  exact e.homToEquiv.bijective.of_comp_iff' _

namespace CategoryTheory.PullbackData

section DegreeZeroBijection

universe v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] {M : A → Type u₂} [∀ a, Category.{v₂} (M a)]
  [∀ a, Abelian (M a)] [∀ a, HasDerivedCategory.{v₂} (M a)]
  (P : PullbackData A M) [∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive]
  (L : ∀ {a b : A}, (a ⟶ b) → (DerivedCategory (M b) ⥤ DerivedCategory (M a)))
  (c : ∀ {a b : A} (f : a ⟶ b),
    DerivedCategory.Qh ⋙ L f ⟶ (P.toHomotopy).pull f ⋙ DerivedCategory.Qh)

/-- **The comparison of the left derived functor at a complex**, `L f (K) ⟶ f^*K` with the
pullback on the right taken degreewise: the comparison `c f` read through the identification
of the localization functors out of the complexes and out of the homotopy category. -/
def complexComparison {a b : A} (f : a ⟶ b) (K : CochainComplex (M b) ℤ) :
    (L f).obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj (((P.pull f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (L f).map ((DerivedCategory.quotientCompQhIso (M b)).inv.app K) ≫
    (c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj K) ≫
    (DerivedCategory.quotientCompQhIso (M a)).hom.app
      (((P.pull f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

/-- **The comparison at an object placed in degree zero is the comparison at the complex `N[0]`**,
followed by the identification of the degreewise pullback of `N[0]` with `(f^*N)[0]`. -/
theorem singleComparison_eq_complexComparison_comp {a b : A} (f : a ⟶ b) (N : M b) :
    singleComparison P L c f N =
      complexComparison P L c f ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).obj N) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex (P.pull f) (ComplexShape.up ℤ) 0).hom.app
            N) := by
  have h := (DerivedCategory.quotientCompQhIso (M a)).hom.naturality
    ((HomologicalComplex.singleMapHomologicalComplex (P.pull f) (ComplexShape.up ℤ) 0).hom.app N)
  dsimp only [Functor.comp_map] at h
  rw [singleComparison, complexComparison]
  exact (congrArg (fun t => (L f).map ((DerivedCategory.quotientCompQhIso (M b)).inv.app
      ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).obj N)) ≫
    (c f).app ((HomotopyCategory.quotient (M b) (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).obj N)) ≫ t) h).trans
    (congrArg (fun t => (L f).map ((DerivedCategory.quotientCompQhIso (M b)).inv.app
      ((HomologicalComplex.single (M b) (ComplexShape.up ℤ) 0).obj N)) ≫ t)
      (Category.assoc _ _ _).symm) |>.trans (Category.assoc _ _ _).symm

variable [hL : ∀ {a b : A} (f : a ⟶ b),
    (L f).IsLeftDerivedFunctor (c f) (HomotopyCategory.quasiIso (M b) (ComplexShape.up ℤ))]
  [hcomp : ∀ {a b d : A} (f : a ⟶ b) (g : b ⟶ d),
    IsIso (derivedComp (fun _ => DerivedCategory.Qh)
      (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c f g)]
  [hid : ∀ a : A, IsIso (derivedIdLift (fun _ => DerivedCategory.Qh)
      (fun a => HomotopyCategory.quasiIso (M a) (ComplexShape.up ℤ)) P.toHomotopy L c a)]

variable {I : Type*} [Category* I] {π : I ⥤ A} {a₀ : A} (κ : ConeTo π a₀)
  (E : DerivedCategory (M a₀)) {F : M a₀} (α : E ⟶ (DerivedCategory.singleFunctor (M a₀) 0).obj F)
  [hZ : ∀ i : I, ((L (κ.leg i)).obj E).IsLE 0]
  [hθ : ∀ i : I, IsIso (degreeZeroCompare P L c κ E α i)]

omit hL hcomp hid in
/-- **The degree-zero bijection** `Hom(L(κ i)^*E, ((κ i)^*G)[0]) ≃ Hom((κ i)^*F, (κ i)^*G)`:
degree-zero cohomology, which is bijective on morphisms from an object concentrated in degrees
`≤ 0` into an object placed in degree zero, followed by precomposition with the inverse of the
comparison `H⁰(L(κ i)^*E) ≅ (κ i)^*F` induced by `α`. -/
def degreeZeroHomEquiv (i : I) (G : M a₀) :
    ((L (κ.leg i)).obj E ⟶
        (DerivedCategory.singleFunctor (M (π.obj i)) 0).obj ((P.pull (κ.leg i)).obj G)) ≃
      ((P.pull (κ.leg i)).obj F ⟶ (P.pull (κ.leg i)).obj G) :=
  (Stacks.Sites.FibredCategory.homologyHomEquiv _ _).trans
    { toFun := fun φ => inv (degreeZeroCompare P L c κ E α i) ≫ φ
      invFun := fun ψ => degreeZeroCompare P L c κ E α i ≫ ψ
      left_inv := fun φ => by simp
      right_inv := fun ψ => by simp }

omit hL hcomp hid in
/-- The degree-zero bijection sends `φ` to its degree-zero cohomology precomposed with the inverse
of the comparison `H⁰(L(κ i)^*E) ≅ (κ i)^*F`. -/
theorem degreeZeroHomEquiv_apply (i : I) (G : M a₀)
    (φ : (L (κ.leg i)).obj E ⟶
      (DerivedCategory.singleFunctor (M (π.obj i)) 0).obj ((P.pull (κ.leg i)).obj G)) :
    degreeZeroHomEquiv P L c κ E α i G φ =
      inv (degreeZeroCompare P L c κ E α i) ≫
        Stacks.Sites.FibredCategory.homologyHomFun _ _ φ :=
  rfl

/-- **`relHomDegreeZero` is the degree-zero bijection after the comparison at `G[0]`**: it sends
`ψ : L(κ i)^*E ⟶ L(κ i)^*(G[0])` to `degreeZeroHomEquiv (ψ ≫ singleComparison)`. -/
theorem relHomDegreeZero_app_apply (hP : P.IsCoherent) (G : M a₀) (i : I)
    (ψ : (L (κ.leg i)).obj E ⟶ (L (κ.leg i)).obj ((DerivedCategory.singleFunctor (M a₀) 0).obj G)) :
    (relHomDegreeZero P L c κ E α hP G).app (Opposite.op i) ψ =
      degreeZeroHomEquiv P L c κ E α i G (ψ ≫ singleComparison P L c (κ.leg i) G) :=
  rfl

/-- **The degree-zero step of the bijectivity**: `relHomDegreeZero` is bijective at a test object
exactly when composing with the comparison `L(κ i)^*(G[0]) ⟶ ((κ i)^*G)[0]` is. -/
theorem bijective_relHomDegreeZero_app_iff (hP : P.IsCoherent) (G : M a₀) (i : I) :
    Function.Bijective ((relHomDegreeZero P L c κ E α hP G).app (Opposite.op i)) ↔
      Function.Bijective (fun ψ : (L (κ.leg i)).obj E ⟶
          (L (κ.leg i)).obj ((DerivedCategory.singleFunctor (M a₀) 0).obj G) =>
        ψ ≫ singleComparison P L c (κ.leg i) G) := by
  exact (degreeZeroHomEquiv P L c κ E α i G).bijective.of_comp_iff' _

end DegreeZeroBijection

end CategoryTheory.PullbackData
