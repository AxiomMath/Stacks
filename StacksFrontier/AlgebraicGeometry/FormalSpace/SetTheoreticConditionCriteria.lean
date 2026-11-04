module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# Criteria for the set-theoretic condition of Stacks 0AIS

Let `S` be a scheme contained in a big fppf site `B`. The set-theoretic condition of
**Stacks 0AIS** asks of an fppf sheaf `X` over `S` for an object `U` of the site with a
surjection `h_U ⟶ X` and an object `R` with a surjection `h_R ⟶ h_U ×_X h_U`. Remark 0AIS
derives it in two steps, which this file records in general form.

* *The first surjection.* If a family `h_{U i} ⟶ X` of maps out of represented sheaves is
  jointly surjective and the index set is not too large, then `U = ∐ U i` is an object of the
  site and `h_U ⟶ X` is a surjection. "Not too large" is
  `AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`: the index is `u`-small and of cardinality
  below the cofinality of the size cutoff of the site, which covers every countable index.
* *The second surjection.* If the diagonal of `X` is representable, then the kernel pair
  `h_U ×_X h_U` of any map from a represented sheaf is itself represented by an object of the
  site, so the second surjection may be taken to be an isomorphism.

## Main results

All in the namespace `AlgebraicGeometry.FormalSpace`.

* `exists_epi_uliftYoneda_of_satisfiesSetTheoreticCondition`: the set-theoretic condition
  provides a surjection from the sheaf represented by an object of the site.
* `exists_epi_uliftYoneda_sigmaObj`: a jointly surjective family of maps out of represented
  sheaves, indexed by an admissible index, assembles into a surjection out of the sheaf
  represented by the coproduct.
* `satisfiesSetTheoreticCondition_of_epi_of_relativelyRepresentable_diag`: a sheaf with
  representable diagonal which receives a surjection from a represented sheaf satisfies the
  set-theoretic condition.
* `satisfiesSetTheoreticCondition_of_jointlyEpi_of_relativelyRepresentable_diag`: the two steps
  together.

## Implementation notes

Joint surjectivity of a family `f i : h_{U i} ⟶ X` is stated as joint epimorphy (two maps out
of `X` agreeing after every `f i` are equal), so that no coproduct of sheaves indexed by a type
of arbitrary universe has to be formed. The representable diagonal is
`CategoryTheory.Functor.relativelyRepresentable` for the sheafified Yoneda embedding, which is
the form in which Stacks 0AI8 is stated in
`AlgebraicGeometry.FormalSpace.diagonal_isClosedImmersion`; Mathlib's
`CategoryTheory.Functor.relativelyRepresentable.of_diag` turns it into representability of every
map from a represented sheaf.

## References

* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The set-theoretic condition of Stacks 0AIS provides a surjection onto the sheaf from the
sheaf represented by an object of the site. -/
theorem exists_epi_uliftYoneda_of_satisfiesSetTheoreticCondition
    {X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (hX : SatisfiesSetTheoreticCondition B S hS X) :
    letI : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
    ∃ (U : BigFppfOver B S hS)
      (t : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ X), Epi t := by
  let J := BigFppfOver.topology B S hS
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨U, -, hU, -, ⟨eU⟩, -, a, ha, -, -⟩ := hX
  let eS : J.uliftYoneda.{u + 1}.obj U ≅ hU :=
    (fullyFaithfulSheafToPresheaf J (Type (u + 1))).preimageIso
      (J.uliftYonedaCompSheafToPresheaf.{u + 1}.app U ≪≫ eU.symm)
  exact ⟨U, eS.hom ≫ a, epi_comp eS.hom a⟩

variable (B S hS)

/-- **The first surjection of Remark 0AIS.** Let `f i : h_{U i} ⟶ X` be a jointly surjective
family of maps from sheaves represented by objects of the site, indexed by a set which is not
too large (an admissible index, for instance a countable one). Then the coproduct
`∐ U i` is an object of the site, and the induced map from the sheaf it represents is a
surjection onto `X` restricting to `f i` on the `i`-th summand. -/
theorem exists_epi_uliftYoneda_sigmaObj {I : Type v} [Small.{u} I] [B.AdmitsCoproductIndex I]
    (U : I → BigFppfOver B S hS) {X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (f : ∀ i,
      letI : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
      (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj (U i) ⟶ X)
    (hf : ∀ ⦃Z : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))⦄ (g g' : X ⟶ Z),
      (∀ i, f i ≫ g = f i ≫ g') → g = g') :
    letI : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
    ∃ t : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj
        (BigFppfOver.sigmaObj B S hS U) ⟶ X,
      Epi t ∧ ∀ i, (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map
        (BigFppfOver.sigmaIncl B S hS U i) ≫ t = f i := by
  let : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let hc := BigFppfOver.isColimitUliftYonedaSigmaCofan B S hS U
  let t := Cofan.IsColimit.desc hc f
  have ht : ∀ i, (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map
      (BigFppfOver.sigmaIncl B S hS U i) ≫ t = f i := Cofan.IsColimit.fac hc f
  refine ⟨t, ⟨fun {Z} g g' hgg' ↦ hf g g' fun i ↦ ?_⟩, ht⟩
  rw [← ht i, Category.assoc, Category.assoc, hgg']

/-- **The second surjection of Remark 0AIS.** A sheaf whose diagonal is representable, and
which receives a surjection `t : h_U ⟶ X` from the sheaf of an object `U` of the site, satisfies
the set-theoretic condition: the kernel pair `h_U ×_X h_U` is the base change of the diagonal
along `h_U ⨯ h_U ⟶ X ⨯ X`, hence is represented by an object `R` of the site, and the second
surjection is the isomorphism `h_R ≅ h_U ×_X h_U`. -/
theorem satisfiesSetTheoreticCondition_of_epi_of_relativelyRepresentable_diag
    {X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} {U : BigFppfOver B S hS}
    (t : letI : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
      (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ X) [Epi t]
    (hdiag : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (diag X)) :
    SatisfiesSetTheoreticCondition B S hS X := by
  let J := BigFppfOver.topology B S hS
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let G := Sheaf.sheafifiedYoneda J
  let eG : G ≅ J.uliftYoneda.{u + 1} := Sheaf.sheafifiedYonedaIsoUliftYoneda' J
  let : PreservesLimitsOfShape (Discrete WalkingPair)
      (J.uliftYoneda.{u + 1} ⋙ sheafToPresheaf J (Type (u + 1))) :=
    preservesLimitsOfShape_of_natIso J.uliftYonedaCompSheafToPresheaf.{u + 1}.symm
  let : PreservesLimitsOfShape (Discrete WalkingPair) J.uliftYoneda.{u + 1} :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J (Type (u + 1)))
  let : PreservesLimitsOfShape (Discrete WalkingPair) G :=
    preservesLimitsOfShape_of_natIso eG.symm
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let t' : G.obj U ⟶ X := eG.hom.app U ≫ t
  have hrep := Functor.relativelyRepresentable.of_diag hdiag t'
  let R := hrep.pullback t'
  let g : J.uliftYoneda.{u + 1}.obj R ⟶ pullback t t :=
    eG.inv.app R ≫ (hrep.isPullback t').isoPullback.hom ≫
      pullback.map t' t' t t (eG.hom.app U) (eG.hom.app U) (𝟙 X) (by simp [t']) (by simp [t'])
  have hg : IsIso g := by
    dsimp only [g]
    infer_instance
  exact ⟨U, R, J.uliftYoneda.{u + 1}.obj U, J.uliftYoneda.{u + 1}.obj R,
    ⟨J.uliftYonedaCompSheafToPresheaf.{u + 1}.app U⟩,
    ⟨J.uliftYonedaCompSheafToPresheaf.{u + 1}.app R⟩, t, inferInstance, g, inferInstance⟩

/-- **Remark 0AIS, both steps.** A sheaf with representable diagonal which receives a jointly
surjective family of maps from sheaves represented by objects of the site, indexed by a set
which is not too large, satisfies the set-theoretic condition. -/
theorem satisfiesSetTheoreticCondition_of_jointlyEpi_of_relativelyRepresentable_diag
    {I : Type v} [Small.{u} I] [B.AdmitsCoproductIndex I]
    (U : I → BigFppfOver B S hS) {X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (f : ∀ i,
      letI : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
      (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj (U i) ⟶ X)
    (hf : ∀ ⦃Z : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))⦄ (g g' : X ⟶ Z),
      (∀ i, f i ≫ g = f i ≫ g') → g = g')
    (hdiag : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (diag X)) :
    SatisfiesSetTheoreticCondition B S hS X := by
  obtain ⟨t, ht, -⟩ := exists_epi_uliftYoneda_sigmaObj B S hS U f hf
  exact satisfiesSetTheoreticCondition_of_epi_of_relativelyRepresentable_diag B S hS t hdiag

end AlgebraicGeometry.FormalSpace

end
