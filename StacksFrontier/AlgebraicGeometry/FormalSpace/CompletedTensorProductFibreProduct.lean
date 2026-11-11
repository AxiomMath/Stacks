module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletedTensorProductStages
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedQuotientsPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageBaseChangeColimit
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.Thickenings.NilIdeal
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Limits.RelativeProductOfColimits
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Adic
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.WeakIdealStages

/-!
# Clause (3) of Stacks 0AN3: the fibre product of McQuillan affine formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, let `A`, `B` and `C` be weakly admissible
topological rings over `S` and let `C ⟶ A` and `C ⟶ B` be continuous homomorphisms over `S`.
**Stacks 0AN3, clause (3)** says that

`Spf A ×_{Spf C} Spf B = Spf (A ⊗̂_C B)`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.CompletedTensorProductData`: the data of the three rings with
  their quotient systems and the two continuous homomorphisms.
* `AlgebraicGeometry.FormalSpace.CompletedTensorProductData.baseIdeal`: the weak ideal of
  definition of `C` attached to a pair of weak ideals of definition of `A` and `B`.
* `AlgebraicGeometry.FormalSpace.CompletedTensorProductData.tensorStageDiagram`: the diagram of
  affine stages `Spec (A ⧸ i ⊗_C B ⧸ j)`, indexed by pairs of weak ideals of definition.

## Main results

* `AlgebraicGeometry.FormalSpace.CompletedTensorProductData.isPullback_tensorStage`: each stage
  of that diagram is the fibre product of the corresponding stages of `Spf A` and `Spf B` over
  `Spf C`.
* `AlgebraicGeometry.FormalSpace.exists_formalSpectrum_completedTensorProduct`:
  **Stacks 0AN3, clause (3)**, at the hypotheses of the source.

## Implementation notes

The stage attached to a pair `(i, j)` of weak ideals of definition is the fibre product of
`Spec (A ⧸ i)` and `Spec (B ⧸ j)` over `Spec (C ⧸ l)`, where `l` is an auxiliary weak ideal of
definition of `C` mapping into both `i` and `j`; its coordinate ring is `A ⧸ i ⊗_C B ⧸ j`
(`AlgebraicGeometry.isPullback_specQuotientTensor`), which by
`StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.WeakIdealStages` is the
quotient of `A ⊗̂_C B` by a weak ideal of definition, these quotients being cofinal.

That the stage is also the fibre product over the whole of `Spf C`, and not only over the stage
`Spec (C ⧸ l)`, is because the stage inclusion `Spec (C ⧸ l) ⟶ Spf C` is a monomorphism — the
transition morphisms of the presenting diagram are closed immersions and a filtered colimit of
sheaves of sets is computed pointwise — so cancelling it does not change the fibre product
(`CategoryTheory.isPullback_of_comp_mono`). No cofinality of the auxiliary ideals is needed:
`l` is a function of `(i, j)` and the two diagrams it mediates between are never compared.

The fibre product of the two formal spectra is then the colimit of the stages by
`CategoryTheory.Limits.isColimit_relativeProductCocone`, the canonical presentations of `Spf A`
and of `Spf B` being universal colimits
(`AlgebraicGeometry.FormalSpace.isUniversalColimit_formalSpectrumDiagram`), and the recognition
statement
`AlgebraicGeometry.FormalSpace.DirectedQuotients.exists_quotientSystem_formalSpectrum_iso` — the
implication (4) ⇒ (1) of Stacks 0AIC for a directed presentation — identifies that colimit with
`Spf (A ⊗̂_C B)`.

Separatedness of `Spf C`, the standing hypothesis of Stacks 0AN3, is not used: the fibre
products of the affine stages are affine for free, their base `Spec (C ⧸ l)` being affine. It is
kept in the statement because it is the hypothesis the source makes.

## References

* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AMU](https://stacks.math.columbia.edu/tag/0AMU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.FormalSpace

universe u

/-- Replacing the two legs of a cartesian square by equal morphisms. -/
private theorem isPullback_congr_cospan {Q : Type*} [Category Q] {W X Y Z : Q} {fst : W ⟶ X}
    {snd : W ⟶ Y} {f f' : X ⟶ Z} {g g' : Y ⟶ Z} (hf : f = f') (hg : g = g')
    (h : IsPullback fst snd f g) : IsPullback fst snd f' g' := by
  subst hf; subst hg; exact h

/-- If two composites agree after the projection `πq`, given compatible projections, then they are
equal. -/
private theorem comp_eq_comp_of_comp_eq {Q : Type*} [Category Q] {X X' T T' Y Y' : Q}
    {m : X ⟶ X'} {iq : X' ⟶ T'} {ip : X ⟶ T} {t : T ⟶ T'} {πp : T ⟶ Y} {πq : T' ⟶ Y'}
    {φ : Y ⟶ Y'} {fp : X ⟶ Y} {fq : X' ⟶ Y'} (hp : ip ≫ πp = fp) (hq : iq ≫ πq = fq)
    (ht : t ≫ πq = πp ≫ φ) (hm : m ≫ fq = fp ≫ φ) : (m ≫ iq) ≫ πq = (ip ≫ t) ≫ πq := by
  rw [Category.assoc, hq, hm, Category.assoc, ht, ← Category.assoc, hp]

/-- Two morphisms of stages of quotient systems are equal when their underlying morphisms of
schemes are. -/
private theorem stage_hom_ext {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {R Q : Type u} [CommRing R] [TopologicalSpace R] [CommRing Q] [TopologicalSpace Q]
    {D : QuotientSystem B S hS R} {E : QuotientSystem B S hS Q}
    {J : TopologicalRing.WeakIdealOfDefinitionIndex R}
    {K : TopologicalRing.WeakIdealOfDefinitionIndex Q} {f g : D.stage J ⟶ E.stage K}
    (h : (Over.Hom.left f.hom).hom = (Over.Hom.left g.hom).hom) : f = g := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact h

/-- A continuous homomorphism of topological rings over `S` is compatible with the transition
morphisms of the two quotient systems. -/
theorem ContinuousHom.stageMap_comp_transition {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {R Q : Type u} [CommRing R] [TopologicalSpace R] [CommRing Q]
    [TopologicalSpace Q] {D : QuotientSystem B S hS R} {E : QuotientSystem B S hS Q}
    (f : ContinuousHom D E) {J J' : TopologicalRing.WeakIdealOfDefinitionIndex R}
    {K K' : TopologicalRing.WeakIdealOfDefinitionIndex Q} (hJ : J'.1 ≤ J.1) (hK : K'.1 ≤ K.1)
    (h : J.1 ≤ Ideal.comap f.toRingHom K.1) (h' : J'.1 ≤ Ideal.comap f.toRingHom K'.1) :
    f.stageMap J K h ≫ D.transition hJ = E.transition hK ≫ f.stageMap J' K' h' := by
  apply stage_hom_ext
  change Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 f.toRingHom h)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJ)) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hK)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap K'.1 f.toRingHom h'))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
  simp

/-- A transition morphism of a quotient system along the identity inclusion of ideals is the
identity. -/
theorem QuotientSystem.transition_refl {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {R : Type u} [CommRing R] [TopologicalSpace R]
    (D : QuotientSystem B S hS R) {J : TopologicalRing.WeakIdealOfDefinitionIndex R}
    (h : J.1 ≤ J.1) : D.transition h = 𝟙 (D.stage J) := by
  apply stage_hom_ext
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) = 𝟙 _
  rw [← Spec.map_id, Spec.map_inj]
  exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a => by simp))

/-- Two transition morphisms of a quotient system compose to the transition morphism of the
composite inclusion of ideals. -/
theorem QuotientSystem.transition_comp {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {R : Type u} [CommRing R] [TopologicalSpace R]
    (D : QuotientSystem B S hS R) {J J' J'' : TopologicalRing.WeakIdealOfDefinitionIndex R}
    (h : J'.1 ≤ J.1) (h' : J''.1 ≤ J'.1) :
    D.transition h ≫ D.transition h' = D.transition (h'.trans h) := by
  apply stage_hom_ext
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h')) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (h'.trans h)))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
  simp

/-- The transition of two quotient tensor products attached to inclusions of the two ideals. -/
def quotientTensorTransition (C : Type u) {A B : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra C A] [Algebra C B] {i i' : Ideal A} {j j' : Ideal B} (hi : i' ≤ i) (hj : j' ≤ j) :
    ((A ⧸ i') ⊗[C] (B ⧸ j')) →+* ((A ⧸ i) ⊗[C] (B ⧸ j)) :=
  (Algebra.TensorProduct.map (Ideal.Quotient.factorₐ C hi)
    (Ideal.Quotient.factorₐ C hj)).toRingHom

/-- The transition of two quotient tensor products is surjective. -/
theorem quotientTensorTransition_surjective (C : Type u) {A B : Type u} [CommRing A] [CommRing B]
    [CommRing C] [Algebra C A] [Algebra C B] {i i' : Ideal A} {j j' : Ideal B} (hi : i' ≤ i)
    (hj : j' ≤ j) : Function.Surjective (quotientTensorTransition C hi hj) :=
  Algebra.TensorProduct.map_surjective _ _
    (Ideal.Quotient.factor_surjective hi) (Ideal.Quotient.factor_surjective hj)

/-- The transition of quotient tensor products restricts on the left factor to the factor map
`A ⧸ i' → A ⧸ i`. -/
theorem quotientTensorTransition_comp_includeLeft (C : Type u) {A B : Type u} [CommRing A]
    [CommRing B] [CommRing C] [Algebra C A] [Algebra C B] {i i' : Ideal A} {j j' : Ideal B}
    (hi : i' ≤ i) (hj : j' ≤ j) :
    (quotientTensorTransition C hi hj).comp
        (Algebra.TensorProduct.includeLeftRingHom : (A ⧸ i') →+* (A ⧸ i') ⊗[C] (B ⧸ j')) =
      (Algebra.TensorProduct.includeLeftRingHom :
        (A ⧸ i) →+* (A ⧸ i) ⊗[C] (B ⧸ j)).comp (Ideal.Quotient.factor hi) :=
  RingHom.ext fun x => by
    simp [quotientTensorTransition, Algebra.TensorProduct.includeLeftRingHom]

/-- The transition of quotient tensor products restricts on the right factor to the factor map
`B ⧸ j' → B ⧸ j`. -/
theorem quotientTensorTransition_comp_includeRight (C : Type u) {A B : Type u} [CommRing A]
    [CommRing B] [CommRing C] [Algebra C A] [Algebra C B] {i i' : Ideal A} {j j' : Ideal B}
    (hi : i' ≤ i) (hj : j' ≤ j) :
    (quotientTensorTransition C hi hj).comp
        ((Algebra.TensorProduct.includeRight :
          (B ⧸ j') →ₐ[C] (A ⧸ i') ⊗[C] (B ⧸ j')).toRingHom) =
      ((Algebra.TensorProduct.includeRight :
        (B ⧸ j) →ₐ[C] (A ⧸ i) ⊗[C] (B ⧸ j)).toRingHom).comp (Ideal.Quotient.factor hj) :=
  RingHom.ext fun x => by
    simp [quotientTensorTransition]

/-! ### The index of the presentation -/

/-- The index of the presentation of a fibre product of two formal spectra: pairs consisting of
a weak ideal of definition of `A` and one of `B`, ordered by reverse inclusion in each. This is
a type synonym for the product of the two index orders, so that the category structure it
carries is the one of its own preorder and not the product of the two preorder categories; the
comparison of the two is
`AlgebraicGeometry.FormalSpace.tensorIndexEquivalence`. -/
def TensorIndex (A B : Type u) [CommRing A] [TopologicalSpace A] [CommRing B]
    [TopologicalSpace B] : Type u :=
  WeakIdeals A × WeakIdeals B

section

variable (A B : Type u) [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]

/-- The index is ordered as the product of the two orders of weak ideals of definition. -/
instance : Preorder (TensorIndex A B) :=
  inferInstanceAs (Preorder (WeakIdeals A × WeakIdeals B))

/-- The index is `u + 1`-small. -/
instance : Small.{u + 1} (TensorIndex A B) :=
  inferInstanceAs (Small.{u + 1} (WeakIdeals A × WeakIdeals B))

/-- The first component of an index. -/
abbrev TensorIndex.fst (p : TensorIndex A B) : WeakIdeals A :=
  Prod.fst (α := WeakIdeals A) (β := WeakIdeals B) p

/-- The second component of an index. -/
abbrev TensorIndex.snd (p : TensorIndex A B) : WeakIdeals B :=
  Prod.snd (α := WeakIdeals A) (β := WeakIdeals B) p

/-- The weak ideal of definition of `A` attached to an index. -/
abbrev TensorIndex.left (p : TensorIndex A B) : TopologicalRing.WeakIdealOfDefinitionIndex A :=
  OrderDual.ofDual (Prod.fst (α := WeakIdeals A) (β := WeakIdeals B) p)

/-- The weak ideal of definition of `B` attached to an index. -/
abbrev TensorIndex.right (p : TensorIndex A B) : TopologicalRing.WeakIdealOfDefinitionIndex B :=
  OrderDual.ofDual (Prod.snd (α := WeakIdeals A) (β := WeakIdeals B) p)

/-- The first projection of the index is monotone. -/
theorem monotone_tensorIndexLeft :
    Monotone (fun p : TensorIndex A B => (Prod.fst (α := WeakIdeals A) (β := WeakIdeals B) p)) :=
  fun _ _ h => h.1

/-- The second projection of the index is monotone. -/
theorem monotone_tensorIndexRight :
    Monotone (fun p : TensorIndex A B => (Prod.snd (α := WeakIdeals A) (β := WeakIdeals B) p)) :=
  fun _ _ h => h.2

/-- The comparison of the preorder category of the index with the product of the two preorder
categories: the identity on objects, and on morphisms the splitting of an inequality of pairs
into a pair of inequalities. Both categories are thin with the same hom-sets nonempty, so this
is an equivalence. -/
def tensorIndexEquivalence : TensorIndex A B ≌ WeakIdeals A × WeakIdeals B where
  functor :=
    { obj := fun p => p
      map := fun f => (homOfLE (leOfHom f).1, homOfLE (leOfHom f).2)
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  inverse :=
    { obj := fun p => p
      map := fun f => homOfLE ⟨leOfHom f.1, leOfHom f.2⟩
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  functor_unitIso_comp := fun _ => rfl

/-- The comparison functor is the identity on objects. -/
@[simp]
theorem tensorIndexEquivalence_functor_obj (p : TensorIndex A B) :
    (tensorIndexEquivalence A B).functor.obj p = p := rfl

/-- The first component of the comparison functor on a morphism. -/
theorem tensorIndexEquivalence_functor_map_fst {p q : TensorIndex A B} (f : p ⟶ q) :
    ((tensorIndexEquivalence A B).functor.map f).1 = homOfLE (leOfHom f).1 := rfl

/-- The second component of the comparison functor on a morphism. -/
theorem tensorIndexEquivalence_functor_map_snd {p q : TensorIndex A B} (f : p ⟶ q) :
    ((tensorIndexEquivalence A B).functor.map f).2 = homOfLE (leOfHom f).2 := rfl

end


/-- The data presenting two morphisms of McQuillan affine formal algebraic spaces to a third:
three weakly admissible topological rings with their quotient systems over `S`, and two
continuous homomorphisms out of the base realising the algebra structures. -/
structure CompletedTensorProductData (𝔅 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝔅.Contains S)
    (A B C : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] [Algebra C A] [Algebra C B] where
  /-- The first ring is weakly admissible. -/
  weaklyAdmissibleLeft : TopologicalRing.IsWeaklyAdmissible A
  /-- The second ring is weakly admissible. -/
  weaklyAdmissibleRight : TopologicalRing.IsWeaklyAdmissible B
  /-- The base ring is weakly admissible. -/
  weaklyAdmissibleBase : TopologicalRing.IsWeaklyAdmissible C
  /-- The quotient system making the first ring a ring over `S`. -/
  systemLeft : QuotientSystem 𝔅 S hS A
  /-- The quotient system making the second ring a ring over `S`. -/
  systemRight : QuotientSystem 𝔅 S hS B
  /-- The quotient system making the base ring a ring over `S`. -/
  systemBase : QuotientSystem 𝔅 S hS C
  /-- The continuous homomorphism from the base to the first ring. -/
  toLeft : ContinuousHom systemBase systemLeft
  /-- The continuous homomorphism from the base to the second ring. -/
  toRight : ContinuousHom systemBase systemRight
  /-- The first algebra structure is the one given by `toLeft`. -/
  algebraMap_eq_left : algebraMap C A = toLeft.toRingHom
  /-- The second algebra structure is the one given by `toRight`. -/
  algebraMap_eq_right : algebraMap C B = toRight.toRingHom

namespace CompletedTensorProductData

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S} {A B C : Type u}
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
  [Algebra C A] [Algebra C B] (P : CompletedTensorProductData 𝔅 S hS A B C)

/-! ### The auxiliary weak ideal of definition of the base -/

/-- The weak ideal of definition of the base attached to a pair of weak ideals of definition of
the two rings: the intersection of a chosen weak ideal of definition with the two preimages. -/
def baseIdeal (i : TopologicalRing.WeakIdealOfDefinitionIndex A)
    (j : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    TopologicalRing.WeakIdealOfDefinitionIndex C :=
  ⟨P.weaklyAdmissibleBase.1.choose ⊓ Ideal.comap P.toLeft.toRingHom i.1 ⊓
      Ideal.comap P.toRight.toRingHom j.1,
    TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right
      (TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right
        P.weaklyAdmissibleBase.1.choose_spec (i.2.1.preimage P.toLeft.continuous))
      (j.2.1.preimage P.toRight.continuous)⟩

/-- The auxiliary ideal of the base lies in the preimage of the given ideal of `A`. -/
theorem baseIdeal_le_comap_left (i : TopologicalRing.WeakIdealOfDefinitionIndex A)
    (j : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    (P.baseIdeal i j).1 ≤ Ideal.comap P.toLeft.toRingHom i.1 :=
  inf_le_left.trans inf_le_right

/-- The auxiliary ideal of the base lies in the preimage of the given ideal of `B`. -/
theorem baseIdeal_le_comap_right (i : TopologicalRing.WeakIdealOfDefinitionIndex A)
    (j : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    (P.baseIdeal i j).1 ≤ Ideal.comap P.toRight.toRingHom j.1 :=
  inf_le_right

/-- The auxiliary ideal of the base lies in the preimage of the given ideal of `A` under
`algebraMap C A`. -/
theorem baseIdeal_le_comap_algebraMap_left (i : TopologicalRing.WeakIdealOfDefinitionIndex A)
    (j : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    (P.baseIdeal i j).1 ≤ Ideal.comap (algebraMap C A) i.1 := by
  rw [P.algebraMap_eq_left]; exact P.baseIdeal_le_comap_left i j

/-- The auxiliary ideal of the base lies in the preimage of the given ideal of `B` under
`algebraMap C B`. -/
theorem baseIdeal_le_comap_algebraMap_right (i : TopologicalRing.WeakIdealOfDefinitionIndex A)
    (j : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    (P.baseIdeal i j).1 ≤ Ideal.comap (algebraMap C B) j.1 := by
  rw [P.algebraMap_eq_right]; exact P.baseIdeal_le_comap_right i j

/-- The auxiliary ideal of the base shrinks when the two ideals shrink. -/
theorem baseIdeal_antitone {i i' : TopologicalRing.WeakIdealOfDefinitionIndex A}
    {j j' : TopologicalRing.WeakIdealOfDefinitionIndex B} (hi : i'.1 ≤ i.1) (hj : j'.1 ≤ j.1) :
    (P.baseIdeal i' j').1 ≤ (P.baseIdeal i j).1 :=
  inf_le_inf (inf_le_inf le_rfl (Ideal.comap_mono hi)) (Ideal.comap_mono hj)

/-! ### The stages and their coordinate rings -/

/-- The morphism from a stage of the first spectrum to the auxiliary stage of the base. -/
def leftStageMap (i : TopologicalRing.WeakIdealOfDefinitionIndex A)
    (j : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    P.systemLeft.stage i ⟶ P.systemBase.stage (P.baseIdeal i j) :=
  P.toLeft.stageMap (P.baseIdeal i j) i (P.baseIdeal_le_comap_left i j)

/-- The morphism from a stage of the second spectrum to the auxiliary stage of the base. -/
def rightStageMap (i : TopologicalRing.WeakIdealOfDefinitionIndex A)
    (j : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    P.systemRight.stage j ⟶ P.systemBase.stage (P.baseIdeal i j) :=
  P.toRight.stageMap (P.baseIdeal i j) j (P.baseIdeal_le_comap_right i j)

/-- The scheme morphism underlying `leftStageMap` is `Spec` of the quotient map of
`algebraMap C A`. -/
theorem toScheme_leftStageMap (i : TopologicalRing.WeakIdealOfDefinitionIndex A)
    (j : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    (BigFppfOver.toScheme 𝔅 S hS).map
        ((BigAffineFppf.inclusion 𝔅 S hS).map (P.leftStageMap i j)) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap i.1 (algebraMap C A)
        (P.baseIdeal_le_comap_algebraMap_left i j))) := by
  have hring : Ideal.quotientMap i.1 P.toLeft.toRingHom (P.baseIdeal_le_comap_left i j) =
      Ideal.quotientMap i.1 (algebraMap C A)
        (P.baseIdeal_le_comap_algebraMap_left i j) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun c => ?_)
    simp [Ideal.quotientMap_mk, P.algebraMap_eq_left]
  change Spec.map (CommRingCat.ofHom
    (Ideal.quotientMap i.1 P.toLeft.toRingHom (P.baseIdeal_le_comap_left i j))) = _
  rw [hring]

/-- The scheme morphism underlying `rightStageMap` is `Spec` of the quotient map of
`algebraMap C B`. -/
theorem toScheme_rightStageMap (i : TopologicalRing.WeakIdealOfDefinitionIndex A)
    (j : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    (BigFppfOver.toScheme 𝔅 S hS).map
        ((BigAffineFppf.inclusion 𝔅 S hS).map (P.rightStageMap i j)) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap j.1 (algebraMap C B)
        (P.baseIdeal_le_comap_algebraMap_right i j))) := by
  have hring : Ideal.quotientMap j.1 P.toRight.toRingHom (P.baseIdeal_le_comap_right i j) =
      Ideal.quotientMap j.1 (algebraMap C B)
        (P.baseIdeal_le_comap_algebraMap_right i j) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun c => ?_)
    simp [Ideal.quotientMap_mk, P.algebraMap_eq_right]
  change Spec.map (CommRingCat.ofHom
    (Ideal.quotientMap j.1 P.toRight.toRingHom (P.baseIdeal_le_comap_right i j))) = _
  rw [hring]

omit [IsTopologicalRing A] [IsLinearTopology A A] [IsTopologicalRing B] [IsLinearTopology B B] in
/-- The inclusion of weak ideals of `A` underlying a morphism of the index. -/
theorem le_left_of_tensorIndex_hom {p q : TensorIndex A B} (f : p ⟶ q) :
    (TensorIndex.left A B q).1 ≤ (TensorIndex.left A B p).1 := (leOfHom f).1

omit [IsTopologicalRing A] [IsLinearTopology A A] [IsTopologicalRing B] [IsLinearTopology B B] in
/-- The inclusion of weak ideals of `B` underlying a morphism of the index. -/
theorem le_right_of_tensorIndex_hom {p q : TensorIndex A B} (f : p ⟶ q) :
    (TensorIndex.right A B q).1 ≤ (TensorIndex.right A B p).1 := (leOfHom f).2

/-- The auxiliary weak ideals of definition of the base decrease along the index. -/
theorem monotone_baseIdeal :
    Monotone (fun p : TensorIndex A B =>
      (OrderDual.toDual (P.baseIdeal (TensorIndex.left A B p) (TensorIndex.right A B p)) :
        WeakIdeals C)) :=
  fun _ _ h => P.baseIdeal_antitone h.1 h.2

/-! ### The stages of the fibre product -/

/-- The diagram of stages of `Spf A`, indexed by pairs of weak ideals of definition. -/
def leftStageDiagram : TensorIndex A B ⥤ BigFppfOver 𝔅 S hS :=
  (monotone_tensorIndexLeft A B).functor ⋙ P.systemLeft.diagram ⋙
    BigAffineFppf.inclusion 𝔅 S hS

/-- The diagram of stages of `Spf B`, indexed by pairs of weak ideals of definition. -/
def rightStageDiagram : TensorIndex A B ⥤ BigFppfOver 𝔅 S hS :=
  (monotone_tensorIndexRight A B).functor ⋙ P.systemRight.diagram ⋙
    BigAffineFppf.inclusion 𝔅 S hS

/-- The diagram of auxiliary stages of `Spf C`, indexed by pairs of weak ideals of
definition. -/
def baseStageDiagram : TensorIndex A B ⥤ BigFppfOver 𝔅 S hS :=
  P.monotone_baseIdeal.functor ⋙ P.systemBase.diagram ⋙ BigAffineFppf.inclusion 𝔅 S hS

/-- The transitions of `leftStageDiagram` are those of the quotient system of `A`. -/
@[simp]
theorem leftStageDiagram_map {p q : TensorIndex A B} (f : p ⟶ q) :
    P.leftStageDiagram.map f = (BigAffineFppf.inclusion 𝔅 S hS).map
      (P.systemLeft.transition (le_left_of_tensorIndex_hom f)) := rfl

/-- The transitions of `rightStageDiagram` are those of the quotient system of `B`. -/
@[simp]
theorem rightStageDiagram_map {p q : TensorIndex A B} (f : p ⟶ q) :
    P.rightStageDiagram.map f = (BigAffineFppf.inclusion 𝔅 S hS).map
      (P.systemRight.transition (le_right_of_tensorIndex_hom f)) := rfl

/-- The transitions of `baseStageDiagram` are those of the quotient system of `C`. -/
@[simp]
theorem baseStageDiagram_map {p q : TensorIndex A B} (f : p ⟶ q) :
    P.baseStageDiagram.map f = (BigAffineFppf.inclusion 𝔅 S hS).map
      (P.systemBase.transition (P.baseIdeal_antitone (le_left_of_tensorIndex_hom f)
        (le_right_of_tensorIndex_hom f))) := rfl

/-- The morphisms from the stages of `Spf A` to the auxiliary stages of `Spf C`. -/
def leftStageProjection : P.leftStageDiagram ⟶ P.baseStageDiagram where
  app p := (BigAffineFppf.inclusion 𝔅 S hS).map
    (P.leftStageMap (TensorIndex.left A B p) (TensorIndex.right A B p))
  naturality p q f := by
    refine ((BigAffineFppf.inclusion 𝔅 S hS).map_comp _ _).symm.trans
      (Eq.trans ?_ ((BigAffineFppf.inclusion 𝔅 S hS).map_comp _ _))
    exact congrArg (BigAffineFppf.inclusion 𝔅 S hS).map
      (P.toLeft.stageMap_comp_transition
        (P.baseIdeal_antitone (le_left_of_tensorIndex_hom f) (le_right_of_tensorIndex_hom f))
        (le_left_of_tensorIndex_hom f) (P.baseIdeal_le_comap_left _ _)
        (P.baseIdeal_le_comap_left _ _)).symm

/-- The morphisms from the stages of `Spf B` to the auxiliary stages of `Spf C`. -/
def rightStageProjection : P.rightStageDiagram ⟶ P.baseStageDiagram where
  app p := (BigAffineFppf.inclusion 𝔅 S hS).map
    (P.rightStageMap (TensorIndex.left A B p) (TensorIndex.right A B p))
  naturality p q f := by
    refine ((BigAffineFppf.inclusion 𝔅 S hS).map_comp _ _).symm.trans
      (Eq.trans ?_ ((BigAffineFppf.inclusion 𝔅 S hS).map_comp _ _))
    exact congrArg (BigAffineFppf.inclusion 𝔅 S hS).map
      (P.toRight.stageMap_comp_transition
        (P.baseIdeal_antitone (le_left_of_tensorIndex_hom f) (le_right_of_tensorIndex_hom f))
        (le_right_of_tensorIndex_hom f) (P.baseIdeal_le_comap_right _ _)
        (P.baseIdeal_le_comap_right _ _)).symm

/-- The components of `leftStageProjection` are the morphisms `leftStageMap`. -/
@[simp]
theorem leftStageProjection_app (p : TensorIndex A B) :
    P.leftStageProjection.app p = (BigAffineFppf.inclusion 𝔅 S hS).map
      (P.leftStageMap (TensorIndex.left A B p) (TensorIndex.right A B p)) := rfl

/-- The components of `rightStageProjection` are the morphisms `rightStageMap`. -/
@[simp]
theorem rightStageProjection_app (p : TensorIndex A B) :
    P.rightStageProjection.app p = (BigAffineFppf.inclusion 𝔅 S hS).map
      (P.rightStageMap (TensorIndex.left A B p) (TensorIndex.right A B p)) := rfl

/-- The diagram of stages of the fibre product in the big fppf site: the fibre products of the
two stage diagrams over the auxiliary stage diagram of the base. -/
def tensorStageDiagramOver : TensorIndex A B ⥤ BigFppfOver 𝔅 S hS :=
  haveI := hasPullbacks_bigFppfOver 𝔅 S hS
  fibreProductDiagram P.leftStageProjection P.rightStageProjection

/-- The first projection of the diagram of stages of the fibre product. -/
def tensorStageFst : P.tensorStageDiagramOver ⟶ P.leftStageDiagram :=
  haveI := hasPullbacks_bigFppfOver 𝔅 S hS
  fibreProductDiagramFst P.leftStageProjection P.rightStageProjection

/-- The second projection of the diagram of stages of the fibre product. -/
def tensorStageSnd : P.tensorStageDiagramOver ⟶ P.rightStageDiagram :=
  haveI := hasPullbacks_bigFppfOver 𝔅 S hS
  fibreProductDiagramSnd P.leftStageProjection P.rightStageProjection

/-- Each stage of the fibre product is the fibre product of the corresponding stages of the two
spectra over the auxiliary stage of the base. -/
theorem isPullback_tensorStage (p : TensorIndex A B) :
    IsPullback (P.tensorStageFst.app p) (P.tensorStageSnd.app p)
      (P.leftStageProjection.app p) (P.rightStageProjection.app p) :=
  have := hasPullbacks_bigFppfOver 𝔅 S hS
  isPullback_fibreProductDiagram P.leftStageProjection P.rightStageProjection p

/-- The first projection is natural in the index. -/
@[reassoc (attr := simp)]
theorem tensorStageDiagramOver_map_fst {p q : TensorIndex A B} (f : p ⟶ q) :
    P.tensorStageDiagramOver.map f ≫ P.tensorStageFst.app q =
      P.tensorStageFst.app p ≫ P.leftStageDiagram.map f :=
  have := hasPullbacks_bigFppfOver 𝔅 S hS
  fibreProductDiagram_map_fst P.leftStageProjection P.rightStageProjection f

/-- The second projection is natural in the index. -/
@[reassoc (attr := simp)]
theorem tensorStageDiagramOver_map_snd {p q : TensorIndex A B} (f : p ⟶ q) :
    P.tensorStageDiagramOver.map f ≫ P.tensorStageSnd.app q =
      P.tensorStageSnd.app p ≫ P.rightStageDiagram.map f :=
  have := hasPullbacks_bigFppfOver 𝔅 S hS
  fibreProductDiagram_map_snd P.leftStageProjection P.rightStageProjection f

/-- The scheme underlying a stage of the fibre product is the fibre product of the two stage
spectra over the auxiliary stage spectrum of the base. -/
theorem isPullback_toScheme_tensorStage (p : TensorIndex A B) :
    IsPullback ((BigFppfOver.toScheme 𝔅 S hS).map (P.tensorStageFst.app p))
      ((BigFppfOver.toScheme 𝔅 S hS).map (P.tensorStageSnd.app p))
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (TensorIndex.left A B p).1
        (algebraMap C A) (P.baseIdeal_le_comap_algebraMap_left _ _))))
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (TensorIndex.right A B p).1
        (algebraMap C B) (P.baseIdeal_le_comap_algebraMap_right _ _)))) := by
  have := preservesPullbacks_bigFppfOverToScheme 𝔅 S hS
  exact isPullback_congr_cospan
    (P.toScheme_leftStageMap (TensorIndex.left A B p) (TensorIndex.right A B p))
    (P.toScheme_rightStageMap (TensorIndex.left A B p) (TensorIndex.right A B p))
    ((P.isPullback_tensorStage p).map (BigFppfOver.toScheme 𝔅 S hS))

/-- The scheme underlying a stage of the fibre product is the spectrum of the tensor product of
the two stage rings. -/
def tensorStageSpecIso (p : TensorIndex A B) :
    (BigFppfOver.toScheme 𝔅 S hS).obj (P.tensorStageDiagramOver.obj p) ≅
      Spec (.of ((A ⧸ (TensorIndex.left A B p).1) ⊗[C] (B ⧸ (TensorIndex.right A B p).1))) :=
  IsPullback.isoIsPullback _ _ (P.isPullback_toScheme_tensorStage p)
    (isPullback_specQuotientTensor (P.baseIdeal_le_comap_algebraMap_left _ _)
      (P.baseIdeal_le_comap_algebraMap_right _ _))

/-- The identification of a stage with a spectrum is compatible with the first projection. -/
@[reassoc]
theorem tensorStageSpecIso_hom_includeLeft (p : TensorIndex A B) :
    (P.tensorStageSpecIso p).hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          (A ⧸ (TensorIndex.left A B p).1) →+*
            (A ⧸ (TensorIndex.left A B p).1) ⊗[C] (B ⧸ (TensorIndex.right A B p).1))) =
      (BigFppfOver.toScheme 𝔅 S hS).map (P.tensorStageFst.app p) :=
  IsPullback.isoIsPullback_hom_fst _ _ (P.isPullback_toScheme_tensorStage p)
    (isPullback_specQuotientTensor (P.baseIdeal_le_comap_algebraMap_left _ _)
      (P.baseIdeal_le_comap_algebraMap_right _ _))

/-- The identification of a stage with a spectrum is compatible with the second projection. -/
@[reassoc]
theorem tensorStageSpecIso_hom_includeRight (p : TensorIndex A B) :
    (P.tensorStageSpecIso p).hom ≫ Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight :
          (B ⧸ (TensorIndex.right A B p).1) →ₐ[C]
            (A ⧸ (TensorIndex.left A B p).1) ⊗[C]
              (B ⧸ (TensorIndex.right A B p).1)).toRingHom)) =
      (BigFppfOver.toScheme 𝔅 S hS).map (P.tensorStageSnd.app p) :=
  IsPullback.isoIsPullback_hom_snd _ _ (P.isPullback_toScheme_tensorStage p)
    (isPullback_specQuotientTensor (P.baseIdeal_le_comap_algebraMap_left _ _)
      (P.baseIdeal_le_comap_algebraMap_right _ _))

/-- A stage of the fibre product is affine. -/
theorem isAffine_tensorStage (p : TensorIndex A B) :
    IsAffine ((BigFppfOver.toScheme 𝔅 S hS).obj (P.tensorStageDiagramOver.obj p)) :=
  IsAffine.of_isIso (P.tensorStageSpecIso p).hom

/-- The diagram of stages of the fibre product, as a diagram of affine schemes over `S`. -/
def tensorStageDiagram : TensorIndex A B ⥤ BigAffineFppf 𝔅 S hS :=
  (IsAffineOver 𝔅 S hS).lift P.tensorStageDiagramOver P.isAffine_tensorStage

/-- The objects of `tensorStageDiagram` are those of `tensorStageDiagramOver`. -/
@[simp]
theorem tensorStageDiagram_obj (p : TensorIndex A B) :
    (BigAffineFppf.inclusion 𝔅 S hS).obj (P.tensorStageDiagram.obj p) =
      P.tensorStageDiagramOver.obj p := rfl

/-- The morphisms of `tensorStageDiagram` are those of `tensorStageDiagramOver`. -/
@[simp]
theorem tensorStageDiagram_map {p q : TensorIndex A B} (f : p ⟶ q) :
    (BigAffineFppf.inclusion 𝔅 S hS).map (P.tensorStageDiagram.map f) =
      P.tensorStageDiagramOver.map f := rfl

/-! ### The transition of the stage rings -/

/-- The transition of the stage rings is the one the projections of the completed tensor
product induce. -/
theorem quotientTensorTransition_stageProjection
    {i i' : TopologicalRing.WeakIdealOfDefinitionIndex A}
    {j j' : TopologicalRing.WeakIdealOfDefinitionIndex B} (hi : i'.1 ≤ i.1) (hj : j'.1 ≤ j.1)
    (z : TopologicalRing.CompletedTensorProduct (R := C) (M := A) (N := B)) :
    quotientTensorTransition C hi hj
        (TopologicalRing.stageProjection C P.weaklyAdmissibleLeft P.weaklyAdmissibleRight
          i' j' z) =
      TopologicalRing.stageProjection C P.weaklyAdmissibleLeft P.weaklyAdmissibleRight i j z :=
  TopologicalRing.stageProjection_naturality C P.weaklyAdmissibleLeft P.weaklyAdmissibleRight
    hi hj z

include P in
/-- The kernel of a transition of stage rings consists of nilpotent elements: it is the image
of a weak ideal of definition of the completed tensor product, whose elements are
topologically nilpotent, and the next stage ideal is open. -/
theorem quotientTensorTransition_ker_le_nilradical
    {i i' : TopologicalRing.WeakIdealOfDefinitionIndex A}
    {j j' : TopologicalRing.WeakIdealOfDefinitionIndex B} (hi : i'.1 ≤ i.1) (hj : j'.1 ≤ j.1) :
    RingHom.ker (quotientTensorTransition C hi hj) ≤ nilradical ((A ⧸ i'.1) ⊗[C] (B ⧸ j'.1)) := by
  intro y hy
  obtain ⟨x, rfl⟩ := TopologicalRing.stageProjection_surjective C P.weaklyAdmissibleLeft
    P.weaklyAdmissibleRight i' j' y
  have hy' : quotientTensorTransition C hi hj
      (TopologicalRing.stageProjection C P.weaklyAdmissibleLeft P.weaklyAdmissibleRight
        i' j' x) = 0 := RingHom.mem_ker.mp hy
  rw [P.quotientTensorTransition_stageProjection hi hj x] at hy'
  have h0 : x ∈ TopologicalRing.stageIdeal C P.weaklyAdmissibleLeft P.weaklyAdmissibleRight
      i j := RingHom.mem_ker.mpr hy'
  obtain ⟨n, hn⟩ := ((TopologicalRing.isWeakIdealOfDefinition_stageIdeal C
    P.weaklyAdmissibleLeft P.weaklyAdmissibleRight i j).2 x h0).exists_pow_mem_of_mem_nhds
      ((TopologicalRing.isOpen_stageIdeal C P.weaklyAdmissibleLeft P.weaklyAdmissibleRight
        i' j').mem_nhds (Ideal.zero_mem _))
  refine mem_nilradical.mpr ⟨n, ?_⟩
  rw [← map_pow]
  exact hn


/-! ### Compatibility of the stage identifications with the transitions -/

/-- The scheme morphism underlying a transition of the stages, followed by the first projection,
is the first projection followed by `Spec` of the factor map of `A`. -/
@[reassoc]
theorem toScheme_tensorStage_map_comp_fst {p q : TensorIndex A B} (f : p ⟶ q) :
    (BigFppfOver.toScheme 𝔅 S hS).map (P.tensorStageDiagramOver.map f) ≫
        (BigFppfOver.toScheme 𝔅 S hS).map (P.tensorStageFst.app q) =
      (BigFppfOver.toScheme 𝔅 S hS).map (P.tensorStageFst.app p) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (le_left_of_tensorIndex_hom f))) :=
  by rw [← Functor.map_comp, P.tensorStageDiagramOver_map_fst, Functor.map_comp]; rfl

/-- The scheme morphism underlying a transition of the stages, followed by the second projection,
is the second projection followed by `Spec` of the factor map of `B`. -/
@[reassoc]
theorem toScheme_tensorStage_map_comp_snd {p q : TensorIndex A B} (f : p ⟶ q) :
    (BigFppfOver.toScheme 𝔅 S hS).map (P.tensorStageDiagramOver.map f) ≫
        (BigFppfOver.toScheme 𝔅 S hS).map (P.tensorStageSnd.app q) =
      (BigFppfOver.toScheme 𝔅 S hS).map (P.tensorStageSnd.app p) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (le_right_of_tensorIndex_hom f))) :=
  by rw [← Functor.map_comp, P.tensorStageDiagramOver_map_snd, Functor.map_comp]; rfl

/-- The identifications of the stages with spectra of tensor products are natural in the
index. -/
theorem toScheme_tensorStage_map_comp_specIso {p q : TensorIndex A B} (f : p ⟶ q) :
    (BigFppfOver.toScheme 𝔅 S hS).map (P.tensorStageDiagramOver.map f) ≫
        (P.tensorStageSpecIso q).hom =
      (P.tensorStageSpecIso p).hom ≫ Spec.map (CommRingCat.ofHom
        (quotientTensorTransition C (le_left_of_tensorIndex_hom f)
          (le_right_of_tensorIndex_hom f))) := by
  refine (isPullback_specQuotientTensor
    (P.baseIdeal_le_comap_algebraMap_left (TensorIndex.left A B q) (TensorIndex.right A B q))
    (P.baseIdeal_le_comap_algebraMap_right (TensorIndex.left A B q)
      (TensorIndex.right A B q))).hom_ext ?_ ?_
  · refine comp_eq_comp_of_comp_eq (P.tensorStageSpecIso_hom_includeLeft p)
      (P.tensorStageSpecIso_hom_includeLeft q) ?_ (P.toScheme_tensorStage_map_comp_fst f)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, quotientTensorTransition_comp_includeLeft,
      CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  · refine comp_eq_comp_of_comp_eq (P.tensorStageSpecIso_hom_includeRight p)
      (P.tensorStageSpecIso_hom_includeRight q) ?_ (P.toScheme_tensorStage_map_comp_snd f)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, quotientTensorTransition_comp_includeRight,
      CommRingCat.ofHom_comp, Spec.map_comp]
    rfl

include P in
/-- **The transitions of the diagram of stages are thickenings.** -/
theorem isThickening_tensorStageDiagram_map {p q : TensorIndex A B} (f : p ⟶ q) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme 𝔅 S hS).map (P.tensorStageDiagram.map f)) := by
  have hspec : Stacks.Thickenings.IsThickening (Spec.map (CommRingCat.ofHom
      (quotientTensorTransition C (le_left_of_tensorIndex_hom f)
        (le_right_of_tensorIndex_hom f)))) := by
    refine ⟨IsClosedImmersion.spec_of_surjective _
      (quotientTensorTransition_surjective C (le_left_of_tensorIndex_hom f)
        (le_right_of_tensorIndex_hom f)), ?_⟩
    change Function.Surjective (PrimeSpectrum.comap
      (quotientTensorTransition C (le_left_of_tensorIndex_hom f)
        (le_right_of_tensorIndex_hom f)))
    intro x
    have hx : x ∈ PrimeSpectrum.zeroLocus
        (RingHom.ker (quotientTensorTransition C (le_left_of_tensorIndex_hom f)
          (le_right_of_tensorIndex_hom f)) : Set _) := fun y hy =>
      nilradical_le_prime x.asIdeal
        (P.quotientTensorTransition_ker_le_nilradical (le_left_of_tensorIndex_hom f)
          (le_right_of_tensorIndex_hom f) hy)
    rw [← range_comap_of_surjective _ _
      (quotientTensorTransition_surjective C (le_left_of_tensorIndex_hom f)
        (le_right_of_tensorIndex_hom f))] at hx
    exact hx
  have hresp : MorphismProperty.RespectsIso
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have heq : (BigFppfOver.toScheme 𝔅 S hS).map (P.tensorStageDiagramOver.map f) =
      (P.tensorStageSpecIso p).hom ≫ Spec.map (CommRingCat.ofHom
          (quotientTensorTransition C (le_left_of_tensorIndex_hom f)
            (le_right_of_tensorIndex_hom f))) ≫ (P.tensorStageSpecIso q).inv := by
    rw [← Category.assoc, ← P.toScheme_tensorStage_map_comp_specIso f, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hbridge : (BigAffineFppf.toScheme 𝔅 S hS).map (P.tensorStageDiagram.map f) =
      (BigFppfOver.toScheme 𝔅 S hS).map (P.tensorStageDiagramOver.map f) :=
    congrArg (BigFppfOver.toScheme 𝔅 S hS).map (P.tensorStageDiagram_map f)
  rw [hbridge, heq]
  exact MorphismProperty.RespectsIso.precomp _ _ _
    (MorphismProperty.RespectsIso.postcomp _ _ _ hspec)

/-! ### The sheaf-level cartesian squares -/

/-- The stage inclusion of `Spf A` composed with `Spf` of the left homomorphism, read through
the auxiliary stage of the base. -/
theorem formalSpectrumInclusion_comp_formalSpectrumMap_left (p : TensorIndex A B) :
    formalSpectrumInclusion P.systemLeft (TensorIndex.fst A B p) ≫
        formalSpectrumMap P.weaklyAdmissibleBase P.toLeft =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
          (P.leftStageProjection.app p) ≫
        formalSpectrumInclusion P.systemBase (OrderDual.toDual
          (P.baseIdeal (TensorIndex.left A B p) (TensorIndex.right A B p))) :=
  formalSpectrumMap_spec P.weaklyAdmissibleBase P.toLeft
    (P.baseIdeal (TensorIndex.left A B p) (TensorIndex.right A B p))
    (TensorIndex.left A B p) (P.baseIdeal_le_comap_left _ _)

/-- The stage inclusion of `Spf B` composed with `Spf` of the right homomorphism, read through
the auxiliary stage of the base. -/
theorem formalSpectrumInclusion_comp_formalSpectrumMap_right (p : TensorIndex A B) :
    formalSpectrumInclusion P.systemRight (TensorIndex.snd A B p) ≫
        formalSpectrumMap P.weaklyAdmissibleBase P.toRight =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
          (P.rightStageProjection.app p) ≫
        formalSpectrumInclusion P.systemBase (OrderDual.toDual
          (P.baseIdeal (TensorIndex.left A B p) (TensorIndex.right A B p))) :=
  formalSpectrumMap_spec P.weaklyAdmissibleBase P.toRight
    (P.baseIdeal (TensorIndex.left A B p) (TensorIndex.right A B p))
    (TensorIndex.right A B p) (P.baseIdeal_le_comap_right _ _)

include P in
/-- **Each stage of the diagram is the fibre product of the corresponding two stages over the
formal spectrum of the base.** The square of the two stage morphisms is cartesian over the
auxiliary stage of the base, and that stage inclusion into `Spf C` is a monomorphism. -/
theorem isPullback_tensorStage_sheaf (p : TensorIndex A B) :
    IsPullback
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map (P.tensorStageFst.app p))
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map (P.tensorStageSnd.app p))
      (formalSpectrumInclusion P.systemLeft (TensorIndex.fst A B p) ≫
        formalSpectrumMap P.weaklyAdmissibleBase P.toLeft)
      (formalSpectrumInclusion P.systemRight (TensorIndex.snd A B p) ≫
        formalSpectrumMap P.weaklyAdmissibleBase P.toRight) := by
  have hsub : (BigFppfOver.topology 𝔅 S hS).Subcanonical := bigFppfOver_subcanonical 𝔅 S hS
  have hpres : PreservesLimitsOfShape WalkingCospan
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)) :=
    preservesLimitsOfShape_of_natIso
      (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology 𝔅 S hS)).symm
  let hmono : Mono (formalSpectrumInclusion P.systemBase (OrderDual.toDual
      (P.baseIdeal (TensorIndex.left A B p) (TensorIndex.right A B p)))) := by
    let _ : Nonempty (WeakIdeals C) := nonempty_weakIdeals P.weaklyAdmissibleBase.1
    let _ : IsDirectedOrder (WeakIdeals C) := isDirectedOrder_weakIdeals C
    apply Sheaf.mono_colimit_ι_of_mono_transition
    intro J K g
    apply Sheaf.mono_sheafifiedYoneda_map_of_mono_underlying
      (BigFppfOver.topology 𝔅 S hS) (BigFppfOver.toScheme 𝔅 S hS)
    change Mono (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom g))))
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (leOfHom g)))) :=
      IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective (leOfHom g))
    infer_instance
  exact isPullback_congr_cospan
    (P.formalSpectrumInclusion_comp_formalSpectrumMap_left p).symm
    (P.formalSpectrumInclusion_comp_formalSpectrumMap_right p).symm
    (@isPullback_comp_mono _ _ _ _ _ _ _ _ _ _ _
      ((P.isPullback_tensorStage p).map
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)))
      (formalSpectrumInclusion P.systemBase (OrderDual.toDual
        (P.baseIdeal (TensorIndex.left A B p) (TensorIndex.right A B p)))) hmono)

/-! ### The sections of the stages -/

/-- The sections of a stage of the fibre product: the tensor product of the two stage rings. -/
def sectionsIso (p : TensorIndex A B) :
    CommRingCat.of ((A ⧸ (TensorIndex.left A B p).1) ⊗[C]
        (B ⧸ (TensorIndex.right A B p).1)) ≅
      Γ((BigFppfOver.toScheme 𝔅 S hS).obj (P.tensorStageDiagramOver.obj p), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of ((A ⧸ (TensorIndex.left A B p).1) ⊗[C]
      (B ⧸ (TensorIndex.right A B p).1)))).symm ≪≫
    Scheme.Γ.mapIso (P.tensorStageSpecIso p).op

/-- The inverse of `sectionsIso` undoes it on elements. -/
theorem sectionsIso_inv_hom_apply (p : TensorIndex A B)
    (x : (A ⧸ (TensorIndex.left A B p).1) ⊗[C] (B ⧸ (TensorIndex.right A B p).1)) :
    ((P.sectionsIso p).inv).hom (((P.sectionsIso p).hom).hom x) = x := by
  simp

/-- `sectionsIso` undoes its inverse on elements. -/
theorem sectionsIso_hom_inv_apply (p : TensorIndex A B)
    (y : Γ((BigFppfOver.toScheme 𝔅 S hS).obj (P.tensorStageDiagramOver.obj p), ⊤)) :
    ((P.sectionsIso p).hom).hom (((P.sectionsIso p).inv).hom y) = y := by
  simp

/-- The projection of the completed tensor product onto the sections of a stage. -/
def proj (p : TensorIndex A B) :
    TopologicalRing.CompletedTensorProduct (R := C) (M := A) (N := B) →+*
      Γ((BigFppfOver.toScheme 𝔅 S hS).obj (P.tensorStageDiagramOver.obj p), ⊤) :=
  ((P.sectionsIso p).hom).hom.comp (TopologicalRing.stageProjection C P.weaklyAdmissibleLeft
    P.weaklyAdmissibleRight (TensorIndex.left A B p) (TensorIndex.right A B p))

/-- The projection onto the sections of a stage is surjective. -/
theorem proj_surjective (p : TensorIndex A B) : Function.Surjective (P.proj p) := by
  intro y
  obtain ⟨x, hx⟩ := TopologicalRing.stageProjection_surjective C P.weaklyAdmissibleLeft
    P.weaklyAdmissibleRight (TensorIndex.left A B p) (TensorIndex.right A B p)
    (((P.sectionsIso p).inv).hom y)
  refine ⟨x, ?_⟩
  change ((P.sectionsIso p).hom).hom (TopologicalRing.stageProjection C _ _ _ _ x) = y
  rw [hx, P.sectionsIso_hom_inv_apply]

/-- The kernel of the projection onto the sections of a stage is the corresponding stage ideal. -/
theorem ker_proj (p : TensorIndex A B) :
    RingHom.ker (P.proj p) = TopologicalRing.stageIdeal C P.weaklyAdmissibleLeft
      P.weaklyAdmissibleRight (TensorIndex.left A B p) (TensorIndex.right A B p) := by
  refine le_antisymm (fun x hx => RingHom.mem_ker.mpr ?_) (fun x hx => RingHom.mem_ker.mpr ?_)
  · have h : ((P.sectionsIso p).hom).hom (TopologicalRing.stageProjection C
        P.weaklyAdmissibleLeft P.weaklyAdmissibleRight (TensorIndex.left A B p)
        (TensorIndex.right A B p) x) = 0 := RingHom.mem_ker.mp hx
    have h2 := congrArg ((P.sectionsIso p).inv).hom h
    rw [P.sectionsIso_inv_hom_apply, map_zero] at h2
    exact h2
  · change ((P.sectionsIso p).hom).hom (TopologicalRing.stageProjection C
      P.weaklyAdmissibleLeft P.weaklyAdmissibleRight (TensorIndex.left A B p)
      (TensorIndex.right A B p) x) = 0
    rw [RingHom.mem_ker.mp hx, map_zero]

/-- The kernel of the projection onto the sections of a stage is a weak ideal of definition. -/
theorem isWeakIdealOfDefinition_ker_proj (p : TensorIndex A B) :
    TopologicalRing.IsWeakIdealOfDefinition (RingHom.ker (P.proj p)) := by
  rw [P.ker_proj]
  exact TopologicalRing.isWeakIdealOfDefinition_stageIdeal C P.weaklyAdmissibleLeft
    P.weaklyAdmissibleRight _ _

/-- The kernel of the projection onto the sections of a stage, as a set, is the corresponding
projection kernel. -/
theorem coe_ker_proj (p : TensorIndex A B) :
    (RingHom.ker (P.proj p) : Set (TopologicalRing.CompletedTensorProduct
        (R := C) (M := A) (N := B))) =
      (TopologicalRing.projectionKernel (B := C) (A := A) (C := B)
        (fun i : TopologicalRing.WeakIdealOfDefinitionIndex A => i.1)
        (fun j : TopologicalRing.WeakIdealOfDefinitionIndex B => j.1)
        (TopologicalRing.hasBasis_nhds_zero_weakIdealOfDefinitionIndex P.weaklyAdmissibleLeft)
        (TopologicalRing.hasBasis_nhds_zero_weakIdealOfDefinitionIndex P.weaklyAdmissibleRight)
        (TensorIndex.left A B p) (TensorIndex.right A B p) : Set _) := by
  rw [P.ker_proj, TopologicalRing.stageIdeal_eq_projectionKernel]

include P in
/-- The kernels of the projections onto the sections of the stages form a basis of neighbourhoods
of zero in the completed tensor product. -/
theorem hasBasis_nhds_zero_ker_proj :
    (nhds (0 : TopologicalRing.CompletedTensorProduct (R := C) (M := A) (N := B))).HasBasis
      (fun _ : TensorIndex A B => True) (fun p => (RingHom.ker (P.proj p) : Set _)) := by
  refine (TopologicalRing.hasBasis_projectionKernel (B := C) (A := A) (C := B)
    (fun i : TopologicalRing.WeakIdealOfDefinitionIndex A => i.1)
    (fun j : TopologicalRing.WeakIdealOfDefinitionIndex B => j.1)
    (TopologicalRing.hasBasis_nhds_zero_weakIdealOfDefinitionIndex P.weaklyAdmissibleLeft)
    (TopologicalRing.hasBasis_nhds_zero_weakIdealOfDefinitionIndex
      P.weaklyAdmissibleRight)).to_hasBasis ?_ ?_
  · exact fun pr _ => ⟨(OrderDual.toDual pr.1, OrderDual.toDual pr.2), trivial,
      (P.coe_ker_proj _).subset⟩
  · exact fun p _ => ⟨(TensorIndex.left A B p, TensorIndex.right A B p), trivial,
      (P.coe_ker_proj p).symm.subset⟩

/-! ### The sections of the stages are compatible with the transitions -/

/-- The identifications of the sections of the stages are compatible with the transitions. -/
theorem sectionsIso_hom_comp_appTop {p q : TensorIndex A B} (f : p ⟶ q) :
    (P.sectionsIso q).hom ≫ ((BigFppfOver.toScheme 𝔅 S hS).map
        (P.tensorStageDiagramOver.map f)).appTop =
      CommRingCat.ofHom (quotientTensorTransition C (le_left_of_tensorIndex_hom f)
        (le_right_of_tensorIndex_hom f)) ≫ (P.sectionsIso p).hom :=
  have h2 : ((P.tensorStageSpecIso q).hom).appTop ≫ ((BigFppfOver.toScheme 𝔅 S hS).map
        (P.tensorStageDiagramOver.map f)).appTop =
      (Spec.map (CommRingCat.ofHom (quotientTensorTransition C
        (le_left_of_tensorIndex_hom f) (le_right_of_tensorIndex_hom f)))).appTop ≫
        ((P.tensorStageSpecIso p).hom).appTop :=
    congrArg Scheme.Hom.appTop (P.toScheme_tensorStage_map_comp_specIso f)
  (Category.assoc _ _ _).trans
    ((congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of
          ((A ⧸ (TensorIndex.left A B q).1) ⊗[C]
            (B ⧸ (TensorIndex.right A B q).1)))).inv ≫ z) h2).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ ((P.tensorStageSpecIso p).hom).appTop)
          (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
            (quotientTensorTransition C (le_left_of_tensorIndex_hom f)
              (le_right_of_tensorIndex_hom f)))).symm).trans (Category.assoc _ _ _))))

/-- The projections onto the sections of the stages are compatible with the transitions. -/
theorem proj_comp_eq {p q : TensorIndex A B} (f : p ⟶ q) :
    ((((BigFppfOver.toScheme 𝔅 S hS).map (P.tensorStageDiagramOver.map f)).appTop).hom).comp
        (P.proj q) = P.proj p := by
  refine RingHom.ext fun z => ?_
  have h := ConcreteCategory.congr_hom (P.sectionsIso_hom_comp_appTop f)
    (TopologicalRing.stageProjection C P.weaklyAdmissibleLeft P.weaklyAdmissibleRight
      (TensorIndex.left A B q) (TensorIndex.right A B q) z)
  simpa [proj, P.quotientTensorTransition_stageProjection (le_left_of_tensorIndex_hom f)
    (le_right_of_tensorIndex_hom f) z] using h

/-! ### The fibre product is the colimit of the stages -/

/-- The diagram of represented stages of the fibre product is the diagram of fibre products of
the two canonical presentations. -/
def tensorStageDiagramIso :
    P.tensorStageDiagramOver ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS) ≅
      (tensorIndexEquivalence A B).functor ⋙ Functor.uncurry.obj
        (relativeProductDiagram (colimit.cocone (formalSpectrumDiagram P.systemLeft))
          (colimit.cocone (formalSpectrumDiagram P.systemRight))
          (formalSpectrumMap P.weaklyAdmissibleBase P.toLeft)
          (formalSpectrumMap P.weaklyAdmissibleBase P.toRight)) :=
  isoUncurryRelativeProductDiagram (colimit.cocone (formalSpectrumDiagram P.systemLeft))
    (colimit.cocone (formalSpectrumDiagram P.systemRight))
    (formalSpectrumMap P.weaklyAdmissibleBase P.toLeft)
    (formalSpectrumMap P.weaklyAdmissibleBase P.toRight)
    (tensorIndexEquivalence A B).functor
    (Functor.whiskerRight P.tensorStageFst (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)))
    (Functor.whiskerRight P.tensorStageSnd (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)))
    P.isPullback_tensorStage_sheaf

attribute [local instance] sheaf_hasColimits

/-- **The fibre product of the two formal spectra is the colimit of the stages.** -/
def isColimitTensorStageCocone :
    IsColimit ((relativeProductCocone (colimit.cocone (formalSpectrumDiagram P.systemLeft))
      (colimit.cocone (formalSpectrumDiagram P.systemRight))
      (formalSpectrumMap P.weaklyAdmissibleBase P.toLeft)
      (formalSpectrumMap P.weaklyAdmissibleBase P.toRight)).whisker
        (tensorIndexEquivalence A B).functor) :=
  IsColimit.whiskerEquivalence
    (isColimit_relativeProductCocone _ _ _ _
      (isUniversalColimit_formalSpectrumDiagram P.weaklyAdmissibleLeft.1 P.systemLeft)
      (isUniversalColimit_formalSpectrumDiagram P.weaklyAdmissibleRight.1 P.systemRight))
    (tensorIndexEquivalence A B)

/-- The fibre product of the two formal spectra, as the colimit of the diagram of stages. -/
def colimitIsoTensorStage :
    pullback (formalSpectrumMap P.weaklyAdmissibleBase P.toLeft)
        (formalSpectrumMap P.weaklyAdmissibleBase P.toRight) ≅
      colimit (P.tensorStageDiagram ⋙ BigAffineFppf.inclusion 𝔅 S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)) :=
  P.isColimitTensorStageCocone.coconePointUniqueUpToIso (colimit.isColimit _) ≪≫
    HasColimit.isoOfNatIso (P.tensorStageDiagramIso.symm ≪≫
      (Functor.isoWhiskerRight (ObjectProperty.liftCompιIso (IsAffineOver 𝔅 S hS)
        P.tensorStageDiagramOver P.isAffine_tensorStage)
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS))).symm) ≪≫
      HasColimit.isoOfNatIso (Functor.associator P.tensorStageDiagram
        (BigAffineFppf.inclusion 𝔅 S hS) (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)))

/-- **The presentation of the fibre product by the quotients of the completed tensor
product.** -/
def directedQuotients : DirectedQuotients 𝔅 S hS
    (pullback (formalSpectrumMap P.weaklyAdmissibleBase P.toLeft)
      (formalSpectrumMap P.weaklyAdmissibleBase P.toRight))
    (TopologicalRing.CompletedTensorProduct (R := C) (M := A) (N := B))
    (TensorIndex A B) where
  diagram := P.tensorStageDiagram
  isThickening := fun _ _ f => P.isThickening_tensorStageDiagram_map f
  colimitIso := P.colimitIsoTensorStage
  proj := P.proj
  proj_surjective := P.proj_surjective
  proj_comp := fun _ _ h => P.proj_comp_eq (homOfLE h)
  isWeakIdealOfDefinition_ker := P.isWeakIdealOfDefinition_ker_proj
  hasBasis_nhds_zero := P.hasBasis_nhds_zero_ker_proj

end CompletedTensorProductData

/-! ### Clause (3) of Stacks 0AN3 -/

attribute [local instance] sheaf_hasColimits

/-- **Stacks 0AN3, clause (3).** Let `S` be a scheme contained in a big fppf site `B`, let
`X ⟶ Z` and `Y ⟶ Z` be morphisms of fppf sheaves over `S` with `Z` separated, and suppose that
`X`, `Y` and `Z` are the formal spectra of weakly admissible topological rings `A`, `B` and `C`
over `S`, the two morphisms being the ones induced by continuous homomorphisms `C ⟶ A` and
`C ⟶ B` over `S`. Then the fibre product `X ×_Z Y` is the formal spectrum of the completed
tensor product `A ⊗̂_C B`, which is again weakly admissible. -/
theorem exists_formalSpectrum_completedTensorProduct (𝔅 : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : 𝔅.Contains S) {A B C : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsLinearTopology B B] [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsLinearTopology C C]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hB : TopologicalRing.IsWeaklyAdmissible B)
    (hC : TopologicalRing.IsWeaklyAdmissible C) (DA : QuotientSystem 𝔅 S hS A)
    (DB : QuotientSystem 𝔅 S hS B) (DC : QuotientSystem 𝔅 S hS C)
    {X Y Z : FppfSheaf 𝔅 S hS} (f : X ⟶ Z) (g : Y ⟶ Z) (eX : X ≅ formalSpectrum DA)
    (eY : Y ≅ formalSpectrum DB) (eZ : Z ≅ formalSpectrum DC)
    (_hZsep : IsSeparated 𝔅 S hS Z) (cToA : ContinuousHom DC DA) (cToB : ContinuousHom DC DB)
    (hf : formalSpectrumMap hC cToA = eX.inv ≫ f ≫ eZ.hom)
    (hg : formalSpectrumMap hC cToB = eY.inv ≫ g ≫ eZ.hom) :
    letI : Algebra C A := cToA.toRingHom.toAlgebra
    letI : Algebra C B := cToB.toRingHom.toAlgebra
    ∃ DT : QuotientSystem 𝔅 S hS
        (TopologicalRing.CompletedTensorProduct (R := C) (M := A) (N := B)),
      TopologicalRing.IsWeaklyAdmissible
          (TopologicalRing.CompletedTensorProduct (R := C) (M := A) (N := B)) ∧
        Nonempty (pullback f g ≅ formalSpectrum DT) := by
  let : Algebra C A := cToA.toRingHom.toAlgebra
  let : Algebra C B := cToB.toRingHom.toAlgebra
  let P : CompletedTensorProductData 𝔅 S hS A B C :=
    { weaklyAdmissibleLeft := hA
      weaklyAdmissibleRight := hB
      weaklyAdmissibleBase := hC
      systemLeft := DA
      systemRight := DB
      systemBase := DC
      toLeft := cToA
      toRight := cToB
      algebraMap_eq_left := rfl
      algebraMap_eq_right := rfl }
  let : Nonempty (TensorIndex A B) :=
    ⟨((nonempty_weakIdeals hA.1).some, (nonempty_weakIdeals hB.1).some)⟩
  let : IsDirectedOrder (WeakIdeals A) := isDirectedOrder_weakIdeals A
  let : IsDirectedOrder (WeakIdeals B) := isDirectedOrder_weakIdeals B
  let : IsDirected (TensorIndex A B) (· ≤ ·) := ⟨fun p q => by
    obtain ⟨x, hx₁, hx₂⟩ := directed_of (· ≤ ·) (TensorIndex.fst A B p) (TensorIndex.fst A B q)
    obtain ⟨y, hy₁, hy₂⟩ := directed_of (· ≤ ·) (TensorIndex.snd A B p) (TensorIndex.snd A B q)
    exact ⟨(x, y), ⟨hx₁, hy₁⟩, ⟨hx₂, hy₂⟩⟩⟩
  obtain ⟨DT, ⟨e⟩⟩ := P.directedQuotients.exists_quotientSystem_formalSpectrum_iso
  refine ⟨DT, TopologicalRing.completedTensorProduct_isWeaklyAdmissible hA.1 hB.1, ⟨?_⟩⟩
  have hfX : f ≫ eZ.hom = eX.hom ≫ formalSpectrumMap hC cToA := by
    rw [hf, Iso.hom_inv_id_assoc]
  have hgY : g ≫ eZ.hom = eY.hom ≫ formalSpectrumMap hC cToB := by
    rw [hg, Iso.hom_inv_id_assoc]
  exact asIso (pullback.map f g (formalSpectrumMap hC cToA) (formalSpectrumMap hC cToB)
    eX.hom eY.hom eZ.hom hfX hgY) ≪≫ e

end AlgebraicGeometry.FormalSpace


end
