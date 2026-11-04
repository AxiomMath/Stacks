module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackObjExists
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge

/-!
# The sufficiency direction of Stacks 0EX9

A category fibred in groupoids over the big h category over `S` which satisfies the three
conditions of Stacks 0EX9 — it is a stack in groupoids for the Zariski topology, it has effective
descent along a flat proper finitely-presented surjection onto an affine object, and the comparison
functor onto the two-fibre product is an equivalence for the almost blowup squares of Examples 0EVG
and 0EVH — is a stack in groupoids for the h topology.  The second condition is the source's
condition (2) in its descent form,
`AlgebraicGeometry.BigHOver.IsAffineFlatProperFinitePresentationDescent`; the source's literal
condition (2) is false for h stacks in general, see there.

Both conditions of Stacks 026F are now available: condition (2),
`AlgebraicGeometry.BigHOver.isMorSheaf_of_generatorSquares`, and condition (3), which this file
assembles out of `AlgebraicGeometry.BigHOver.nonempty_descentSolution_id`.  The route is Stacks
02ZF, `CategoryTheory.Functor.isStack_iff_isEquivalence_toDescentData`: the functor from the fibre
over `U` to the descent data of a covering family of `U` is fully faithful by condition (2) in the
form `AlgebraicGeometry.BigHOver.nonempty_fullyFaithful_toDescentData_of_generatorSquares`, and it
is essentially surjective because a solution of the descent problem over `𝟙 U` is exactly an object
of the fibre over `U` isomorphic, as a descent datum, to the given one.  The last step from
Stacks 026F to Stacks 02ZI is `CategoryTheory.Functor.IsStack.isStackInGroupoids`.

## Main results

* `AlgebraicGeometry.BigHOver.essSurj_toDescentData_of_generatorSquares`: the functor to the
  descent data of a covering family is essentially surjective.
* `AlgebraicGeometry.BigHOver.isStack_of_generatorSquares`: Stacks 026F for the h topology.
* `AlgebraicGeometry.BigHOver.isStackInGroupoids_of_generatorSquares`: **Stacks 0EX9, the
  sufficiency direction.**

## References

* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 02ZF](https://stacks.math.columbia.edu/tag/02ZF)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t v u

namespace AlgebraicGeometry

namespace BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 : Type t} [Category.{v} 𝒳] {p : 𝒳 ⥤ BigHOver B S hS} [p.IsFibered]

/-- **The functor from a fibre to the descent data of a covering family is essentially
surjective**, from conditions (1), (2) and (3) of Stacks 0EX9.

A solution of the descent problem over `𝟙 U`,
`AlgebraicGeometry.BigHOver.nonempty_descentSolution_id`, carries an object of the fibre over `U`
whose chosen pullback along each member of the family is identified with the object of the datum
there; those identifications are compatible with the gluing isomorphisms because a solution is, so
they constitute an isomorphism of descent data. -/
public theorem essSurj_toDescentData_of_generatorSquares
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    {U : BigHOver B S hS} {I : Type (u + 1)} {V : I → BigHOver B S hS} (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U) :
    ((Functor.IsFibered.pullbackPseudofunctor p).toDescentData f).EssSurj := by
  refine ⟨fun Dd ↦ ?_⟩
  obtain ⟨s⟩ := nonempty_descentSolution_id (D := Dd) h1 h2 h3 h4 hf
  -- the identification of the chosen pullback of the descended object with the object of the
  -- datum, over each member of the family
  obtain ⟨eI, heI⟩ : ∃ eI : ∀ i, Functor.pullbackFiber p s.obj (f i) ≅ descentObj Dd i,
      ∀ i, (eI i).hom = (s.iso i (f i) (𝟙 (V i)) (f i) (Category.comp_id (f i))
        (Category.id_comp (f i))).hom ≫
          (Functor.pullbackFiberIdIso (descentObj Dd i)).hom :=
    ⟨fun i ↦ s.iso i (f i) (𝟙 (V i)) (f i) (Category.comp_id (f i))
      (Category.id_comp (f i)) ≪≫ Functor.pullbackFiberIdIso (descentObj Dd i), fun _ ↦ rfl⟩
  -- its base change along a morphism into a member of the family
  have hE : ∀ (i : I) ⦃Z : BigHOver B S hS⦄ (g : Z ⟶ V i) (q : Z ⟶ U) (hq : g ≫ f i = q),
      Functor.pullbackFiberHom (eI i).hom g =
        (Functor.pullbackFiberCompIso' s.obj (f i) g q hq).hom ≫
          (s.iso i q g q (Category.comp_id q) hq).hom := by
    intro i Z g q hq
    have hbc := s.iso_baseChange i (f i) (𝟙 (V i)) (f i) (Category.comp_id (f i))
      (Category.id_comp (f i)) g q hq g (Category.comp_id g) q (Category.comp_id q) hq
    rw [Functor.baseChangeFiberMor] at hbc
    rw [heI i, Functor.pullbackFiberHom_comp, pullbackFiberHom_pullbackFiberIdIso_hom_eq,
      ← hbc, Iso.hom_inv_id_assoc]
  refine ⟨s.obj, ⟨Pseudofunctor.DescentData.isoMk eI ?_⟩⟩
  intro Z q i₁ i₂ f₁ f₂ hf₁ hf₂
  have heqq : f₁ ≫ f i₁ = f₂ ≫ f i₂ := by rw [hf₁, hf₂]
  have hmap : ∀ (i : I) ⦃Z : BigHOver B S hS⦄ (g : Z ⟶ V i),
      Functor.pullbackFiberHom (eI i).hom g =
        ((Functor.IsFibered.pullbackPseudofunctor p).map g.op.toLoc).toFunctor.map (eI i).hom :=
    fun i _ g ↦ (Functor.pullbackPseudofunctor_map_map p g (eI i).hom).symm
  have htd : (((Functor.IsFibered.pullbackPseudofunctor p).toDescentData f).obj s.obj).hom q
        f₁ f₂ hf₁ hf₂ = (Functor.pullbackFiberComparison s.obj f₁ f₂ heqq).hom :=
    Functor.toDescentData_obj_hom p f s.obj q f₁ f₂ hf₁ hf₂ heqq
  -- the commutation condition, in the chosen-pullback spelling
  have hgoal : Functor.pullbackFiberHom (eI i₁).hom f₁ ≫
        (descentIso Dd i₁ i₂ f₁ f₂ q hf₁ hf₂).hom =
      (Functor.pullbackFiberComparison s.obj f₁ f₂ heqq).hom ≫
        Functor.pullbackFiberHom (eI i₂).hom f₂ := by
    rw [hE i₁ f₁ q hf₁, hE i₂ f₂ q hf₂,
      ← Functor.pullbackFiberCompIso'_hom_comp_inv p s.obj (f i₁) (f i₂) f₁ f₂ q hf₁ hf₂ heqq]
    simp only [Category.assoc]
    rw [s.compat i₁ i₂ q f₁ f₂ q (Category.comp_id q) hf₁ hf₂, Iso.inv_hom_id_assoc]
  -- and crossed into the spelling of the pullback pseudofunctor
  rw [hmap i₁ f₁, hmap i₂ f₂] at hgoal
  rw [htd]
  exact hgoal

/-- **Stacks 026F for the h topology, from conditions (1), (2) and (3) of Stacks 0EX9.**

By Stacks 02ZF it suffices that the functor from the fibre over an object to the descent data of a
covering family of it be an equivalence; it is fully faithful by
`AlgebraicGeometry.BigHOver.nonempty_fullyFaithful_toDescentData_of_generatorSquares` and
essentially surjective by
`AlgebraicGeometry.BigHOver.essSurj_toDescentData_of_generatorSquares`. -/
public theorem isStack_of_generatorSquares
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p) :
    p.IsStack (BigHOver.topology B S hS) := by
  rw [Functor.isStack_iff_isEquivalence_toDescentData]
  intro T 𝒰 h𝒰
  obtain ⟨hff⟩ := nonempty_fullyFaithful_toDescentData_of_generatorSquares h1 h2 h3 h4 𝒰.f h𝒰
  exact
    { faithful := hff.faithful
      full := hff.full
      essSurj := essSurj_toDescentData_of_generatorSquares h1 h2 h3 h4 𝒰.f h𝒰 }

/-- **Stacks 0EX9, the sufficiency direction.**  A category fibred in groupoids over the big h
category over `S` which

1. is a stack in groupoids for the Zariski topology,
2. has effective descent, with descent of morphisms, along every surjective flat proper morphism
   of finite presentation `X ⟶ Y` of the site with `Y` affine: the functor from `𝒮_Y` to the
   descent data relative to `{X ⟶ Y}` is an equivalence, and
3. has `𝒮_X ⟶ 𝒮_Z ×_{𝒮_E} 𝒮_{X'}` an equivalence for every almost blow up square of the site of
   the shape of Example 0EVG or of Example 0EVH

is a stack in groupoids for the h topology.

Conditions (1) and (3) are those of the source.  Condition (2) is the source's condition (2) with
the two-fibre product `𝒮_X ×_{𝒮_{X ×_Y X}} 𝒮_X` replaced by the category of descent data, which
adds the cocycle condition over `X ×_Y X ×_Y X`: the literal condition fails for every h stack with
a nontrivial automorphism over an affine object, by the fold-map computation in the module
documentation of
`StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackCriterion`, and the
descent form is what the source's proof uses.  The three hypotheses are those of the sheaf-level
criterion of Stacks 0EVI that the proof of the source applies, read for a category fibred in
groupoids: the Zariski one is the topology condition (1) of 0EVI quantifies over, and the descent
along `{X ⟶ Y}` and the two equivalences range over the morphisms and squares conditions (2), (3)
and (4) of 0EVI range over.

The proof runs Stacks 0EVI on the two auxiliary presheaves of sets on the slice `(Sch/S)_h / U`
that the source builds out of `𝒮`: the presheaf of morphisms between two objects of the fibre over
`U`, whose sheaf property is
`AlgebraicGeometry.BigHOver.isMorSheaf_of_generatorSquares`, and the presheaf of solutions of a
descent problem, whose sheaf property is
`AlgebraicGeometry.BigHOver.nonempty_descentSolution_id`.  Both are run through
`AlgebraicGeometry.BigHOver.of_localOnGenerators`. -/
@[stacks 0EX9 "if, with condition (2) in its descent form"]
public theorem isStackInGroupoids_of_generatorSquares
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p) :
    p.IsStackInGroupoids.{u + 1} (BigHOver.topology B S hS) :=
  (isStack_of_generatorSquares h1 h2 h3 h4).isStackInGroupoids h1.isFiberedInGroupoids

end BigHOver

end AlgebraicGeometry

end
