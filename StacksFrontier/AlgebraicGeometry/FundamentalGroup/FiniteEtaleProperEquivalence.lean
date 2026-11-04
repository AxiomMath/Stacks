module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper

import all StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.GaloisCategoryAxioms
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite étale covers over a henselian pair: the reduction to essential surjectivity

Let `g : X₀ ⟶ X` be a morphism of schemes such that every point of `X` specializes into the image
of `g` — the situation of a proper scheme `X` over a henselian pair `(A, I)` and its closed fibre
`X₀ = X ×_{Spec A} Spec (A ⧸ I)`.  Base change along `g` is already known to be *faithful* on
finite étale covers, by
`AlgebraicGeometry.faithful_finiteEtaleBaseChange_of_forall_exists_specializes`.  This file
supplies the next two layers of the argument of Stacks Tag 0GS2 and leaves exactly one input
open.

The first layer is conservativity: a morphism of finite étale covers of `X` which becomes an
isomorphism after base change to `X₀` was already an isomorphism
(`AlgebraicGeometry.reflectsIsomorphisms_finiteEtaleBaseChange`).  Faithfulness makes such a
morphism a monomorphism, hence an open immersion on underlying schemes, and its image is an open
set containing the whole closed fibre, so by specialization it is everything; an open immersion
which is surjective is an isomorphism.  This is the global form of the step that the Stacks proof
of 0GS2 takes from Étale Morphisms, Lemma 41.14.2 (Tag 04DH).

The second layer is the deduction of *fullness* from *essential surjectivity*, which is step (2)
of the Stacks proof.  Given `ψ : U₀ ⟶ V₀` between base changes, its graph is a cover of the base
change of `U ×_X V`; descending that cover along `g` produces a finite étale `W ⟶ U ×_X V` whose
first projection becomes an isomorphism over `X₀`, hence — by the first layer — is an isomorphism,
and `ψ` lifts.  The hypothesis consumed is exactly essential surjectivity of base change *over
each finite étale cover* `P` of `X`, which is `AlgebraicGeometry.finiteEtaleBaseChangeEssSurjOver`;
`AlgebraicGeometry.finiteEtaleBaseChangeEssSurjOver_of_essSurj` derives it from essential
surjectivity of the base-change functor on covers of `P`, and every such `P` is again proper over
`Spec A`, so this is the same assertion for a different proper scheme.

Consequently Tag 0GS2 is reduced to *essential surjectivity alone*:
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj`.
Essential surjectivity is where algebraization enters: Grothendieck existence over a complete
Noetherian ring and Artin approximation over a Noetherian G-ring.  No part of that is used here.

## Main definitions

* `AlgebraicGeometry.pullbackGraph` — the graph `U₀ ⟶ (U ×_X V) ×_X X₀` of a morphism
  `U₀ ⟶ V₀` of base changes, built from the universal property of the two pullbacks.
* `AlgebraicGeometry.finiteEtaleOverProd` — `U ×_X V` as a finite étale cover of `X`.
* `AlgebraicGeometry.finiteEtaleGraph` — the graph, as a morphism of finite étale covers of `X₀`.
* `AlgebraicGeometry.finiteEtaleBaseChangeEssSurjOver` — essential surjectivity of base change
  along `g` relative to a finite étale cover `P` of `X`.

## Main results

* `AlgebraicGeometry.reflectsIsomorphisms_finiteEtaleBaseChange` — base change to the closed fibre
  reflects isomorphisms of finite étale covers.
* `AlgebraicGeometry.full_finiteEtaleBaseChange_of_essSurjOver` — fullness from relative essential
  surjectivity.
* `AlgebraicGeometry.essSurj_finiteEtaleBaseChange_of_essSurjOver` — and ordinary essential
  surjectivity from the relative form.
* `AlgebraicGeometry.finiteEtaleBaseChangeEssSurjOver_of_essSurj` and
  `AlgebraicGeometry.essSurj_finiteEtaleBaseChange_comp_of_isIso` — the two bridges that turn the
  relative hypothesis into essential surjectivity for the proper scheme `P`.
* `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_essSurjOver` and
  `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj`
  — Tag 0GS2 granted essential surjectivity.

## References

* [Stacks Project, Tag 0GS2](https://stacks.math.columbia.edu/tag/0GS2)
* [Stacks Project, Tag 04DH](https://stacks.math.columbia.edu/tag/04DH)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {X X₀ : Scheme.{u}}

/-! ### Elementary facts about morphisms of finite étale covers -/

/-- A morphism of finite étale covers of `X` is itself finite étale. -/
theorem finiteEtale_left {A B : FiniteEtaleOver X} (f : A ⟶ B) : finiteEtale f.left :=
  MorphismProperty.of_postcomp finiteEtale f.left B.hom B.prop
    (by rw [MorphismProperty.Over.w f]; exact A.prop)

/-- The structure morphism of a base-changed cover is the second pullback projection. -/
theorem finiteEtaleBaseChange_obj_hom (f : X ⟶ X₀) (A : FiniteEtaleOver X₀) :
    ((finiteEtaleBaseChange f).obj A).hom = pullback.snd A.hom f := rfl

/-- The second projection of the pullback is preserved by base change of a morphism of covers. -/
theorem finiteEtaleBaseChange_map_left_snd (f : X ⟶ X₀) {A B : FiniteEtaleOver X₀} (φ : A ⟶ B) :
    ((finiteEtaleBaseChange f).map φ).left ≫ pullback.snd B.hom f = pullback.snd A.hom f :=
  pullback.lift_snd _ _ _

/-! ### Conservativity of base change -/

/-- If every point of `X` specializes into the image of `g`, and a morphism `f` of finite étale
covers of `X` is surjective after base change along `g`, then `f` is surjective.

The image of `f` is open because `f` is étale, and it contains the whole closed fibre because the
base change of `f` is surjective; an open set containing a specialization of a point contains the
point. -/
theorem surjective_left_of_forall_exists_specializes (g : X₀ ⟶ X)
    (hsp : ∀ x : X, ∃ x' ∈ Set.range g.base, x ⤳ x')
    {A B : FiniteEtaleOver X} (f : A ⟶ B)
    (hsurj : Function.Surjective ((finiteEtaleBaseChange g).map f).left.base) :
    Function.Surjective f.left.base := by
  have hBfin : IsFinite B.hom := B.prop.1
  have hfet : Etale f.left := (finiteEtale_left f).2
  have hopen : IsOpen (Set.range f.left.base) := f.left.isOpenMap.isOpen_range
  have hsub : (B.hom.base ⁻¹' Set.range g.base) ⊆ Set.range f.left.base := by
    rw [← Scheme.Pullback.range_fst]
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hsurj y
    refine ⟨(pullback.fst A.hom g).base z, ?_⟩
    have h : (pullback.fst B.hom g).base (((finiteEtaleBaseChange g).map f).left.base z)
        = f.left.base ((pullback.fst A.hom g).base z) :=
      congrArg (fun k => k.base z) (finiteEtaleBaseChange_map_left_fst g f)
    rw [← h, hz]
  intro b
  obtain ⟨b', hb', hspec⟩ := B.hom.isClosedMap.exists_specializes_mem_preimage hsp b
  exact hspec.mem_open hopen (hsub hb')

/-- If every point of `X` specializes into the image of `g`, a morphism of finite étale covers of
`X` whose base change along `g` is an isomorphism is an isomorphism on underlying schemes. -/
theorem isIso_left_of_isIso_map (g : X₀ ⟶ X)
    (hsp : ∀ x : X, ∃ x' ∈ Set.range g.base, x ⤳ x')
    {A B : FiniteEtaleOver X} (f : A ⟶ B) [IsIso ((finiteEtaleBaseChange g).map f)] :
    IsIso f.left := by
  have := faithful_finiteEtaleBaseChange_of_forall_exists_specializes g hsp
  have hmono : Mono f := (finiteEtaleBaseChange g).mono_of_mono_map inferInstance
  have : IsOpenImmersion f.left := mono_finiteEtale_isOpenImmersion f
  have hiso : IsIso ((finiteEtaleBaseChange g).map f).left :=
    (MorphismProperty.Over.forget finiteEtale ⊤ X₀ ⋙ CategoryTheory.Over.forget X₀).map_isIso
      ((finiteEtaleBaseChange g).map f)
  have hs : Function.Surjective f.left.base :=
    surjective_left_of_forall_exists_specializes g hsp f
      ((isIso_iff_isOpenImmersion_and_surjective _).1 hiso).2.surj
  exact (isIso_iff_isOpenImmersion_and_surjective f.left).2 ⟨inferInstance, ⟨hs⟩⟩

/-- **Base change to the closed fibre reflects isomorphisms of finite étale covers.** If every
point of `X` specializes into the image of `g`, then a morphism of finite étale covers of `X`
which becomes an isomorphism over `X₀` is an isomorphism.

This is the global form of the step the Stacks proof of Tag 0GS2 takes from Étale Morphisms,
Lemma 41.14.2 (Tag 04DH). -/
theorem reflectsIsomorphisms_finiteEtaleBaseChange (g : X₀ ⟶ X)
    (hsp : ∀ x : X, ∃ x' ∈ Set.range g.base, x ⤳ x') :
    (finiteEtaleBaseChange g).ReflectsIsomorphisms where
  reflects {A B} f hf := by
    have : IsIso f.left := isIso_left_of_isIso_map g hsp f
    let e : A ≅ B := MorphismProperty.Over.isoMk (asIso f.left) (MorphismProperty.Over.w f)
    have he : e.hom = f := MorphismProperty.Over.Hom.ext rfl
    exact he ▸ e.isIso_hom

/-! ### The graph of a morphism of base changes

Everything in this section is stated at the level of schemes and in a single spelling of the
pullbacks involved, so that the rewriting needed to prove it does not have to cross the
definitional equality `((finiteEtaleBaseChange g).obj A).left = pullback A.hom g`. -/

section Graph

variable {U V : Scheme.{u}} (g : X₀ ⟶ X) (u : U ⟶ X) (v : V ⟶ X)
  (ψ : pullback u g ⟶ pullback v g) (hψ : ψ ≫ pullback.snd v g = pullback.snd u g)

/-- The morphism `(pr₁, ψ ≫ pr₁) : U ×_X X₀ ⟶ U ×_X V` attached to a morphism `ψ` of base
changes over `X₀`. -/
noncomputable def pullbackGraphToProd : pullback u g ⟶ pullback u v :=
  pullback.lift (pullback.fst u g) (ψ ≫ pullback.fst v g)
    (by rw [pullback.condition, ← hψ, Category.assoc, Category.assoc, pullback.condition])

/-- The first component of `pullbackGraphToProd` is the first projection `U ×_X X₀ ⟶ U`. -/
@[reassoc (attr := simp)]
theorem pullbackGraphToProd_fst :
    pullbackGraphToProd g u v ψ hψ ≫ pullback.fst u v = pullback.fst u g :=
  pullback.lift_fst _ _ _

/-- The second component of `pullbackGraphToProd` is `ψ` followed by the projection to `V`. -/
@[reassoc (attr := simp)]
theorem pullbackGraphToProd_snd :
    pullbackGraphToProd g u v ψ hψ ≫ pullback.snd u v = ψ ≫ pullback.fst v g :=
  pullback.lift_snd _ _ _

/-- The graph `U ×_X X₀ ⟶ (U ×_X V) ×_X X₀` of a morphism `ψ` of base changes over `X₀`. -/
noncomputable def pullbackGraph : pullback u g ⟶ pullback (pullback.fst u v ≫ u) g :=
  pullback.lift (pullbackGraphToProd g u v ψ hψ) (pullback.snd u g)
    (by rw [← Category.assoc, pullbackGraphToProd_fst]; exact pullback.condition)

/-- The first component of `pullbackGraph` is `pullbackGraphToProd`. -/
@[reassoc (attr := simp)]
theorem pullbackGraph_fst :
    pullbackGraph g u v ψ hψ ≫ pullback.fst (pullback.fst u v ≫ u) g
      = pullbackGraphToProd g u v ψ hψ :=
  pullback.lift_fst _ _ _

/-- The second component of `pullbackGraph` is the projection `U ×_X X₀ ⟶ X₀`. -/
@[reassoc (attr := simp)]
theorem pullbackGraph_snd :
    pullbackGraph g u v ψ hψ ≫ pullback.snd (pullback.fst u v ≫ u) g = pullback.snd u g :=
  pullback.lift_snd _ _ _

/-- Composing the graph with the base change of the first projection gives the identity. The
morphism `m` is the base change of `pr₁ : U ×_X V ⟶ U`, described by its two components. -/
theorem pullbackGraph_comp_fst (m : pullback (pullback.fst u v ≫ u) g ⟶ pullback u g)
    (hm₁ : m ≫ pullback.fst u g = pullback.fst (pullback.fst u v ≫ u) g ≫ pullback.fst u v)
    (hm₂ : m ≫ pullback.snd u g = pullback.snd (pullback.fst u v ≫ u) g) :
    pullbackGraph g u v ψ hψ ≫ m = 𝟙 (pullback u g) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, hm₁, pullbackGraph_fst_assoc, pullbackGraphToProd_fst,
      Category.id_comp]
  · rw [Category.assoc, hm₂, pullbackGraph_snd, Category.id_comp]

/-- Composing the graph with the base change of the second projection gives `ψ` back. The
morphism `m` is the base change of `pr₂ : U ×_X V ⟶ V`, described by its two components. -/
theorem pullbackGraph_comp_snd (m : pullback (pullback.fst u v ≫ u) g ⟶ pullback v g)
    (hm₁ : m ≫ pullback.fst v g = pullback.fst (pullback.fst u v ≫ u) g ≫ pullback.snd u v)
    (hm₂ : m ≫ pullback.snd v g = pullback.snd (pullback.fst u v ≫ u) g) :
    pullbackGraph g u v ψ hψ ≫ m = ψ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, hm₁, pullbackGraph_fst_assoc, pullbackGraphToProd_snd]
  · rw [Category.assoc, hm₂, pullbackGraph_snd, hψ]

end Graph

/-! ### Fullness from relative essential surjectivity -/

section Prod

variable (U V : FiniteEtaleOver X)

/-- The fibre product `U ×_X V`, as a finite étale cover of `X`. -/
noncomputable def finiteEtaleOverProd : FiniteEtaleOver X :=
  MorphismProperty.Over.mk ⊤ (pullback.fst U.hom V.hom ≫ U.hom)
    (finiteEtale.comp_mem _ _ (finiteEtale.pullback_fst U.hom V.hom V.prop) U.prop)

/-- The first projection `U ×_X V ⟶ U`. -/
noncomputable def finiteEtaleOverProdFst : finiteEtaleOverProd U V ⟶ U :=
  MorphismProperty.Over.homMk (pullback.fst U.hom V.hom) rfl trivial

/-- The second projection `U ×_X V ⟶ V`. -/
noncomputable def finiteEtaleOverProdSnd : finiteEtaleOverProd U V ⟶ V :=
  MorphismProperty.Over.homMk (pullback.snd U.hom V.hom) pullback.condition.symm trivial

end Prod

variable (g : X₀ ⟶ X)

/-- The graph of a morphism `ψ : U₀ ⟶ V₀` of base changes, as a morphism of finite étale covers
of `X₀` from `U₀` to the base change of `U ×_X V`. -/
noncomputable def finiteEtaleGraph {U V : FiniteEtaleOver X}
    (ψ : (finiteEtaleBaseChange g).obj U ⟶ (finiteEtaleBaseChange g).obj V) :
    (finiteEtaleBaseChange g).obj U
      ⟶ (finiteEtaleBaseChange g).obj (finiteEtaleOverProd U V) :=
  MorphismProperty.Over.homMk
    (pullbackGraph g U.hom V.hom ψ.left (MorphismProperty.Over.w ψ))
    (pullbackGraph_snd g U.hom V.hom ψ.left (MorphismProperty.Over.w ψ)) trivial

/-- Composing `finiteEtaleGraph g ψ` with the base change of the first projection
`U ×_X V ⟶ U` gives the identity. -/
theorem finiteEtaleGraph_comp_fst {U V : FiniteEtaleOver X}
    (ψ : (finiteEtaleBaseChange g).obj U ⟶ (finiteEtaleBaseChange g).obj V) :
    finiteEtaleGraph g ψ ≫ (finiteEtaleBaseChange g).map (finiteEtaleOverProdFst U V) = 𝟙 _ :=
  MorphismProperty.Over.Hom.ext <|
    pullbackGraph_comp_fst g U.hom V.hom ψ.left (MorphismProperty.Over.w ψ) _
      (finiteEtaleBaseChange_map_left_fst g (finiteEtaleOverProdFst U V))
      (finiteEtaleBaseChange_map_left_snd g (finiteEtaleOverProdFst U V))

/-- Composing `finiteEtaleGraph g ψ` with the base change of the second projection
`U ×_X V ⟶ V` gives `ψ`. -/
theorem finiteEtaleGraph_comp_snd {U V : FiniteEtaleOver X}
    (ψ : (finiteEtaleBaseChange g).obj U ⟶ (finiteEtaleBaseChange g).obj V) :
    finiteEtaleGraph g ψ ≫ (finiteEtaleBaseChange g).map (finiteEtaleOverProdSnd U V) = ψ :=
  MorphismProperty.Over.Hom.ext <|
    pullbackGraph_comp_snd g U.hom V.hom ψ.left (MorphismProperty.Over.w ψ) _
      (finiteEtaleBaseChange_map_left_fst g (finiteEtaleOverProdSnd U V))
      (finiteEtaleBaseChange_map_left_snd g (finiteEtaleOverProdSnd U V))

/-- Base change along `g : X₀ ⟶ X` is *essentially surjective over* the finite étale cover `P` of
`X`: every finite étale cover of the base change `P ×_X X₀` is, together with its structure
morphism, the base change of a finite étale cover of `P`.

Stated in the slice over `P` this is ordinary essential surjectivity of base change along
`P ×_X X₀ ⟶ P`; see `finiteEtaleBaseChangeEssSurjOver_of_essSurj`. -/
def finiteEtaleBaseChangeEssSurjOver (P : FiniteEtaleOver X) : Prop :=
  ∀ (Q : FiniteEtaleOver X₀) (q : Q ⟶ (finiteEtaleBaseChange g).obj P),
    ∃ (W : FiniteEtaleOver X) (w : W ⟶ P) (ε : (finiteEtaleBaseChange g).obj W ≅ Q),
      (finiteEtaleBaseChange g).map w = ε.hom ≫ q

/-- **Fullness of base change on finite étale covers, from relative essential surjectivity.**
This is step (2) of the Stacks proof of Tag 0GS2: the graph of `ψ : U₀ ⟶ V₀` is a finite étale
cover of the base change of `U ×_X V`; a descent `W ⟶ U ×_X V` of it has `W ⟶ U` an isomorphism
over `X₀`, hence an isomorphism, and `ψ` is the base change of the resulting `U ⟶ V`. -/
theorem full_finiteEtaleBaseChange_of_essSurjOver
    (hsp : ∀ x : X, ∃ x' ∈ Set.range g.base, x ⤳ x')
    (hes : ∀ P : FiniteEtaleOver X, finiteEtaleBaseChangeEssSurjOver g P) :
    (finiteEtaleBaseChange g).Full := by
  have hrefl := reflectsIsomorphisms_finiteEtaleBaseChange g hsp
  constructor
  intro U V ψ
  obtain ⟨W, w, ε, hwε⟩ :=
    hes (finiteEtaleOverProd U V) ((finiteEtaleBaseChange g).obj U) (finiteEtaleGraph g ψ)
  have hα : (finiteEtaleBaseChange g).map (w ≫ finiteEtaleOverProdFst U V) = ε.hom := by
    rw [Functor.map_comp, hwε, Category.assoc, finiteEtaleGraph_comp_fst, Category.comp_id]
  have : IsIso ((finiteEtaleBaseChange g).map (w ≫ finiteEtaleOverProdFst U V)) :=
    hα ▸ ε.isIso_hom
  have : IsIso (w ≫ finiteEtaleOverProdFst U V) := hrefl.reflects _
  have hinv : (finiteEtaleBaseChange g).map (inv (w ≫ finiteEtaleOverProdFst U V)) = ε.inv := by
    rw [← Iso.comp_hom_eq_id, ← hα, ← Functor.map_comp, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id]
  refine ⟨inv (w ≫ finiteEtaleOverProdFst U V) ≫ w ≫ finiteEtaleOverProdSnd U V, ?_⟩
  rw [Functor.map_comp, Functor.map_comp, hinv, hwε, Category.assoc,
    Iso.inv_hom_id_assoc, finiteEtaleGraph_comp_snd]

/-- Relative essential surjectivity over every finite étale cover implies ordinary essential
surjectivity: take the cover `𝟙 X`, whose base change is the final object of `FÉt_{X₀}`. -/
theorem essSurj_finiteEtaleBaseChange_of_essSurjOver
    (hes : ∀ P : FiniteEtaleOver X, finiteEtaleBaseChangeEssSurjOver g P) :
    (finiteEtaleBaseChange g).EssSurj := by
  constructor
  intro Q
  obtain ⟨W, _, ε, _⟩ := hes (MorphismProperty.Over.mk ⊤ (𝟙 X) (finiteEtale.id_mem X)) Q
    (MorphismProperty.Over.homMk
      (pullback.lift (Q.hom ≫ g) Q.hom (Category.comp_id _)) (pullback.lift_snd _ _ _) trivial)
  exact ⟨W, ⟨ε⟩⟩

/-- **Tag 0GS2 granted essential surjectivity.** If every point of `X` specializes into the image
of `g` and base change along `g` is essentially surjective over every finite étale cover of `X`,
then base change along `g` is an equivalence on finite étale covers. -/
theorem isEquivalence_finiteEtaleBaseChange_of_essSurjOver
    (hsp : ∀ x : X, ∃ x' ∈ Set.range g.base, x ⤳ x')
    (hes : ∀ P : FiniteEtaleOver X, finiteEtaleBaseChangeEssSurjOver g P) :
    (finiteEtaleBaseChange g).IsEquivalence := by
  have hfaithful := faithful_finiteEtaleBaseChange_of_forall_exists_specializes g hsp
  have hfull := full_finiteEtaleBaseChange_of_essSurjOver g hsp hes
  have hess := essSurj_finiteEtaleBaseChange_of_essSurjOver g hes
  exact { faithful := hfaithful, full := hfull, essSurj := hess }

/-! ### Descent of a cover along a finite étale cover

As in the graph section, these two lemmas are stated at the level of schemes and in a single
spelling of the pullbacks, so that no rewriting has to cross
`((finiteEtaleBaseChange g).obj P).left = pullback P.hom g`. -/

section Descent

/-- `W ×_P (P ×_X X₀) ≅ W ×_X X₀` carries an identification of `W ×_P (P ×_X X₀)` with a cover
`Q` of `P ×_X X₀` into one of `Q` with `W ×_X X₀` over `X₀`. -/
theorem pullbackRightPullbackFstIso_inv_comp_comp {P Q W : Scheme.{u}} (g : X₀ ⟶ X) (p : P ⟶ X)
    (ww : W ⟶ P) (ql : Q ⟶ pullback p g) (qh : Q ⟶ X₀)
    (hq : ql ≫ pullback.snd p g = qh) (ηl : pullback ww (pullback.fst p g) ⟶ Q)
    (hη : ηl ≫ ql = pullback.snd ww (pullback.fst p g)) :
    ((pullbackRightPullbackFstIso p g ww).inv ≫ ηl) ≫ qh = pullback.snd (ww ≫ p) g := by
  rw [← hq, Category.assoc, ← Category.assoc ηl, hη,
    ← pullbackRightPullbackFstIso_hom_snd p g ww, Iso.inv_hom_id_assoc]

/-- Under that identification, the base change along `g` of `W ⟶ P` becomes the structure
morphism `Q ⟶ P ×_X X₀` of the cover.  The morphism `m` is the base change of `W ⟶ P`,
described by its two components. -/
theorem eq_pullbackRightPullbackFstIso_inv_comp_comp {P Q W : Scheme.{u}} (g : X₀ ⟶ X)
    (p : P ⟶ X) (ww : W ⟶ P) (ql : Q ⟶ pullback p g)
    (ηl : pullback ww (pullback.fst p g) ⟶ Q)
    (hη : ηl ≫ ql = pullback.snd ww (pullback.fst p g))
    (m : pullback (ww ≫ p) g ⟶ pullback p g)
    (hm₁ : m ≫ pullback.fst p g = pullback.fst (ww ≫ p) g ≫ ww)
    (hm₂ : m ≫ pullback.snd p g = pullback.snd (ww ≫ p) g) :
    m = ((pullbackRightPullbackFstIso p g ww).inv ≫ ηl) ≫ ql := by
  rw [Category.assoc, hη, Iso.eq_inv_comp]
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, hm₁, pullbackRightPullbackFstIso_hom_fst_assoc, pullback.condition]
  · rw [Category.assoc, hm₂, pullbackRightPullbackFstIso_hom_snd]

end Descent

/-- Relative essential surjectivity over `P` is ordinary essential surjectivity of base change
along `P ×_X X₀ ⟶ P`.

A cover `q : Q ⟶ P ×_X X₀` is a finite étale cover of `P ×_X X₀`; a cover `W` of `P` descending
it gives the cover `W ⟶ P ⟶ X` of `X`, and `W ×_P (P ×_X X₀) = W ×_X X₀` by the pullback pasting
isomorphism `pullbackRightPullbackFstIso`. -/
theorem finiteEtaleBaseChangeEssSurjOver_of_essSurj (P : FiniteEtaleOver X)
    (h : (finiteEtaleBaseChange (pullback.fst P.hom g)).EssSurj) :
    finiteEtaleBaseChangeEssSurjOver g P := by
  intro Q q
  obtain ⟨W, ⟨η⟩⟩ :=
    h.mem_essImage (MorphismProperty.Over.mk ⊤ q.left (finiteEtale_left q))
  have hη : η.hom.left ≫ q.left = pullback.snd W.hom (pullback.fst P.hom g) :=
    MorphismProperty.Over.w η.hom
  have hq : q.left ≫ pullback.snd P.hom g = Q.hom := MorphismProperty.Over.w q
  have hW : finiteEtale (W.hom ≫ P.hom) := finiteEtale.comp_mem _ _ W.prop P.prop
  refine ⟨MorphismProperty.Over.mk ⊤ (W.hom ≫ P.hom) hW,
    MorphismProperty.Over.homMk W.hom rfl trivial,
    MorphismProperty.Over.isoMk ((pullbackRightPullbackFstIso P.hom g W.hom).symm ≪≫
      (MorphismProperty.Over.forget finiteEtale ⊤ (pullback P.hom g)
        ⋙ CategoryTheory.Over.forget _).mapIso η)
      (pullbackRightPullbackFstIso_inv_comp_comp g P.hom W.hom q.left Q.hom hq η.hom.left hη),
    MorphismProperty.Over.Hom.ext ?_⟩
  refine eq_pullbackRightPullbackFstIso_inv_comp_comp g P.hom W.hom q.left η.hom.left hη
    (m := ((finiteEtaleBaseChange g).map
      (MorphismProperty.Over.homMk (A := MorphismProperty.Over.mk ⊤ (W.hom ≫ P.hom) hW)
        (B := P) W.hom rfl trivial)).left) ?_ ?_
  · exact finiteEtaleBaseChange_map_left_fst g _
  · exact finiteEtaleBaseChange_map_left_snd g _

/-- Base change along an isomorphism is essentially surjective on finite étale covers. -/
theorem essSurj_finiteEtaleBaseChange_of_isIso {Y₁ Y₂ : Scheme.{u}} (θ : Y₁ ⟶ Y₂) [IsIso θ] :
    (finiteEtaleBaseChange θ).EssSurj := by
  constructor
  intro Q
  have hθ : finiteEtale θ := ⟨inferInstance, inferInstance⟩
  have hiso : IsIso (pullback.fst (Q.hom ≫ θ) θ) :=
    (MorphismProperty.isomorphisms Scheme).pullback_fst _ _ (inferInstanceAs (IsIso θ))
  exact ⟨MorphismProperty.Over.mk ⊤ (Q.hom ≫ θ) (finiteEtale.comp_mem _ _ Q.prop hθ),
    ⟨MorphismProperty.Over.isoMk (@asIso _ _ _ _ (pullback.fst (Q.hom ≫ θ) θ) hiso)
      ((cancel_mono θ).1 ((Category.assoc _ _ _).trans pullback.condition))⟩⟩

/-- Essential surjectivity of base change is unchanged by precomposing the base-change morphism
with an isomorphism. -/
theorem essSurj_finiteEtaleBaseChange_comp_of_isIso {Y₁ Y₂ P : Scheme.{u}} (θ : Y₁ ⟶ Y₂)
    [IsIso θ] (g₂ : Y₂ ⟶ P) (h : (finiteEtaleBaseChange g₂).EssSurj) :
    (finiteEtaleBaseChange (θ ≫ g₂)).EssSurj := by
  have h₂ : (MorphismProperty.Over.pullback finiteEtale ⊤ g₂).EssSurj := h
  have h₁ : (MorphismProperty.Over.pullback finiteEtale ⊤ θ).EssSurj :=
    essSurj_finiteEtaleBaseChange_of_isIso θ
  exact Functor.essSurj_of_iso (MorphismProperty.Over.pullbackComp θ g₂).symm

/-- A finite étale cover of a scheme proper over `S` is itself proper over `S`, so the hypothesis
of `isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj` is the
essential-surjectivity half of Tag 0GS2 for another proper scheme over the same henselian pair. -/
@[ega "III 2.6.2.5" "Properness of Z' over Y"]
theorem isProper_comp_of_finiteEtaleOver {S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (P : FiniteEtaleOver X) : IsProper (P.hom ≫ f) := by
  have : IsFinite P.hom := P.prop.1
  infer_instance

/-- **Stacks Project, Tag 0GS2, granted essential surjectivity.** If `(A, I)` is a henselian
pair, `X` is proper over `Spec A`, and base change to the closed fibre is essentially surjective
on finite étale covers of every scheme `P` finite étale over `X`, then base change to the closed
fibre is an equivalence on finite étale covers of `X`.

Each such `P` is itself proper over `Spec A` by `isProper_comp_of_finiteEtaleOver`, and the
hypothesis is literally the conclusion's own base-change functor with `f` replaced by
`P.hom ≫ f`: that is, the essential-surjectivity half of Tag 0GS2 for the proper schemes finite
étale over `X`.  The faithfulness and fullness halves, and the conservativity used to deduce
fullness from essential surjectivity, are proved unconditionally. -/
theorem isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianPair_of_essSurj
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (hes : ∀ P : FiniteEtaleOver X,
      (finiteEtaleBaseChange (pullback.fst (P.hom ≫ f)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).EssSurj) :
    (finiteEtaleBaseChange
      (pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).IsEquivalence := by
  refine isEquivalence_finiteEtaleBaseChange_of_essSurjOver _
    (exists_specializes_mem_range_pullback_fst_of_isProper A hI.le_jacobson f) fun P => ?_
  refine finiteEtaleBaseChangeEssSurjOver_of_essSurj _ P ?_
  rw [← pullbackRightPullbackFstIso_hom_fst f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) P.hom]
  exact essSurj_finiteEtaleBaseChange_comp_of_isIso _ _ (hes P)

end AlgebraicGeometry

end
