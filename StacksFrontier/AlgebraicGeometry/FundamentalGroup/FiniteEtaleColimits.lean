module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.RingTheory.Etale.Pi
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteEtaleLocal
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleLimits
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct

/-!
# Colimits of split finite étale covers

Let `X` be a scheme. This file develops the right-exactness half of Stacks Tag 0BN9 as far as it
goes without the relative spectrum of a quasi-coherent algebra: the category `FÉt_X` of schemes
finite étale over `X` has finite coproducts, given by disjoint unions, and it has coequalizers of
pairs of morphisms between *split* covers; both are computed in the category of schemes.

A split cover is a finite disjoint union `∐_{i : ι} X` of copies of the base, with its fold map;
by Stacks Tag 04HN (`Stacks.Etale.exists_etaleCover_pullback_iso_sigma`) every finite étale cover
becomes split after an étale base change, so this is exactly the étale-local picture that the
proof of Tag 0BN9 reduces to, and the diagram

```
∐_{j ∈ κ} X ⇉ ∐_{i ∈ ι} X ⟶ ∐_{t ∈ Coeq(σ, τ)} X
```

displayed in the proof of Tag 0BNA.

Two ingredients are isolated because they are independent of the geometry. The first is purely
set-theoretic and categorical: for `σ τ : κ → ι` the coequalizer of the two induced morphisms
`∐_{κ} A ⇉ ∐_{ι} A` in *any* category with the relevant coproducts is `∐_{t} A` indexed by the
coequalizer `IndexCoeq σ τ` of `σ` and `τ` in types, because a morphism out of a coproduct is a
family of morphisms and such a family descends to the quotient exactly when it is constant on the
generating relation. The second is a reflection principle: a cofork in `P.Over ⊤ X` whose
underlying cofork in the ambient category is a coequalizer is itself a coequalizer, since the
structure morphism of the apex is determined by the (epimorphic) cofork projection.

The missing step towards Tag 0BN9 itself is the coequalizer of an arbitrary pair, which is the
relative spectrum of the equalizer of the two induced maps of quasi-coherent algebras. Its
affine, algebraic input — that the equalizer of two maps of finite étale algebras is again
finite étale — is proved in
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/FiniteEtaleColimits/EqualizerAlgebra.lean`. Only
the split case is proved here. See the implementation notes.

## Main definitions

* `Stacks.FundamentalGroup.IndexCoeq` — the coequalizer of two maps of index types.
* `Stacks.FundamentalGroup.sigmaIndexMap` — the morphism of coproducts induced by a map of index
  types.
* `Stacks.FundamentalGroup.splitCover` — the split finite étale cover `∐_{i : ι} X` of `X`.
* `Stacks.FundamentalGroup.piPrecompAlgHom` — the algebra homomorphism `(ι → R) ⟶ (κ → R)` given
  by precomposition with a map of index types.

## Main results

* `Stacks.FundamentalGroup.isColimitSigmaIndexCofork` — in any category, the coequalizer of two
  morphisms of coproducts induced by maps of index types is the coproduct indexed by the
  coequalizer of the index maps.
* `Stacks.FundamentalGroup.isColimitOfIsColimitCoconeLeft` and
  `Stacks.FundamentalGroup.isColimitOfIsColimitCoforkLeft` — a cocone, respectively a cofork, of a
  subcategory of an over category defined by a morphism property is a colimit as soon as its
  underlying cocone, respectively cofork, is.
* `Stacks.FundamentalGroup.finiteEtale_sigmaDesc` — a morphism out of a finite disjoint union of
  finite étale covers is finite étale; `Stacks.FundamentalGroup.finiteEtale_of_isSplitCover`
  specialises this to split coverings.
* `Stacks.FundamentalGroup.hasFiniteCoproducts_finiteEtaleOver` — `FÉt_X` has finite coproducts,
  given by disjoint unions, with the empty scheme as the empty coproduct; the identification with
  the disjoint union is `Stacks.FundamentalGroup.isColimitSigmaCocone`.
* `Stacks.FundamentalGroup.isColimit_splitCoverCofork` — the étale-local coequalizer of Tag 0BN9:
  the coequalizer of two index-induced morphisms of split finite étale covers of `X` is the split
  cover indexed by the coequalizer of the index maps, both in `FÉt_X` and in schemes.
* `Stacks.FundamentalGroup.indexCoeqPiAlgEquiv` — the algebraic form of the same computation: the
  equalizer of the two precomposition maps `(ι → R) ⇉ (κ → R)` is `∏_{t ∈ IndexCoeq σ τ} R`, and
  by `Stacks.FundamentalGroup.etale_equalizer_piPrecompAlgHom` it is finite étale over `R`.

## Implementation notes

Neither `HasFiniteColimits (FÉt_X)` nor the finite-colimit instance
`HasFiniteColimitsWithLocalCoequalizers X` of Tag 0BN9 is constructed. Finite coproducts and the
coequalizers of pairs of split covers are proved here, but a general pair `a, b : Z ⟶ Y` of
finite étale covers is handled in the source by writing `Y = Spec(𝓑)` and `Z = Spec(𝓒)`
relatively over `X`, forming the equalizer algebra `𝓐 = Eq(a^♯, b^♯)`, and checking that
`Spec(𝓐) ⟶ X` is finite étale after an étale covering on which both covers split — where it is
the algebra indexed by `IndexCoeq`, which is the content of `isColimitSigmaIndexCofork`.

Two of the three inputs of that reduction are now available, and the third is what is missing.
The relative spectrum of a quasi-coherent algebra on a scheme, and the anti-equivalence of
Stacks Tag 01SA between the schemes affine over `X` and the quasi-coherent `𝒪_X`-algebras, are
`Stacks.AffineAlgebraEquivalence.relativeSpec` and
`Stacks.AffineAlgebraEquivalence.affineQuasicoherentEquivalence`, in
`StacksFrontier/AlgebraicGeometry/RelativeSpecEssSurj/Basic.lean`; and that the equalizer algebra
is finite étale over an affine base is
`Stacks.FundamentalGroup.etale_and_moduleFinite_equalizer` of
`FiniteEtaleColimits/EqualizerAlgebra.lean`, where the category of finite étale algebras over a
ring is also shown to have finite limits. What is missing is the sheaf-level step: the equalizer
of two morphisms of quasi-coherent `𝒪_X`-algebras, as a quasi-coherent `𝒪_X`-algebra, whose
sections over an affine open are the equalizer of the sections (quasi-coherence of the subsheaf
of agreement, which holds because localization is exact). With that, the coequalizer in `FÉt_X`
is its relative spectrum, finite étale because that property is Zariski-local on `X`, and the
universal property is the anti-equivalence applied to the sectionwise equalizer.

No instance is declared in the meantime: `HasFiniteColimitsWithLocalCoequalizers` is a
`Prop`-valued class, and an incomplete instance would silently weaken every consumer.

## References

* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
* [Stacks Project, Tag 0BNA](https://stacks.math.columbia.edu/tag/0BNA)
* [Stacks Project, Tag 04HN](https://stacks.math.columbia.edu/tag/04HN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe v u

namespace Stacks.FundamentalGroup

/-! ### Coequalizers of index types -/

/-- The relation on an index type `ι` generated by `σ j ∼ τ j`, for `σ τ : κ → ι`. -/
def IndexRel {ι κ : Type*} (σ τ : κ → ι) (i i' : ι) : Prop := ∃ j, σ j = i ∧ τ j = i'

/-- The coequalizer of two maps of index types `σ τ : κ → ι`, as the quotient of `ι` by the
relation generated by `σ j ∼ τ j`. -/
def IndexCoeq {ι κ : Type*} (σ τ : κ → ι) : Type _ := Quot (IndexRel σ τ)

/-- The coequalizer of two maps out of a finite index type is finite. -/
instance {ι κ : Type*} (σ τ : κ → ι) [Finite ι] : Finite (IndexCoeq σ τ) := Quot.finite _

/-- The canonical map from an index type to the coequalizer of two maps out of it. -/
def toIndexCoeq {ι κ : Type*} (σ τ : κ → ι) (i : ι) : IndexCoeq σ τ := Quot.mk _ i

/-- The two maps become equal in the coequalizer of the index types. -/
lemma toIndexCoeq_comp_eq {ι κ : Type*} (σ τ : κ → ι) (j : κ) :
    toIndexCoeq σ τ (σ j) = toIndexCoeq σ τ (τ j) := Quot.sound ⟨j, rfl, rfl⟩

/-- A family indexed by `ι` which is unchanged by `σ` and `τ` descends to the coequalizer of the
index types. -/
def indexCoeqLift {ι κ : Type*} {σ τ : κ → ι} {β : Sort*} (g : ι → β)
    (hg : ∀ j, g (σ j) = g (τ j)) : IndexCoeq σ τ → β :=
  Quot.lift g (by rintro i i' ⟨j, rfl, rfl⟩; exact hg j)

/-- The descended family takes the value `g i` on the class of `i`. -/
@[simp]
lemma indexCoeqLift_toIndexCoeq {ι κ : Type*} {σ τ : κ → ι} {β : Sort*} (g : ι → β)
    (hg : ∀ j, g (σ j) = g (τ j)) (i : ι) :
    indexCoeqLift g hg (toIndexCoeq σ τ i) = g i := rfl

/-- Every element of the coequalizer of two maps of index types comes from the index type. -/
lemma indexCoeq_ind {ι κ : Type*} {σ τ : κ → ι} {motive : IndexCoeq σ τ → Prop}
    (h : ∀ i, motive (toIndexCoeq σ τ i)) (t : IndexCoeq σ τ) : motive t := Quot.ind h t

/-! ### Coequalizers of coproducts of a constant family -/

section Sigma

variable {C : Type*} [Category* C] (A : C) {ι κ : Type*} (σ τ : κ → ι)

/-- A morphism out of a coproduct of copies of `A` built from a map `ρ` of index types commutes
with the fold maps. -/
private lemma desc_ι_comp_desc_id [HasCoproduct (fun _ : κ ↦ A)] [HasCoproduct (fun _ : ι ↦ A)]
    (ρ : κ → ι) :
    (Sigma.desc fun j ↦ Sigma.ι (fun _ : ι ↦ A) (ρ j)) ≫ (Sigma.desc fun _ : ι ↦ 𝟙 A) =
      Sigma.desc fun _ : κ ↦ 𝟙 A := by
  refine Sigma.hom_ext _ _ fun j ↦ ?_
  rw [Sigma.ι_desc_assoc, Sigma.ι_desc, Sigma.ι_desc]

/-- The projection onto the coproduct indexed by the coequalizer of the index maps commutes with
the fold maps. -/
lemma sigmaIndexCoforkπ_comp_sigmaDesc_id [HasCoproduct (fun _ : ι ↦ A)]
    [HasCoproduct (fun _ : IndexCoeq σ τ ↦ A)] :
    (Sigma.desc fun i ↦ Sigma.ι (fun _ : IndexCoeq σ τ ↦ A) (toIndexCoeq σ τ i)) ≫
        (Sigma.desc fun _ : IndexCoeq σ τ ↦ 𝟙 A) = Sigma.desc fun _ : ι ↦ 𝟙 A :=
  desc_ι_comp_desc_id A (toIndexCoeq σ τ)

variable [HasCoproduct (fun _ : κ ↦ A)] [HasCoproduct (fun _ : ι ↦ A)]

/-- The morphism `∐_{j : κ} A ⟶ ∐_{i : ι} A` of coproducts of a constant family induced by a map
`ρ : κ → ι` of index types. -/
noncomputable def sigmaIndexMap (ρ : κ → ι) : (∐ fun _ : κ ↦ A) ⟶ (∐ fun _ : ι ↦ A) :=
  Sigma.desc fun j ↦ Sigma.ι (fun _ : ι ↦ A) (ρ j)

/-- The index-induced morphism sends the `j`-th summand to the `ρ j`-th summand. -/
@[simp, reassoc]
lemma ι_sigmaIndexMap (ρ : κ → ι) (j : κ) :
    Sigma.ι (fun _ : κ ↦ A) j ≫ sigmaIndexMap A ρ = Sigma.ι (fun _ : ι ↦ A) (ρ j) :=
  Sigma.ι_desc _ _

/-- An index-induced morphism of coproducts of copies of `A` commutes with the fold maps. -/
lemma sigmaIndexMap_comp_sigmaDesc_id (ρ : κ → ι) :
    sigmaIndexMap A ρ ≫ (Sigma.desc fun _ : ι ↦ 𝟙 A) = Sigma.desc fun _ : κ ↦ 𝟙 A :=
  desc_ι_comp_desc_id A ρ

variable [HasCoproduct (fun _ : IndexCoeq σ τ ↦ A)]

/-- The cofork on the two index-induced morphisms `∐_{κ} A ⇉ ∐_{ι} A` whose apex is the coproduct
indexed by the coequalizer `IndexCoeq σ τ` of the index maps. -/
@[reducible] noncomputable def sigmaIndexCofork : Cofork (sigmaIndexMap A σ) (sigmaIndexMap A τ) :=
  Cofork.ofπ (Sigma.desc fun i ↦ Sigma.ι (fun _ : IndexCoeq σ τ ↦ A) (toIndexCoeq σ τ i)) (by
    refine Sigma.hom_ext _ _ fun j ↦ ?_
    rw [ι_sigmaIndexMap_assoc, ι_sigmaIndexMap_assoc, Sigma.ι_desc, Sigma.ι_desc,
      toIndexCoeq_comp_eq])

/-- **The combinatorial core of Stacks 0BN9.** The coequalizer of the two morphisms
`∐_{j : κ} A ⇉ ∐_{i : ι} A` induced by maps `σ τ : κ → ι` of index types is the coproduct
`∐_{t : IndexCoeq σ τ} A` indexed by the coequalizer of `σ` and `τ`.

A morphism out of `∐_{ι} A` is a family of morphisms out of `A` indexed by `ι`, and it equalizes
the two induced morphisms exactly when the family takes equal values at `σ j` and `τ j` for all
`j`, that is, exactly when it descends to `IndexCoeq σ τ`. -/
noncomputable def isColimitSigmaIndexCofork : IsColimit (sigmaIndexCofork A σ τ) := by
  refine Cofork.IsColimit.mk _ (fun s ↦ Sigma.desc (indexCoeqLift
    (fun i ↦ Sigma.ι (fun _ : ι ↦ A) i ≫ Cofork.π s) (fun j ↦ ?_))) (fun s ↦ ?_) (fun s m hm ↦ ?_)
  · have h := Sigma.ι (fun _ : κ ↦ A) j ≫= s.condition
    rwa [ι_sigmaIndexMap_assoc, ι_sigmaIndexMap_assoc] at h
  · refine Sigma.hom_ext _ _ fun i ↦ ?_
    simp [sigmaIndexCofork]
  · refine Sigma.hom_ext _ _ (indexCoeq_ind fun i ↦ ?_)
    have h := Sigma.ι (fun _ : ι ↦ A) i ≫= hm
    rw [Cofork.π_ofπ, Sigma.ι_desc_assoc] at h
    rwa [Sigma.ι_desc]

end Sigma

/-! ### Reflecting colimits along the forgetful functor -/

section Reflect

variable {T : Type*} [Category* T] {P : MorphismProperty T} {X : T}

/-- The cocone underlying a cocone in the subcategory of `Over X` defined by a morphism
property. -/
@[reducible] def coconeLeft {J : Type*} [Category* J] {D : J ⥤ P.Over ⊤ X} (c : Cocone D) :
    Cocone (D ⋙ MorphismProperty.Over.forget P ⊤ X ⋙ Over.forget X) where
  pt := c.pt.left
  ι :=
    { app j := (c.ι.app j).left
      naturality := fun _ _ g ↦
        (congrArg (fun k ↦ k.left) (c.w g)).trans (Category.comp_id _).symm }

/-- A cocone in the subcategory of `Over X` defined by a morphism property is a colimit as soon as
its underlying cocone is one.

The factorisation through the apex is the one obtained in the ambient category; it is a morphism
over `X` because the components of a colimit cocone are jointly epimorphic. -/
def isColimitOfIsColimitCoconeLeft {J : Type*} [Category* J] {D : J ⥤ P.Over ⊤ X} (c : Cocone D)
    (hc : IsColimit (coconeLeft c)) : IsColimit c where
  desc s := MorphismProperty.Over.homMk (hc.desc (coconeLeft s)) (by
    refine hc.hom_ext fun j ↦ ?_
    have h1 : (coconeLeft c).ι.app j ≫ hc.desc (coconeLeft s) = (coconeLeft s).ι.app j :=
      hc.fac (coconeLeft s) j
    rw [← Category.assoc, h1]
    change (s.ι.app j).left ≫ s.pt.hom = (c.ι.app j).left ≫ c.pt.hom
    have w1 : (s.ι.app j).left ≫ s.pt.hom = (D.obj j).hom := MorphismProperty.Over.w (s.ι.app j)
    have w2 : (c.ι.app j).left ≫ c.pt.hom = (D.obj j).hom := MorphismProperty.Over.w (c.ι.app j)
    rw [w1, w2])
  fac s j := MorphismProperty.Over.Hom.ext (hc.fac (coconeLeft s) j)
  uniq s m hm := MorphismProperty.Over.Hom.ext (hc.uniq (coconeLeft s) m.left
    fun j ↦ congrArg (fun k ↦ k.left) (hm j))

/-- The cofork underlying a cofork in the subcategory of `Over X` defined by a morphism
property. -/
@[reducible] def coforkLeft {Y Z : P.Over ⊤ X} {a b : Y ⟶ Z} (c : Cofork a b) :
    Cofork a.left b.left :=
  Cofork.ofπ c.π.left (congrArg (fun k ↦ k.left) c.condition)

/-- A cofork in the subcategory of `Over X` defined by a morphism property is a coequalizer as
soon as its underlying cofork is one.

The factorisation through the apex is the one obtained in the ambient category; it is a morphism
over `X` because the cofork projection is an epimorphism, being a coequalizer projection. -/
def isColimitOfIsColimitCoforkLeft {Y Z : P.Over ⊤ X} {a b : Y ⟶ Z} (c : Cofork a b)
    (hc : IsColimit (coforkLeft c)) : IsColimit c := by
  refine Cofork.IsColimit.mk c (fun s ↦ MorphismProperty.Over.homMk (hc.desc (coforkLeft s))
    ?_) (fun s ↦ ?_) (fun s m hm ↦ ?_)
  · have he : Epi (Cofork.π (coforkLeft c)) := Cofork.IsColimit.epi hc
    refine (cancel_epi (Cofork.π (coforkLeft c))).1 ?_
    have h1 : Cofork.π (coforkLeft c) ≫ hc.desc (coforkLeft s) = Cofork.π (coforkLeft s) :=
      hc.fac (coforkLeft s) WalkingParallelPair.one
    rw [← Category.assoc, h1]
    change s.π.left ≫ s.pt.hom = c.π.left ≫ c.pt.hom
    rw [MorphismProperty.Over.w, MorphismProperty.Over.w]
  · apply MorphismProperty.Over.Hom.ext
    exact hc.fac (coforkLeft s) WalkingParallelPair.one
  · apply MorphismProperty.Over.Hom.ext
    have he : Epi (Cofork.π (coforkLeft c)) := Cofork.IsColimit.epi hc
    refine (cancel_epi (Cofork.π (coforkLeft c))).1 ?_
    have h2 : Cofork.π (coforkLeft c) ≫ hc.desc (coforkLeft s) = Cofork.π (coforkLeft s) :=
      hc.fac (coforkLeft s) WalkingParallelPair.one
    change Cofork.π (coforkLeft c) ≫ m.left = Cofork.π (coforkLeft c) ≫ hc.desc (coforkLeft s)
    rw [h2]
    exact congrArg (fun k ↦ k.left) hm

end Reflect

/-! ### Finite disjoint unions of finite étale covers -/

/-- A morphism out of a finite disjoint union of schemes is finite étale as soon as each of its
restrictions to a component is. Finiteness is `AlgebraicGeometry.isFinite_sigmaDesc` and étaleness
holds because étale morphisms are Zariski-local at the source. -/
theorem finiteEtale_sigmaDesc {ι : Type v} [Finite ι] {X : Scheme.{u}} {Y : ι → Scheme.{u}}
    {f : ∀ i, Y i ⟶ X} (hf : ∀ i, finiteEtale (f i)) :
    finiteEtale (Sigma.desc f) :=
  have : ∀ i, IsFinite (f i) := fun i ↦ (hf i).1
  have : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Etale)
  ⟨isFinite_sigmaDesc, IsZariskiLocalAtSource.sigmaDesc fun i ↦ (hf i).2⟩

/-- A split covering, that is, a finite disjoint union of copies of the base, is finite étale. -/
theorem finiteEtale_of_isSplitCover {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : Stacks.Etale.IsSplitCover f) : finiteEtale f := by
  obtain ⟨ι, _, e, he⟩ := hf
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso
      (finiteEtale : MorphismProperty Scheme.{u}) e.hom _).mpr
    (finiteEtale_sigmaDesc fun _ ↦ MorphismProperty.id_mem _ _)

/-! ### Finite coproducts of finite étale covers -/

section Coproducts

variable (X : Scheme.{u}) {α : Type v} [Finite α] (D : Discrete α ⥤ FiniteEtaleOver X)

/-- The disjoint union of a finite family of finite étale covers of `X`, as a cocone on the
corresponding discrete diagram in `FÉt_X`. -/
noncomputable def sigmaCocone : Cocone D where
  pt := MorphismProperty.Over.mk ⊤ (Sigma.desc fun i ↦ (D.obj ⟨i⟩).hom)
    (finiteEtale_sigmaDesc fun i ↦ (D.obj ⟨i⟩).prop)
  ι := Discrete.natTrans fun i ↦ MorphismProperty.Over.homMk
    (Sigma.ι (fun i ↦ (D.obj ⟨i⟩).left) i.as) (Sigma.ι_desc _ _)

/-- **Finite coproducts in `FÉt_X`, Stacks 0BN9.** The disjoint union of a finite family of finite
étale covers of `X` is their coproduct in `FÉt_X`, and it is computed in the category of
schemes. -/
noncomputable def isColimitSigmaCocone : IsColimit (sigmaCocone X D) :=
  isColimitOfIsColimitCoconeLeft _ (coproductIsCoproduct' _)

/-- A finite discrete diagram of finite étale covers of `X` has a colimit, namely its disjoint
union. -/
theorem hasColimitsOfShape_discrete_finiteEtaleOver :
    HasColimitsOfShape (Discrete α) (FiniteEtaleOver X) where
  has_colimit D := ⟨_, isColimitSigmaCocone X D⟩

/-- **Stacks 0BN9**, the coproduct half of right exactness: the category of schemes finite étale
over a scheme has finite coproducts, given by disjoint unions, the empty coproduct being the empty
scheme. -/
instance hasFiniteCoproducts_finiteEtaleOver : HasFiniteCoproducts (FiniteEtaleOver X) where
  out n := hasColimitsOfShape_discrete_finiteEtaleOver X (α := Fin n)

end Coproducts

/-! ### Coequalizers of split finite étale covers -/

section SplitCover

variable (X : Scheme.{u}) {ι κ : Type u} [Finite ι] [Finite κ]

/-- The split finite étale cover `∐_{i : ι} X` of `X`, with its fold map, as an object of
`FÉt_X`. -/
@[reducible] noncomputable def splitCover (X : Scheme.{u}) (ι : Type u) [Finite ι] :
    FiniteEtaleOver X :=
  MorphismProperty.Over.mk ⊤ (Sigma.desc fun _ : ι ↦ 𝟙 X)
    (finiteEtale_sigmaDesc fun _ ↦ MorphismProperty.id_mem _ _)

/-- The underlying scheme of the split cover indexed by `ι` is `∐_{i : ι} X`. -/
@[simp]
lemma splitCover_left (ι : Type u) [Finite ι] : (splitCover X ι).left = ∐ fun _ : ι ↦ X := rfl

/-- The structure morphism of the split cover indexed by `ι` is its fold map. -/
@[simp]
lemma splitCover_hom (ι : Type u) [Finite ι] :
    (splitCover X ι).hom = Sigma.desc fun _ : ι ↦ 𝟙 X := rfl

/-- The morphism of split finite étale covers of `X` induced by a map of index types. -/
noncomputable def splitCoverMap (ρ : κ → ι) : splitCover X κ ⟶ splitCover X ι :=
  MorphismProperty.Over.homMk (sigmaIndexMap X ρ) (sigmaIndexMap_comp_sigmaDesc_id X ρ)

/-- The underlying morphism of schemes of `splitCoverMap X ρ` is `sigmaIndexMap X ρ`. -/
@[simp]
lemma splitCoverMap_left (ρ : κ → ι) : (splitCoverMap X ρ).left = sigmaIndexMap X ρ := rfl

/-- The cofork of split finite étale covers of `X` on two index-induced morphisms, with apex the
split cover indexed by the coequalizer of the index maps. -/
@[reducible] noncomputable def splitCoverCofork (σ τ : κ → ι) :
    Cofork (splitCoverMap X σ) (splitCoverMap X τ) :=
  Cofork.ofπ (MorphismProperty.Over.homMk
      (A := splitCover X ι) (B := splitCover X (IndexCoeq σ τ))
      (Sigma.desc fun i ↦ Sigma.ι (fun _ : IndexCoeq σ τ ↦ X) (toIndexCoeq σ τ i))
      (sigmaIndexCoforkπ_comp_sigmaDesc_id X σ τ))
    (MorphismProperty.Over.Hom.ext (sigmaIndexCofork X σ τ).condition)

/-- **The étale-local coequalizer of Stacks 0BN9.** For maps `σ τ : κ → ι` of finite index types,
the coequalizer of the two induced morphisms of split finite étale covers
`∐_{j : κ} X ⇉ ∐_{i : ι} X` is the split cover `∐_{t : IndexCoeq σ τ} X` indexed by the
coequalizer of `σ` and `τ`.

This is the diagram displayed in the proof of Tag 0BNA. By `isColimitSigmaIndexCofork` the
underlying cofork of schemes is already a coequalizer, so by `isColimitOfIsColimitCoforkLeft` the
cofork of finite étale covers is one as well; in particular this coequalizer is computed in the
category of schemes. -/
noncomputable def isColimit_splitCoverCofork (σ τ : κ → ι) :
    IsColimit (splitCoverCofork X σ τ) :=
  isColimitOfIsColimitCoforkLeft _ (isColimitSigmaIndexCofork X σ τ)

/-- Two index-induced morphisms of split finite étale covers have a coequalizer in `FÉt_X`. -/
instance hasCoequalizer_splitCoverMap (σ τ : κ → ι) :
    HasCoequalizer (splitCoverMap X σ) (splitCoverMap X τ) :=
  ⟨⟨⟨_, isColimit_splitCoverCofork X σ τ⟩⟩⟩

/-- The underlying cofork of schemes of the coequalizer of two index-induced morphisms of split
finite étale covers is a coequalizer: the forgetful functor to schemes preserves these
coequalizers, which is the input Tag 0BNA needs. -/
noncomputable def isColimit_coforkLeft_splitCoverCofork (σ τ : κ → ι) :
    IsColimit (coforkLeft (splitCoverCofork X σ τ)) :=
  isColimitSigmaIndexCofork X σ τ

end SplitCover

/-! ### The equalizer algebra in the split case -/

section EqualizerAlgebra

variable (R : Type*) [CommRing R] {ι κ : Type*} (σ τ : κ → ι)

/-- Precomposition with a map `ρ : κ → ι` of index types, as a homomorphism of `R`-algebras
`(ι → R) ⟶ (κ → R)`. On spectra this is the morphism `∐_{κ} Spec R ⟶ ∐_{ι} Spec R` induced
by `ρ`. -/
def piPrecompAlgHom (ρ : κ → ι) : (ι → R) →ₐ[R] (κ → R) :=
  AlgHom.pi fun j ↦ Pi.evalAlgHom R (fun _ : ι ↦ R) (ρ j)

/-- Precomposition with `ρ` evaluates a function at `ρ j` in the `j`-th coordinate. -/
@[simp]
lemma piPrecompAlgHom_apply (ρ : κ → ι) (x : ι → R) (j : κ) :
    piPrecompAlgHom R ρ x j = x (ρ j) := rfl

/-- A function on the index type lies in the equalizer of the two precomposition maps exactly
when it takes equal values at `σ j` and `τ j` for every `j`. -/
lemma mem_equalizer_piPrecompAlgHom (x : ι → R) :
    x ∈ AlgHom.equalizer (piPrecompAlgHom R σ) (piPrecompAlgHom R τ) ↔
      ∀ j, x (σ j) = x (τ j) := by
  simp only [AlgHom.mem_equalizer, funext_iff, piPrecompAlgHom_apply]

/-- **The equalizer algebra of Stacks 0BN9 in the split case.** The equalizer of the two
precomposition maps `(ι → R) ⇉ (κ → R)` attached to `σ τ : κ → ι` is the algebra of functions on
the coequalizer `IndexCoeq σ τ` of the index maps.

This is the algebraic form of `isColimitSigmaIndexCofork`: writing the two split covers as
`Spec (ι → R)` and `Spec (κ → R)`, the algebra `𝓐 = Eq(a^♯, b^♯)` of the source proof is
`∏_{t ∈ IndexCoeq σ τ} R`. -/
noncomputable def indexCoeqPiAlgEquiv :
    (IndexCoeq σ τ → R) ≃ₐ[R]
      AlgHom.equalizer (piPrecompAlgHom R σ) (piPrecompAlgHom R τ) := by
  refine AlgEquiv.ofBijective
    ((piPrecompAlgHom R (toIndexCoeq σ τ)).codRestrict _ (fun y ↦ ?_)) ⟨?_, ?_⟩
  · rw [mem_equalizer_piPrecompAlgHom]
    intro j
    rw [piPrecompAlgHom_apply, piPrecompAlgHom_apply, toIndexCoeq_comp_eq]
  · intro y y' h
    have h' : piPrecompAlgHom R (toIndexCoeq σ τ) y = piPrecompAlgHom R (toIndexCoeq σ τ) y' :=
      congrArg Subtype.val h
    exact funext (indexCoeq_ind fun i ↦ congrFun h' i)
  · rintro ⟨x, hx⟩
    rw [mem_equalizer_piPrecompAlgHom] at hx
    exact ⟨indexCoeqLift x hx, Subtype.ext (funext fun _ ↦ rfl)⟩

variable [Finite ι]

/-- The equalizer algebra of two precomposition maps out of a finite product of copies of `R` is
a finite `R`-module. -/
theorem moduleFinite_equalizer_piPrecompAlgHom :
    Module.Finite R (AlgHom.equalizer (piPrecompAlgHom R σ) (piPrecompAlgHom R τ)) :=
  Module.Finite.equiv (indexCoeqPiAlgEquiv R σ τ).toLinearEquiv

/-- The equalizer algebra of two precomposition maps out of a finite product of copies of `R` is
étale over `R`. Together with `moduleFinite_equalizer_piPrecompAlgHom` this is the step
"`𝓐 = ∏_{t ∈ T} 𝒪_X`, whose spectrum is certainly finite étale over `X`" of the source proof. -/
theorem etale_equalizer_piPrecompAlgHom :
    Algebra.Etale R (AlgHom.equalizer (piPrecompAlgHom R σ) (piPrecompAlgHom R τ)) :=
  Algebra.Etale.of_equiv (indexCoeqPiAlgEquiv R σ τ)

end EqualizerAlgebra

end Stacks.FundamentalGroup

end
