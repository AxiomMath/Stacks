module

public import Mathlib.AlgebraicGeometry.Gluing
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.Representation

/-!
# The morphism into relative Proj attached to an invertible sheaf and a graded map

[Stacks, Tag 0D2Z] and its scheme-level form [Stacks, Tag 01O9] fix a graded quasi-coherent
algebra `𝒜` on a base, a morphism `f : X ⟶ Y` into that base, an invertible module `ℒ` on `X`
and a homomorphism of graded algebras `ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}`, and produce from them a
canonical morphism

  `r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)`

over the base, where `U(ψ) ⊆ X` is the open locus on which `ψ` is surjective in some positive
degree.  The morphism is *characterized* by its restrictions: on any test scheme `W ⟶ U(ψ)` on
which `ψ` is surjective in a positive degree, the composite `W ⟶ Proj_Y(𝒜)` is the morphism
that the construction of relative Proj attaches to the restricted pair `(ℒ|_W, ψ|_W)`.

This file builds that morphism at the scheme level from the representation of relative Proj by
the functor `F₁` of [Stacks, Tag 01O4]. A pair `(ℒ, ψ)` with `ψ` surjective in degree one on a
test scheme is a `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair`, and the morphism it
classifies is `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Representation.classifyingMorphism`.
The classifying morphism is compatible with base change of the test scheme, which is the
characterizing property (2) of Tag 01O9 and of Tag 0D2Z, and local morphisms on the members of
an open cover that agree on the overlaps glue to the unique morphism restricting to them.

Here `U(ψ)` is *presented by such a cover*: the input is a scheme `U` over the base together with
an open cover of it and a pair on each member, surjective in degree one.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.ofOpenCover` is `r_{ℒ,ψ}`: the
  morphism `U ⟶ Proj_S(𝒜)` over the base obtained by glueing the morphisms classified by the
  members of a compatible family of pairs on an open cover of `U`.
* `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.ofOpenCover_of_isPullbackPair`: the
  same morphism, under the hypothesis that on each overlap the two restricted pairs are
  pullbacks of one common pair.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.strictlyEquivalent_of_isPullbackPair`:
  two pairs that are both the canonical pullback of one pair along one morphism of test schemes
  are strictly isomorphic, so the class of the pullback of a pair is well defined.
* `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.comp_classifyingMorphism`: the
  classifying morphism of a pair, composed with a morphism of test schemes, is the classifying
  morphism of the pulled-back pair.  This is characterizing property (2).
* `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.comp_classifyingMorphism_eq_comp`:
  two pairs on two test schemes whose pullbacks to a common test scheme agree have classifying
  morphisms that agree there.
* `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.eq_classifyingMorphism_iff`: a
  morphism over the base is the classifying morphism of a pair exactly when it induces the class
  of that pair — the uniqueness half of "characterized by".
* `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.ofOpenCover_restrict` is
  characterizing property (2) for the glued morphism: it restricts on each member of the cover
  to the morphism classified by the pair there.
* `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.eq_ofOpenCover`: the glued morphism is
  the only morphism over the base with those restrictions.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.ProjRepresentsF1

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

universe u

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})

/-- Reassociation with a cancellation performed inside: if `b ≫ c = d` then
`(a ≫ b) ≫ c = a ≫ d`. -/
public theorem assoc_of {C : Type*} [Category C] {W X Y Z : C} (a : W ⟶ X) {b : X ⟶ Y}
    {c : Y ⟶ Z} {d : X ⟶ Z} (h : b ≫ c = d) : (a ≫ b) ≫ c = a ≫ d :=
  Eq.trans (Category.assoc a b c) (congrArg (a ≫ ·) h)

/-! ### The graded-map clause, read on adjoint transposes -/

/-- The clause of strict isomorphism comparing the graded maps of two pairs is equivalent to the
same clause on their adjoint transposes: `F1Pair.ψ` is the adjoint form of the graded map and
`F1Pair.pullbackMap` its transpose. -/
public theorem pullbackMap_comp_iff {T : Scheme.{u}} {f : T ⟶ S} (P Q : F1Pair A TA f) (n : ℤ)
    (h : (TA T P.L).tensor.piece n ⟶ (TA T Q.L).tensor.piece n) :
    P.pullbackMap A TA n ≫ h = Q.pullbackMap A TA n ↔
      P.ψ n ≫ (Scheme.Modules.pushforward f).map h = Q.ψ n := by
  have key := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right_symm
    (P.ψ n) h
  exact Iff.trans (by rw [key]; rfl)
    (Equiv.apply_eq_iff_eq ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm)

/-! ### The class of the pullback of a pair is well defined -/

/-- **Two pullbacks of one pair are strictly isomorphic.**  If `Q` and `Q'` are both canonical
pullbacks of the pair `P` along `g`, then the comparison isomorphisms of the two pullback data
compose to a strict isomorphism `Q ≅ Q'`.  Consequently the class in `F1` of a pullback of `P`
depends only on `P` and `g`. -/
public theorem strictlyEquivalent_of_isPullbackPair {ι : TensorAlgebraPullbackIsos.{u} TA}
    {T T' : Scheme.{u}} {f : T ⟶ S} {g : T' ⟶ T} {P : F1Pair A TA f}
    {Q Q' : F1Pair A TA (g ≫ f)} (h : IsPullbackPair A TA ι g P Q)
    (h' : IsPullbackPair A TA ι g P Q') : StrictlyEquivalent A TA Q Q' := by
  obtain ⟨β, γ, hgen, hone, hψ⟩ := h
  obtain ⟨β', γ', hgen', hone', hψ'⟩ := h'
  refine ⟨β.symm ≪≫ β', γ.symm ≪≫ γ', ?_, ?_, fun n => ?_⟩
  · have hback : (TA T' Q.L).tensorGenerator ≫ γ.inv.app 1 =
        β.inv ≫ (TA T' ((Scheme.Modules.pullback g).obj P.L)).tensorGenerator :=
      (Iso.comp_inv_eq (gradedAlgebraIsoApp γ 1)).mpr (Eq.symm
        (Eq.trans (Category.assoc _ _ _)
          (Eq.trans (congrArg (β.inv ≫ ·) hgen) (β.inv_hom_id_assoc _))))
    exact Eq.trans (Category.assoc _ _ _).symm
      (Eq.trans (congrArg (· ≫ γ'.hom.app 1) hback)
        (Eq.trans (Category.assoc _ _ _)
          (Eq.trans (congrArg (β.inv ≫ ·) hgen') (Category.assoc _ _ _).symm)))
  · have hback : SheafOfModules.sectionsMap (γ.inv.app 0) (TA T' Q.L).tensor.one =
        (TA T' ((Scheme.Modules.pullback g).obj P.L)).tensor.one :=
      Eq.trans (congrArg (SheafOfModules.sectionsMap (γ.inv.app 0)) hone).symm
        (congrArg (fun k : (TA T' ((Scheme.Modules.pullback g).obj P.L)).tensor.piece 0 ⟶
              (TA T' ((Scheme.Modules.pullback g).obj P.L)).tensor.piece 0 =>
            SheafOfModules.sectionsMap k
              (TA T' ((Scheme.Modules.pullback g).obj P.L)).tensor.one)
          (gradedAlgebraIsoApp γ 0).hom_inv_id)
    exact Eq.trans (congrArg (SheafOfModules.sectionsMap (γ'.hom.app 0)) hback) hone'
  · refine (pullbackMap_comp_iff A TA Q Q' n _).mp ?_
    calc Q.pullbackMap A TA n ≫ γ.inv.app n ≫ γ'.hom.app n
        = ((Scheme.Modules.pullbackComp g f).inv.app (A.piece n) ≫
            (Scheme.Modules.pullback g).map (P.pullbackMap A TA n) ≫
            (ι g P.L n).hom ≫ γ.hom.app n) ≫ γ.inv.app n ≫ γ'.hom.app n :=
          congrArg (· ≫ γ.inv.app n ≫ γ'.hom.app n) (hψ n).symm
      _ = (Scheme.Modules.pullbackComp g f).inv.app (A.piece n) ≫
            (Scheme.Modules.pullback g).map (P.pullbackMap A TA n) ≫
            (ι g P.L n).hom ≫ γ'.hom.app n :=
          assoc_of _ (assoc_of _ (assoc_of _ ((gradedAlgebraIsoApp γ n).hom_inv_id_assoc _)))
      _ = Q'.pullbackMap A TA n := hψ' n

/-! ### The classifying morphism and base change -/

variable {ι : TensorAlgebraPullbackIsos.{u} TA} {D : TwistData A}

/-- The class in `F1` of any canonical pullback of a pair is the pullback of its class. -/
public theorem pullbackClass_quot_mk (R : F1Representation A TA ι D) {T T' : Scheme.{u}}
    {f : T ⟶ S} (g : T' ⟶ T) (P : F1Pair A TA f) (Q : F1Pair A TA (g ≫ f))
    (hQ : IsPullbackPair A TA ι g P Q) :
    R.pullbackClass g (Quot.mk _ P) = Quot.mk _ Q := by
  obtain ⟨Q', hQ', hclass⟩ := R.pullbackClass_rep g P
  rw [hclass]
  exact (quot_mk_eq_iff_strictlyEquivalent A TA Q' Q).mpr
    (strictlyEquivalent_of_isPullbackPair A TA hQ' hQ)

/-- **A morphism over the base is the classifying morphism of a pair exactly when it induces the
class of that pair.**  This is the uniqueness in "characterized by" of Tag 01O9 and Tag 0D2Z. -/
public theorem eq_classifyingMorphism_iff (R : F1Representation A TA ι D) {T : Scheme.{u}}
    (f : T ⟶ S) (P : F1Pair A TA f)
    (h : {g : T ⟶ (relativeProj A).scheme // g ≫ (relativeProj A).toBase = f}) :
    h = R.classifyingMorphism f P ↔ R.homEquiv f h = Quot.mk _ P :=
  Equiv.eq_symm_apply (R.homEquiv f)

/-- **Characterizing property (2): the classifying morphism is compatible with base change of
the test scheme.**  Restricting the pair `P` along `g : T' ⟶ T` restricts the morphism it
classifies.  Tag 01O9 states this as the agreement of `r_{ℒ,ψ}` on a test scheme with the
morphism the construction of relative Proj attaches to the restricted pair. -/
public theorem comp_classifyingMorphism (R : F1Representation A TA ι D) {T T' : Scheme.{u}}
    {f : T ⟶ S} (g : T' ⟶ T) (P : F1Pair A TA f) (Q : F1Pair A TA (g ≫ f))
    (hQ : IsPullbackPair A TA ι g P Q) :
    g ≫ (R.classifyingMorphism f P).1 = (R.classifyingMorphism (g ≫ f) Q).1 := by
  refine congrArg Subtype.val
    ((eq_classifyingMorphism_iff A TA R (g ≫ f) Q ⟨g ≫ (R.classifyingMorphism f P).1, ?_⟩).mpr ?_)
  · rw [Category.assoc, (R.classifyingMorphism f P).2]
  · rw [R.homEquiv_natural g (R.classifyingMorphism f P), R.classifyingMorphism_spec]
    exact pullbackClass_quot_mk A TA R g P Q hQ

/-- Transporting a pair along an equality of structure morphisms transports its classifying
morphism. -/
public theorem classifyingMorphism_congr (R : F1Representation A TA ι D) {T : Scheme.{u}}
    {f f' : T ⟶ S} (e : f = f') (P : F1Pair A TA f) :
    (R.classifyingMorphism f P).1 = (R.classifyingMorphism f' (e ▸ P)).1 := by
  subst e
  rfl

/-- **The overlap compatibility.**  Two pairs on two test schemes whose restrictions to a common
test scheme are pullbacks of one and the same pair have classifying morphisms that agree on that
common test scheme. -/
public theorem comp_classifyingMorphism_eq_comp (R : F1Representation A TA ι D)
    {T₁ T₂ W : Scheme.{u}} {f₁ : T₁ ⟶ S} {f₂ : T₂ ⟶ S} {k₁ : W ⟶ T₁} {k₂ : W ⟶ T₂}
    (e : k₁ ≫ f₁ = k₂ ≫ f₂) (P₁ : F1Pair A TA f₁) (P₂ : F1Pair A TA f₂)
    (Q : F1Pair A TA (k₁ ≫ f₁)) (h₁ : IsPullbackPair A TA ι k₁ P₁ Q)
    (h₂ : IsPullbackPair A TA ι k₂ P₂ (e ▸ Q)) :
    k₁ ≫ (R.classifyingMorphism f₁ P₁).1 = k₂ ≫ (R.classifyingMorphism f₂ P₂).1 := by
  rw [comp_classifyingMorphism A TA R k₁ P₁ Q h₁,
    comp_classifyingMorphism A TA R k₂ P₂ (e ▸ Q) h₂]
  exact classifyingMorphism_congr A TA R e Q

/-! ### Glueing the local morphisms: the morphism `r_{ℒ,ψ}` -/

variable {U : Scheme.{u}} (R : F1Representation A TA ι D) (f : U ⟶ S) (𝒰 : U.OpenCover)

/-- **`r_{ℒ,ψ}`.**  Given a scheme `U` over the base, an open cover of `U`, and on each member a
pair — an invertible module with a graded map out of the restricted algebra, surjective in degree
one — whose classifying morphisms agree on the overlaps, the glued morphism
`U ⟶ Proj_S(𝒜)` over the base.

In Tag 01O9 and Tag 0D2Z the scheme `U` is `U(ψ)`, the cover is by the opens on which `ψ` is
surjective in a positive degree, and the pair on each member is the restriction of `(ℒ, ψ)`. -/
public def ofOpenCover (P : ∀ i, F1Pair A TA (𝒰.f i ≫ f))
    (hP : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (R.classifyingMorphism _ (P i)).1 =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ (R.classifyingMorphism _ (P j)).1) :
    U ⟶ (relativeProj A).scheme :=
  𝒰.glueMorphisms (fun i => (R.classifyingMorphism _ (P i)).1) hP

/-- **Characterizing property (2) for the glued morphism.**  It restricts on each member of the
cover to the morphism classified by the pair there. -/
public theorem ofOpenCover_restrict (P : ∀ i, F1Pair A TA (𝒰.f i ≫ f))
    (hP : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (R.classifyingMorphism _ (P i)).1 =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ (R.classifyingMorphism _ (P j)).1) (i : 𝒰.I₀) :
    𝒰.f i ≫ ofOpenCover A TA R f 𝒰 P hP = (R.classifyingMorphism _ (P i)).1 :=
  Scheme.Cover.ι_glueMorphisms 𝒰 _ hP i

/-- **The glued morphism lies over the base.**  This is the clause of Tag 01O9 and Tag 0D2Z that
`r_{ℒ,ψ}` is a morphism *over* the base. -/
public theorem ofOpenCover_comp_toBase (P : ∀ i, F1Pair A TA (𝒰.f i ≫ f))
    (hP : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (R.classifyingMorphism _ (P i)).1 =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ (R.classifyingMorphism _ (P j)).1) :
    ofOpenCover A TA R f 𝒰 P hP ≫ (relativeProj A).toBase = f :=
  𝒰.hom_ext _ _ fun i =>
    Eq.trans (Category.assoc _ _ _).symm
      (Eq.trans (congrArg (· ≫ (relativeProj A).toBase)
        (ofOpenCover_restrict A TA R f 𝒰 P hP i)) (R.classifyingMorphism _ (P i)).2)

/-- **The glued morphism is the only one with those restrictions.**  Together with
`ofOpenCover_restrict` this is the "characterized by" of Tag 01O9 and Tag 0D2Z for the data
presented by a cover. -/
public theorem eq_ofOpenCover (P : ∀ i, F1Pair A TA (𝒰.f i ≫ f))
    (hP : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (R.classifyingMorphism _ (P i)).1 =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ (R.classifyingMorphism _ (P j)).1)
    (g : U ⟶ (relativeProj A).scheme)
    (hg : ∀ i, 𝒰.f i ≫ g = (R.classifyingMorphism _ (P i)).1) :
    g = ofOpenCover A TA R f 𝒰 P hP :=
  𝒰.hom_ext _ _ fun i =>
    (hg i).trans (ofOpenCover_restrict A TA R f 𝒰 P hP i).symm

/-- The two overlap projections of an open cover, followed by the inclusions of the members and
the structure morphism to the base, give the same morphism to the base. -/
public theorem overlap_comp {V : Scheme.{u}} (g : V ⟶ S) (𝒱 : V.OpenCover) (i j : 𝒱.I₀) :
    pullback.fst (𝒱.f i) (𝒱.f j) ≫ 𝒱.f i ≫ g =
      pullback.snd (𝒱.f i) (𝒱.f j) ≫ 𝒱.f j ≫ g := by
  rw [← Category.assoc, pullback.condition, Category.assoc]

/-- **`r_{ℒ,ψ}` with the overlap hypothesis checked on pairs.**  It suffices that on each overlap
the two restricted pairs are canonical pullbacks of one common pair. -/
public def ofOpenCover_of_isPullbackPair (P : ∀ i, F1Pair A TA (𝒰.f i ≫ f))
    (Q : ∀ i j, F1Pair A TA (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ f))
    (hQ₁ : ∀ i j, IsPullbackPair A TA ι (pullback.fst (𝒰.f i) (𝒰.f j)) (P i) (Q i j))
    (hQ₂ : ∀ i j, IsPullbackPair A TA ι (pullback.snd (𝒰.f i) (𝒰.f j)) (P j)
      (overlap_comp f 𝒰 i j ▸ Q i j)) :
    U ⟶ (relativeProj A).scheme :=
  ofOpenCover A TA R f 𝒰 P fun i j =>
    comp_classifyingMorphism_eq_comp A TA R (overlap_comp f 𝒰 i j) (P i) (P j) (Q i j)
      (hQ₁ i j) (hQ₂ i j)

/-- The morphism of `ofOpenCover_of_isPullbackPair` restricts on each member of the cover to the
morphism classified by the pair there. -/
public theorem ofOpenCover_of_isPullbackPair_restrict (P : ∀ i, F1Pair A TA (𝒰.f i ≫ f))
    (Q : ∀ i j, F1Pair A TA (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ f))
    (hQ₁ : ∀ i j, IsPullbackPair A TA ι (pullback.fst (𝒰.f i) (𝒰.f j)) (P i) (Q i j))
    (hQ₂ : ∀ i j, IsPullbackPair A TA ι (pullback.snd (𝒰.f i) (𝒰.f j)) (P j)
      (overlap_comp f 𝒰 i j ▸ Q i j)) (i : 𝒰.I₀) :
    𝒰.f i ≫ ofOpenCover_of_isPullbackPair A TA R f 𝒰 P Q hQ₁ hQ₂ =
      (R.classifyingMorphism _ (P i)).1 :=
  ofOpenCover_restrict A TA R f 𝒰 P _ i

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
