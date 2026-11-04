module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.Invertible
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.BaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.RelativeSpecRepresentability.Basic

/-!
# Base change for the relative spectrum functor

Let `S` be a scheme carrying a quasi-coherent sheaf `A` of commutative `𝒪_S`-algebras, and let
`F` be the functor sending a test scheme `T` to the pairs `(f : T ⟶ S, φ : A ⟶ f_* 𝒪_T)`. For a
morphism `g : S' ⟶ S` put `A' = g^*A`, the pullback of `A` as an algebra sheaf, and let `F'` be
the functor attached to `(S', A')`. This file proves that `F'` is canonically the fibre product
`h_{S'} ×_{h_S} F`, which is Stacks Tag 01LS.

The structural natural transformation `Stacks.RelativeSpec.relativeSpecFunctorToBase : F ⟶ h_S`,
which forgets the algebra map of a pair, is taken from
`StacksFrontier.AlgebraicGeometry.RelativeSpec.BaseChange`, and so is
`Stacks.RelativeSpec.AlgebraSheaf.pairHomEquiv`, the identification of a morphism of algebra
sheaves `A ⟶ f_* 𝒪_T` with the algebra datum of a relative-spectrum pair over `T`; the two
`@[simp]` lemmas reading that identification off on underlying presheaves are here.

## Main definitions

* `Stacks.RelativeSpec.pairHomBaseChangeEquiv` is the transpose of that datum across base
  change: for `q : T ⟶ S'` the algebra maps `g^*A ⟶ q_* 𝒪_T` are the algebra maps
  `A ⟶ (q ≫ g)_* 𝒪_T`.
* `Stacks.RelativeSpec.RelativeSpecSituation.baseChange` is the relative-spectrum situation
  `(S', g^*A)`.
* `Stacks.RelativeSpec.baseChangeToOriginal` is the canonical transformation `F' ⟶ F`.
* `Stacks.RelativeSpec.relativeSpecFunctorBaseChangeIso` is the base-change isomorphism
  `F' ≅ h_{S'} ×_{h_S} F`.

## Main results

* `Stacks.RelativeSpec.RelativeSpecSituation.baseChange` is Tag 01LS's `A' = g^*A`: the
  pullback of a quasi-coherent algebra is again a quasi-coherent algebra, so `(S', g^*A)` is
  again a relative-spectrum situation.
* `Stacks.RelativeSpec.baseChangeToOriginal_app_fst` and
  `Stacks.RelativeSpec.baseChangeToOriginal_app_right` compute the two components of the
  canonical transformation `F' ⟶ F`.
* `Stacks.RelativeSpec.relativeSpecFunctorBaseChangeIso` is Tag 01LS, and
  `Stacks.RelativeSpec.relativeSpecFunctorBaseChangeIso_hom_fst`,
  `Stacks.RelativeSpec.relativeSpecFunctorBaseChangeIso_hom_snd` identify its two components
  with the structural map to the new base and with the canonical map to the original functor.

## Implementation notes

The pulled-back algebra is `Stacks.AffineAlgebraEquivalence.algebraPullback`, i.e.
`g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T`, which is quasi-coherent by
`Stacks.AlgebraPullbackQcoh.algebraPullback_isQuasicoherent`; no choice is involved, so
`RelativeSpecSituation.baseChange` is a construction and not a `Nonempty` statement.

The whole content of the tag is the single bijection `pairHomBaseChangeEquiv`, and that is the
adjunction `Stacks.AffineAlgebraEquivalence.algebraPullbackPushforwardAdjunction` between
pullback and direct image of algebra sheaves, read through
`Stacks.AffineAlgebraEquivalence.algebraPushforward_pushforwardAlgebra`
(`g_*(q_* 𝒪_T) = (q ≫ g)_* 𝒪_T`). Quasi-coherence is used nowhere in the argument; it is
needed only so that `(S', g^*A)` is a situation in the sense of Tag 01LM, which is what makes
`F'` "the functor attached to `(S', A')`" of the source.

A relative-spectrum pair records its algebra map after forgetting sheaves to presheaves, while
the adjunction lives in the category of sheaves of algebras; `AlgebraSheaf.pairHomEquiv` is the
translation, which loses nothing because a morphism of sheaves *is* a morphism of underlying
presheaves.

The displayed fibre product is the categorical pullback of functors to types, which carries the
functoriality in the test scheme automatically. That the comparison is invertible is checked on
each test scheme, where the abstract pullback is identified with the explicit subtype of the
product by `CategoryTheory.Limits.pullbackObjIso` and
`CategoryTheory.Limits.Types.pullbackIsoPullback`.

## References

* [Stacks Project, Tag 01LS](https://stacks.math.columbia.edu/tag/01LS)
* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01LR](https://stacks.math.columbia.edu/tag/01LR)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.RelativeSpec

/-! ### The algebra datum of a relative-spectrum pair -/

/-- The algebra datum attached to a morphism of algebra sheaves `A ⟶ f_* 𝒪_T` is that morphism,
read on underlying presheaves. -/
@[simp]
theorem AlgebraSheaf.pairHomEquiv_apply_right {X T : Scheme.{u}} (A : AlgebraSheaf X)
    (f : T ⟶ X) (u : A ⟶ pushforwardAlgebra f) :
    (A.pairHomEquiv f u).right = u.right.hom :=
  rfl

/-- The morphism of algebra sheaves attached to the algebra datum of a relative-spectrum pair
is, on underlying presheaves, that datum. -/
@[simp]
theorem AlgebraSheaf.pairHomEquiv_symm_apply_right {X T : Scheme.{u}} (A : AlgebraSheaf X)
    (f : T ⟶ X) (v : Under.mk A.hom.hom ⟶ Under.mk f.c) :
    ((A.pairHomEquiv f).symm v).right.hom = v.right :=
  rfl

/-! ### Transposing the algebra datum across base change -/

/-- **The content of [Stacks, Tag 01LS].** For `g : S' ⟶ S` and `q : T ⟶ S'`, the algebra maps
`g^*A ⟶ q_* 𝒪_T` on `S'` are canonically the algebra maps `A ⟶ (q ≫ g)_* 𝒪_T` on `S`.

This is the adjunction between pullback and direct image of algebra sheaves, together with the
identification `g_*(q_* 𝒪_T) = (q ≫ g)_* 𝒪_T`. It is the statement that a pair over `T` for
`(S', g^*A)` is the same thing as a pair over `T` for `(S, A)` whose morphism to `S` is given a
factorization through `g`. -/
def pairHomBaseChangeEquiv {S S' T : Scheme.{u}} (A : AlgebraSheaf S) (g : S' ⟶ S)
    (q : T ⟶ S') :
    (Under.mk ((algebraPullback g).obj A).hom.hom ⟶ Under.mk q.c) ≃
      (Under.mk A.hom.hom ⟶ Under.mk (q ≫ g).c) :=
  (AlgebraSheaf.pairHomEquiv ((algebraPullback g).obj A) q).symm.trans
    (((algebraPullbackPushforwardAdjunction g).homEquiv A (pushforwardAlgebra q)).trans
      (A.pairHomEquiv (q ≫ g)))

/-- The transpose of the algebra datum across base change, computed: it is the direct image
along `g` of the given datum, precomposed with the adjunct of the canonical map
`g⁻¹A ⟶ g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_{S'}`. -/
theorem pairHomBaseChangeEquiv_right {S S' T : Scheme.{u}} (A : AlgebraSheaf S) (g : S' ⟶ S)
    (q : T ⟶ S') (φ : Under.mk ((algebraPullback g).obj A).hom.hom ⟶ Under.mk q.c) :
    (pairHomBaseChangeEquiv A g q φ).right =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g.base).homEquiv
          A.right ((algebraPullback g).obj A).right
          ((algebraPullbackMap g).app A)).hom ≫
        (TopCat.Presheaf.pushforward CommRingCat g.base).map φ.right := by
  set u := (AlgebraSheaf.pairHomEquiv ((algebraPullback g).obj A) q).symm φ
  exact congrArg (fun k : A.right ⟶
    (TopCat.Sheaf.pushforward CommRingCat g.base).obj (pushforwardAlgebra q).right => k.hom)
    ((homEquiv_right g A (pushforwardAlgebra q) u).trans
      (Adjunction.homEquiv_naturality_right
        (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g.base)
        ((algebraPullbackMap g).app A) u.right))

/-! ### The base-changed situation -/

/-- **Stacks Project, Tag 01LS.** The relative-spectrum situation obtained from `(S, A)` by base
change along `g : S' ⟶ S`: the base is `S'` and the algebra is `A' = g^*A`, the pullback
`g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_{S'}` of `A` as an algebra sheaf, which is again quasi-coherent. -/
@[stacks 01LS "the base-changed situation (S', g^*A)"]
def RelativeSpecSituation.baseChange (s : RelativeSpecSituation.{u}) {S' : Scheme.{u}}
    (g : S' ⟶ s.base) : RelativeSpecSituation.{u} where
  base := S'
  algebra := (algebraPullback g).obj s.algebra
  isQuasicoherent :=
    Stacks.AlgebraPullbackQcoh.algebraPullback_isQuasicoherent g s.algebra s.isQuasicoherent

variable (s : RelativeSpecSituation.{u}) {S' : Scheme.{u}} (g : S' ⟶ s.base)

/-- The base of the base-changed situation is the source of the base-change morphism. -/
@[simp]
theorem baseChange_base : (s.baseChange g).base = S' :=
  rfl

/-- The algebra of the base-changed situation is the pullback of the original algebra. -/
@[simp]
theorem baseChange_algebra :
    (s.baseChange g).algebra = (algebraPullback g).obj s.algebra :=
  rfl

/-- Pulling a relative-spectrum pair back along a morphism of test schemes commutes with
transposing its algebra datum across base change. -/
theorem pairHomBaseChangeEquiv_pullback {T T' : Scheme.{u}} (a : T' ⟶ T)
    (p : RelativeSpecPair (s.baseChange g) T) :
    pairHomBaseChangeEquiv s.algebra g (RelativeSpecPair.pullback a p).1
        (RelativeSpecPair.pullback a p).2 =
      (RelativeSpecPair.pullback (s := s) a
        ⟨p.1 ≫ g, pairHomBaseChangeEquiv s.algebra g p.1 p.2⟩).2 := by
  refine Under.UnderMorphism.ext ?_
  refine (pairHomBaseChangeEquiv_right s.algebra g _ _).trans ?_
  refine (comp_functor_map_comp (TopCat.Presheaf.pushforward CommRingCat g.base) _ p.2.right
    ((TopCat.Presheaf.pushforward CommRingCat p.1.base).map a.c)).trans ?_
  exact congrArg (fun k : s.algebra.right.obj ⟶
      (TopCat.Presheaf.pushforward CommRingCat g.base).obj (Under.mk p.1.c).right =>
    k ≫ (TopCat.Presheaf.pushforward CommRingCat g.base).map
      ((TopCat.Presheaf.pushforward CommRingCat p.1.base).map a.c))
    (pairHomBaseChangeEquiv_right s.algebra g p.1 p.2).symm

/-! ### The base-change isomorphism -/

/-- The canonical natural transformation `F' ⟶ F` from the relative-spectrum functor of
`(S', g^*A)` to that of `(S, A)`: a pair `(q, φ')` over `T` is sent to `q ≫ g` together with the
transpose of `φ'` across base change. -/
def baseChangeToOriginal :
    relativeSpecFunctor (s.baseChange g) ⟶ relativeSpecFunctor s where
  app T := ↾fun p : RelativeSpecPair (s.baseChange g) T.unop ↦
    ⟨p.1 ≫ g, pairHomBaseChangeEquiv s.algebra g p.1 p.2⟩
  naturality X Y a := by
    ext p
    exact Sigma.ext rfl (heq_of_eq (pairHomBaseChangeEquiv_pullback s g a.unop p))

/-- **Stacks Project, Tag 01LS.** The morphism to `S` underlying the image of a pair under the
canonical transformation `F' ⟶ F` is the morphism to `S'` of the pair, composed with `g`. -/
@[stacks 01LS "base component of the canonical map to the original functor"]
theorem baseChangeToOriginal_app_fst {T : Scheme.{u}}
    (p : RelativeSpecPair (s.baseChange g) T) :
    ((baseChangeToOriginal s g).app (.op T) p).1 = p.1 ≫ g :=
  rfl

/-- **Stacks Project, Tag 01LS.** The algebra map of the image of a pair under the canonical
transformation `F' ⟶ F` is the direct image along `g` of the pair's algebra map, precomposed
with the adjunct of the canonical map `g⁻¹A ⟶ g^*A`. -/
@[stacks 01LS "algebra component of the canonical map to the original functor"]
theorem baseChangeToOriginal_app_right {T : Scheme.{u}}
    (p : RelativeSpecPair (s.baseChange g) T) :
    ((baseChangeToOriginal s g).app (.op T) p).2.right =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g.base).homEquiv
          s.algebra.right ((algebraPullback g).obj s.algebra).right
          ((algebraPullbackMap g).app s.algebra)).hom ≫
        (TopCat.Presheaf.pushforward CommRingCat g.base).map p.2.right :=
  pairHomBaseChangeEquiv_right s.algebra g p.1 p.2

/-- The square whose pullback is to be formed: the structural map of `F'` followed by `h_g`
agrees with the canonical map `F' ⟶ F` followed by the structural map of `F`.

This is the statement for the situation `s.baseChange g`;
`Stacks.RelativeSpec.relativeSpecFunctorToBase_comp_yoneda_map` is the corresponding statement
for a situation presented by an arbitrary extension-of-scalars datum. -/
theorem relativeSpecFunctorToBase_baseChange_comp_yoneda_map :
    relativeSpecFunctorToBase (s.baseChange g) ≫ yoneda.map g =
      baseChangeToOriginal s g ≫ relativeSpecFunctorToBase s := by
  ext T p
  rfl

/-- The comparison `F' ⟶ h_{S'} ×_{h_S} F` with components the structural map to the new base
and the canonical map to the original functor. -/
def baseChangeHom :
    relativeSpecFunctor (s.baseChange g) ⟶
      pullback (yoneda.map g) (relativeSpecFunctorToBase s) :=
  pullback.lift (relativeSpecFunctorToBase (s.baseChange g)) (baseChangeToOriginal s g)
    (relativeSpecFunctorToBase_baseChange_comp_yoneda_map s g)

/-- The first component of the comparison is the structural map to the new base. -/
theorem baseChangeHom_comp_fst :
    baseChangeHom s g ≫ pullback.fst (yoneda.map g) (relativeSpecFunctorToBase s) =
      relativeSpecFunctorToBase (s.baseChange g) :=
  pullback.lift_fst _ _ _

/-- The second component of the comparison is the canonical map to the original functor. -/
theorem baseChangeHom_comp_snd :
    baseChangeHom s g ≫ pullback.snd (yoneda.map g) (relativeSpecFunctorToBase s) =
      baseChangeToOriginal s g :=
  pullback.lift_snd _ _ _

/-- The comparison of a test scheme, with values in the explicit fibre product of sets. -/
def pullbackObjOfPair {T : Scheme.{u}} (p : RelativeSpecPair (s.baseChange g) T) :
    Types.PullbackObj ((yoneda.map g).app (.op T))
      ((relativeSpecFunctorToBase s).app (.op T)) :=
  ⟨⟨p.1, (baseChangeToOriginal s g).app (.op T) p⟩, rfl⟩

/-- On every test scheme the comparison with the explicit fibre product of sets is bijective:
injective because the transpose of the algebra datum is injective, surjective because a pair for
`(S, A)` whose morphism factors through `g` is the transpose of a pair for `(S', g^*A)`. -/
theorem pullbackObjOfPair_bijective {T : Scheme.{u}} :
    Function.Bijective (pullbackObjOfPair s g (T := T)) := by
  constructor
  · rintro ⟨q, φ⟩ ⟨q', φ'⟩ hp
    have hval := congrArg Subtype.val hp
    obtain rfl : q = q' := congrArg Prod.fst hval
    have hsnd : ((baseChangeToOriginal s g).app (.op T) ⟨q, φ⟩) =
        ((baseChangeToOriginal s g).app (.op T) ⟨q, φ'⟩) := congrArg Prod.snd hval
    refine congrArg (Sigma.mk q) ((pairHomBaseChangeEquiv s.algebra g q).injective ?_)
    exact eq_of_heq (Sigma.ext_iff.mp hsnd).2
  · rintro ⟨⟨q, ⟨f, φ⟩⟩, h⟩
    obtain rfl : q ≫ g = f := h
    exact ⟨⟨q, (pairHomBaseChangeEquiv s.algebra g q).symm φ⟩, Subtype.ext (Prod.ext rfl
      (congrArg (Sigma.mk (q ≫ g)) ((pairHomBaseChangeEquiv s.algebra g q).apply_symm_apply φ)))⟩

/-- On every test scheme the comparison `F' ⟶ h_{S'} ×_{h_S} F` is bijective: it is
`pullbackObjOfPair` read through the identification of the pullback of functors with the
explicit fibre product of sets. -/
theorem bijective_baseChangeHom_app (T : Scheme.{u}ᵒᵖ) :
    Function.Bijective ((baseChangeHom s g).app T) := by
  let e := Limits.pullbackObjIso (yoneda.map g) (relativeSpecFunctorToBase s) T ≪≫
    Types.pullbackIsoPullback ((yoneda.map g).app T) ((relativeSpecFunctorToBase s).app T)
  have hcomp (p : (relativeSpecFunctor (s.baseChange g)).obj T) :
      e.toEquiv ((baseChangeHom s g).app T p) = pullbackObjOfPair s g p := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · simp only [e, pullbackObjOfPair, Iso.toEquiv_fun, Iso.trans_hom,
      ConcreteCategory.comp_apply]
      rw [Types.pullbackIsoPullback_hom_fst, ← ConcreteCategory.comp_apply,
        pullbackObjIso_hom_comp_fst]
      exact ConcreteCategory.congr_hom
        (NatTrans.congr_app (baseChangeHom_comp_fst s g) T) p
    · simp only [e, pullbackObjOfPair, Iso.toEquiv_fun, Iso.trans_hom,
      ConcreteCategory.comp_apply]
      rw [Types.pullbackIsoPullback_hom_snd, ← ConcreteCategory.comp_apply,
        pullbackObjIso_hom_comp_snd]
      exact ConcreteCategory.congr_hom
        (NatTrans.congr_app (baseChangeHom_comp_snd s g) T) p
  have h : ⇑e.toEquiv ∘ ConcreteCategory.hom ((baseChangeHom s g).app T) =
      pullbackObjOfPair s g := funext hcomp
  rw [← Equiv.comp_bijective _ e.toEquiv, h]
  exact pullbackObjOfPair_bijective s g

/-- The comparison `F' ⟶ h_{S'} ×_{h_S} F` is an isomorphism, being bijective on every test
scheme. -/
instance isIso_baseChangeHom : IsIso (baseChangeHom s g) := by
  have : ∀ T, IsIso ((baseChangeHom s g).app T) := fun T => by
    rw [isIso_iff_bijective]
    exact bijective_baseChangeHom_app s g T
  exact NatIso.isIso_of_isIso_app _

/-- **Stacks Project, Tag 01LS.** Formation of the relative-spectrum functor commutes with
arbitrary base change: the functor attached to `(S', g^*A)` is canonically the fibre product
`h_{S'} ×_{h_S} F` of the functor of points of `S'` and the functor attached to `(S, A)` over
the functor of points of `S`. -/
@[stacks 01LS "canonical base-change isomorphism"]
def relativeSpecFunctorBaseChangeIso :
    relativeSpecFunctor (s.baseChange g) ≅
      pullback (yoneda.map g) (relativeSpecFunctorToBase s) :=
  asIso (baseChangeHom s g)

/-- **Stacks Project, Tag 01LS.** The first component of the base-change isomorphism is the
structural map of `F'` to the functor of points of the new base. -/
@[stacks 01LS "first component of the canonical isomorphism"]
theorem relativeSpecFunctorBaseChangeIso_hom_fst :
    (relativeSpecFunctorBaseChangeIso s g).hom ≫
        pullback.fst (yoneda.map g) (relativeSpecFunctorToBase s) =
      relativeSpecFunctorToBase (s.baseChange g) :=
  baseChangeHom_comp_fst s g

/-- **Stacks Project, Tag 01LS.** The second component of the base-change isomorphism is the
canonical transformation `F' ⟶ F` induced by the base-change map of algebras. -/
@[stacks 01LS "second component of the canonical isomorphism"]
theorem relativeSpecFunctorBaseChangeIso_hom_snd :
    (relativeSpecFunctorBaseChangeIso s g).hom ≫
        pullback.snd (yoneda.map g) (relativeSpecFunctorToBase s) =
      baseChangeToOriginal s g :=
  baseChangeHom_comp_snd s g

end Stacks.RelativeSpec

end
