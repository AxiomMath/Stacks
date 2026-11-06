module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.Topology.KrullDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The automorphism functor of a scheme over a base

Let `X` be a scheme over `S`. Its *automorphism functor* sends an `S`-scheme `T` to the group
`Aut_T(X_T)` of automorphisms of the base change `X_T = X ×_S T` over `T`, and a morphism
`h : T' ⟶ T` of `S`-schemes to base change of automorphisms along `h`. When this functor is
representable by an `S`-scheme `G`, the group scheme `G` is the automorphism group scheme
`Aut(X/S)`; the group structure on its points is the pointwise one, carried by Yoneda.

## Main definitions

* `AlgebraicGeometry.Scheme.baseChangeMap`: the canonical morphism `X_{T'} ⟶ X_T` over `h`.
* `AlgebraicGeometry.Scheme.endBaseChange`: the base change along `h` of an endomorphism of `X_T`
  over `T`.
* `AlgebraicGeometry.Scheme.autBaseChange`: the base change of an automorphism, a group
  homomorphism `Aut_T(X_T) →* Aut_{T'}(X_{T'})`.
* `AlgebraicGeometry.Scheme.autFunctor`: the functor `T ↦ Aut_T(X_T)` on `S`-schemes.
* `AlgebraicGeometry.Scheme.autFunctorIsoOfIso`: isomorphic `S`-schemes have isomorphic
  automorphism functors.

## Main results

* `AlgebraicGeometry.Scheme.endBaseChange_comp_baseChangeMap`: base change of an endomorphism
  commutes with the canonical morphism `X_{T'} ⟶ X_T`; together with the second projection this
  characterizes it.
* `AlgebraicGeometry.Scheme.endBaseChange_comp` and `AlgebraicGeometry.Scheme.endBaseChange_id`:
  base change is multiplicative.
* `AlgebraicGeometry.Scheme.endBaseChange_baseChange_id` and
  `AlgebraicGeometry.Scheme.endBaseChange_baseChange_comp`: base change is functorial in `h`.
* `AlgebraicGeometry.Scheme.topologicalKrullDim_left_eq_of_representableBy`: all representing
  objects of a functor on `S`-schemes, in particular all automorphism group schemes of `X`, have
  the same dimension.

## Implementation notes

The base change `X_T` is Mathlib's `(Over.pullback T.hom).obj X`, whose underlying scheme is the
chosen pullback `pullback X.hom T.hom` and whose structure morphism is the second projection.
Base change of an automorphism `ψ` along `h` is the unique endomorphism of `X_{T'}` over `T'`
whose composite with the first projection to `X` is the composite of the canonical morphism
`X_{T'} ⟶ X_T`, of `ψ` and of the first projection; no comparison isomorphism between iterated
pullbacks is involved, which is what makes the functor laws hold on the nose.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

variable {S : Scheme.{u}} (X : Over S)

/-- The canonical morphism `X ×_S T' ⟶ X ×_S T` over a morphism `h : T' ⟶ T` of `S`-schemes. -/
noncomputable def baseChangeMap {T T' : Over S} (h : T' ⟶ T) :
    pullback X.hom T'.hom ⟶ pullback X.hom T.hom :=
  pullback.map X.hom T'.hom X.hom T.hom (𝟙 _) h.left (𝟙 _) (by simp) (by simp)

/-- The canonical morphism `X_{T'} ⟶ X_T` commutes with the first projections to `X`. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_fst {T T' : Over S} (h : T' ⟶ T) :
    baseChangeMap X h ≫ pullback.fst X.hom T.hom = pullback.fst X.hom T'.hom := by
  simp [baseChangeMap]

/-- The canonical morphism `X_{T'} ⟶ X_T` lies over `h : T' ⟶ T`. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_snd {T T' : Over S} (h : T' ⟶ T) :
    baseChangeMap X h ≫ pullback.snd X.hom T.hom = pullback.snd X.hom T'.hom ≫ h.left := by
  simp [baseChangeMap]

/-- The canonical morphism over the identity of `T` is the identity of `X_T`. -/
@[simp]
theorem baseChangeMap_id (T : Over S) : baseChangeMap X (𝟙 T) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

/-- The canonical morphism over a composite `h' ≫ h` is the composite of the canonical
morphisms. -/
theorem baseChangeMap_comp {T T' T'' : Over S} (h : T' ⟶ T) (h' : T'' ⟶ T') :
    baseChangeMap X (h' ≫ h) = baseChangeMap X h' ≫ baseChangeMap X h := by
  apply pullback.hom_ext <;> simp

/-- An endomorphism of `X_T` over `T` commutes with the projection to `T`. -/
private theorem endo_left_snd {T : Over S}
    (φ : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj X) :
    φ.left ≫ pullback.snd X.hom T.hom = pullback.snd X.hom T.hom := Over.w φ

/-- The base change along `h : T' ⟶ T` of an endomorphism `φ` of `X_T` over `T`: the unique
endomorphism of `X_{T'}` over `T'` whose composite with the projection to `X` is
`X_{T'} ⟶ X_T ⟶ X_T ⟶ X`. -/
noncomputable def endBaseChange {T T' : Over S} (h : T' ⟶ T)
    (φ : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj X) :
    (Over.pullback T'.hom).obj X ⟶ (Over.pullback T'.hom).obj X :=
  Over.homMk (pullback.lift (baseChangeMap X h ≫ φ.left ≫ pullback.fst X.hom T.hom)
    (pullback.snd X.hom T'.hom) (by
      have hφ : φ.left ≫ pullback.snd X.hom T.hom = pullback.snd X.hom T.hom := Over.w φ
      simp only [Category.assoc, pullback.condition]
      rw [reassoc_of% hφ, baseChangeMap_snd_assoc, Over.w h])) (by simp)

/-- The composite of the base change of `φ` with the projection to `X` is
`X_{T'} ⟶ X_T ⟶ X_T ⟶ X`, through the canonical morphism and `φ`. -/
@[reassoc (attr := simp)]
theorem endBaseChange_left_fst {T T' : Over S} (h : T' ⟶ T)
    (φ : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj X) :
    (endBaseChange X h φ).left ≫ pullback.fst X.hom T'.hom =
      baseChangeMap X h ≫ φ.left ≫ pullback.fst X.hom T.hom := by
  simp [endBaseChange]

/-- The base change of `φ` commutes with the projection to `T'`. -/
@[reassoc (attr := simp)]
theorem endBaseChange_left_snd {T T' : Over S} (h : T' ⟶ T)
    (φ : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj X) :
    (endBaseChange X h φ).left ≫ pullback.snd X.hom T'.hom = pullback.snd X.hom T'.hom := by
  simp [endBaseChange]

/-- An endomorphism of `X_T` over `T` is determined by its composite with the projection to
`X`. -/
theorem endo_ext {T : Over S} {φ ψ : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj X}
    (h : φ.left ≫ pullback.fst X.hom T.hom = ψ.left ≫ pullback.fst X.hom T.hom) : φ = ψ := by
  ext1
  exact pullback.hom_ext h ((endo_left_snd X φ).trans (endo_left_snd X ψ).symm)

/-- **Base change commutes with the canonical morphism.** The square formed by the base change
of `φ`, by `φ` and by the canonical morphism `X_{T'} ⟶ X_T` commutes. -/
@[reassoc]
theorem endBaseChange_comp_baseChangeMap {T T' : Over S} (h : T' ⟶ T)
    (φ : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj X) :
    (endBaseChange X h φ).left ≫ baseChangeMap X h = baseChangeMap X h ≫ φ.left := by
  apply pullback.hom_ext
  · simp
  · simp [endo_left_snd X φ]

/-- The base change of the identity of `X_T` is the identity of `X_{T'}`. -/
@[simp]
theorem endBaseChange_id {T T' : Over S} (h : T' ⟶ T) :
    endBaseChange X h (𝟙 _) = 𝟙 _ :=
  endo_ext X (by simp)

/-- Base change of endomorphisms along `h` preserves composition. -/
theorem endBaseChange_comp {T T' : Over S} (h : T' ⟶ T)
    (φ ψ : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj X) :
    endBaseChange X h (φ ≫ ψ) = endBaseChange X h φ ≫ endBaseChange X h ψ :=
  endo_ext X (by simp [endBaseChange_comp_baseChangeMap_assoc])

/-- Base change of an endomorphism along the identity of `T` is the endomorphism itself. -/
@[simp]
theorem endBaseChange_baseChange_id {T : Over S}
    (φ : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj X) :
    endBaseChange X (𝟙 T) φ = φ :=
  endo_ext X (by simp)

/-- Base change of an endomorphism along a composite `h' ≫ h` is base change along `h`
followed by base change along `h'`. -/
theorem endBaseChange_baseChange_comp {T T' T'' : Over S} (h : T' ⟶ T) (h' : T'' ⟶ T')
    (φ : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj X) :
    endBaseChange X (h' ≫ h) φ = endBaseChange X h' (endBaseChange X h φ) :=
  endo_ext X (by simp [baseChangeMap_comp])

/-- The base change along `h : T' ⟶ T` of automorphisms, `Aut_T(X_T) →* Aut_{T'}(X_{T'})`. -/
noncomputable def autBaseChange {T T' : Over S} (h : T' ⟶ T) :
    Aut ((Over.pullback T.hom).obj X) →* Aut ((Over.pullback T'.hom).obj X) where
  toFun ψ := .of
    { hom := endBaseChange X h ψ.asIso.hom
      inv := endBaseChange X h ψ.asIso.inv
      hom_inv_id := by rw [← endBaseChange_comp, ψ.asIso.hom_inv_id, endBaseChange_id]
      inv_hom_id := by rw [← endBaseChange_comp, ψ.asIso.inv_hom_id, endBaseChange_id] }
  map_one' := Aut.ext (Iso.ext (endBaseChange_id X h))
  map_mul' ψ ψ' := Aut.ext (Iso.ext (endBaseChange_comp X h ψ'.asIso.hom ψ.asIso.hom))

/-- The underlying morphism of the base change of an automorphism `ψ` is the base change of
`ψ.hom`. -/
@[simp]
theorem autBaseChange_hom {T T' : Over S} (h : T' ⟶ T) (ψ : Aut ((Over.pullback T.hom).obj X)) :
    (autBaseChange X h ψ).asIso.hom = endBaseChange X h ψ.asIso.hom :=
  rfl

/-- The inverse of the base change of an automorphism `ψ` is the base change of `ψ.inv`. -/
@[simp]
theorem autBaseChange_inv {T T' : Over S} (h : T' ⟶ T) (ψ : Aut ((Over.pullback T.hom).obj X)) :
    (autBaseChange X h ψ).asIso.inv = endBaseChange X h ψ.asIso.inv :=
  rfl

/-- **The automorphism functor** `T ↦ Aut_T(X ×_S T)` of an `S`-scheme `X`, on the category of
`S`-schemes, acting on morphisms by base change of automorphisms. A representing object of this
functor is the automorphism group scheme `Aut(X/S)`. -/
@[sga "3 III 0.11"]
noncomputable def autFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Aut ((Over.pullback T.unop.hom).obj X)
  map h := ↾fun ψ ↦ autBaseChange X h.unop ψ
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro ψ
    exact Aut.ext (Iso.ext (endBaseChange_baseChange_id X ψ.asIso.hom))
  map_comp h h' := by
    apply ConcreteCategory.hom_ext
    intro ψ
    exact Aut.ext (Iso.ext (endBaseChange_baseChange_comp X h.unop h'.unop ψ.asIso.hom))

/-- The value of the automorphism functor at `T` is the automorphism group of `X_T` over `T`. -/
@[simp]
theorem autFunctor_obj (T : (Over S)ᵒᵖ) :
    (autFunctor X).obj T = Aut ((Over.pullback T.unop.hom).obj X) :=
  rfl

/-- The automorphism functor sends a morphism `h` to base change of automorphisms along
`h.unop`. -/
@[simp]
theorem autFunctor_map_apply {T T' : (Over S)ᵒᵖ} (h : T ⟶ T')
    (ψ : Aut ((Over.pullback T.unop.hom).obj X)) :
    (autFunctor X).map h ψ = autBaseChange X h.unop ψ :=
  rfl

/-! ### Transport along an isomorphism -/

variable {X} {Y : Over S}

/-- The base change to `T` of a morphism `e : X ⟶ Y` of `S`-schemes commutes with the canonical
morphisms of base changes along `h : T' ⟶ T`. -/
@[reassoc]
theorem pullback_map_left_comp_baseChangeMap (e : X ⟶ Y) {T T' : Over S} (h : T' ⟶ T) :
    ((Over.pullback T'.hom).map e).left ≫ baseChangeMap Y h =
      baseChangeMap X h ≫ ((Over.pullback T.hom).map e).left := by
  apply pullback.hom_ext <;> simp

/-- Conjugation by the base change of an isomorphism `e : X ≅ Y` commutes with base change of
endomorphisms. -/
theorem endBaseChange_conj (e : X ≅ Y) {T T' : Over S} (h : T' ⟶ T)
    (φ : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj X) :
    endBaseChange Y h ((Over.pullback T.hom).map e.inv ≫ φ ≫ (Over.pullback T.hom).map e.hom) =
      (Over.pullback T'.hom).map e.inv ≫ endBaseChange X h φ ≫
        (Over.pullback T'.hom).map e.hom := by
  apply endo_ext
  have key : ∀ {T : Over S}, ((Over.pullback T.hom).map e.hom).left ≫
      pullback.fst Y.hom T.hom = pullback.fst X.hom T.hom ≫ e.hom.left := by
    simp
  simp only [Over.comp_left, Category.assoc, endBaseChange_left_fst,
    endBaseChange_left_fst_assoc, key]
  rw [← pullback_map_left_comp_baseChangeMap_assoc e.inv h]

/-- **Isomorphic schemes have isomorphic automorphism functors**: conjugation by the base changes
of an isomorphism `e : X ≅ Y` of `S`-schemes. -/
noncomputable def autFunctorIsoOfIso (e : X ≅ Y) : autFunctor X ≅ autFunctor Y :=
  NatIso.ofComponents (fun T ↦ ((Over.pullback T.unop.hom).mapIso e).conjAut.toEquiv.toIso) (by
    intro T T' h
    apply ConcreteCategory.hom_ext
    intro ψ
    exact Aut.ext (Iso.ext (endBaseChange_conj e h.unop ψ.asIso.hom).symm))

/-- The isomorphism of automorphism functors induced by `e : X ≅ Y` sends an automorphism `ψ`
of `X_T` to its conjugate by the base change of `e`. -/
@[simp]
theorem autFunctorIsoOfIso_hom_app_hom (e : X ≅ Y) (T : (Over S)ᵒᵖ)
    (ψ : Aut ((Over.pullback T.unop.hom).obj X)) :
    ((autFunctorIsoOfIso e).hom.app T ψ).asIso.hom =
      (Over.pullback T.unop.hom).map e.inv ≫ ψ.asIso.hom ≫ (Over.pullback T.unop.hom).map e.hom :=
  rfl

/-! ### Representing objects -/

/-- Representing objects of a functor on `S`-schemes have homeomorphic underlying schemes, hence
the same dimension. -/
theorem topologicalKrullDim_left_eq_of_representableBy
    {F : (Over S)ᵒᵖ ⥤ Type u} {G G' : Over S} (R : F.RepresentableBy G)
    (R' : F.RepresentableBy G') : topologicalKrullDim G.left = topologicalKrullDim G'.left := by
  let e : G.left ≅ G'.left := (Over.forget S).mapIso (R.uniqueUpToIso R')
  exact IsHomeomorph.topologicalKrullDim_eq _
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isHomeomorph

end AlgebraicGeometry.Scheme
