module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorPlainIso
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestriction

/-!
# The transition maps of a derived tensor tower, read through the plain tensor products

Let `(A, d)`, `(A', d)` and `(B, d)` be differential graded algebras over a commutative ring `R`,
let `φ : A ⟶ A'` be a homomorphism of differential graded algebras, let `P` be a differential
graded `(A, B)`-bimodule and `P'` a differential graded `(A', B)`-bimodule. A comparison of the
*plain* tensor functors
`τ : (- |_A) ⊗_A P ⟶ - ⊗_{A'} P'`
— a homomorphism `P ⊗_A Y|_A ⟶ P' ⊗_{A'} Y` of differential graded `B`-modules for every
differential graded `A'`-module `Y`, natural in `Y` — induces a comparison
`P ⊗_A^𝐋 (- |_A) ⟶ P' ⊗_{A'}^𝐋 -`
of the derived tensor functors, by the universal property of the derived tensor product of
Tag 09LS as a left derived functor. The two are compatible: the derived comparison, read through
the identification `DifferentialGraded.Bimodule.derivedTensorObjIsoPlain` of a derived tensor
product at a module orthogonal on the left to the acyclic modules with the plain one, *is* `τ`.

This is the naturality that an isomorphism of objects of `D(B, d)` does not by itself provide. A
tower `n ↦ P_n ⊗_{A_n}^𝐋 X_n` has for its transition maps the derived comparisons above composed
with the derived tensor product of the transition maps `X_m ⟶ X_n|_{A_m}` of the modules; the
main result below says that transition map, read through the plain isomorphisms, is the plain
transition map `P_m ⊗_{A_m} X_m ⟶ P_n ⊗_{A_n} X_n`. Two such towers are therefore isomorphic as
functors `ℕᵒᵖ ⥤ D(B, d)` as soon as their *plain* transition squares commute, which is a
statement about homomorphisms of differential graded modules.

## Main definitions

* `DifferentialGraded.Bimodule.restrictTensorHomotopyTrans`: the comparison of the plain tensor
  functors, read on the homotopy categories.
* `DifferentialGraded.Bimodule.derivedTensorRestrictTrans`: the induced comparison
  `P ⊗_A^𝐋 (- |_A) ⟶ P' ⊗_{A'}^𝐋 -` of the derived tensor functors.

## Main results

* `DifferentialGraded.Bimodule.derivedTensorObjIsoPlain_naturality`: the identification of a
  derived tensor product with the plain one is natural in the module.
* `DifferentialGraded.Bimodule.derivedTensorRestrictTrans_app_comp_counit`: the derived
  comparison, followed by the comparison of Tag 0BZ2 for `P'`, is the plain comparison. This is
  the defining property of the lift, and everything else is a consequence of it.
* `DifferentialGraded.Bimodule.derivedTensorRestrictTrans_unique`: that property determines the
  derived comparison, so a comparison built by any other route is covered by the results below
  once it is checked.
* `DifferentialGraded.Bimodule.derivedTensorRestrictTrans_towerMap`: **the transition map of a
  derived tensor tower is the plain one.** At modules orthogonal on the left to the acyclic
  modules, the derived tensor product of a transition homomorphism followed by the derived
  comparison, read through
  `DifferentialGraded.Bimodule.derivedTensorObjIsoPlain`, is the plain transition homomorphism.
* `DifferentialGraded.Bimodule.derivedTensorObjIsoOfTensorIso_naturality`: **the naturality
  square.** Two derived tensor towers whose plain transition squares commute have commuting
  derived transition squares, for the isomorphisms
  `DifferentialGraded.Bimodule.derivedTensorObjIsoOfTensorIso`.

## Implementation notes

*Why the derived comparison is constructed rather than assumed.* A comparison of the derived
tensor functors over two different algebras is not determined by its values on objects, and an
arbitrary such comparison has no relation to the plain tensor products; a square for it would
have to be assumed. The construction below instead produces it from the plain comparison by
`CategoryTheory.Functor.leftDerivedLift`, the universal property of a left derived functor, whose
defining identity `CategoryTheory.Functor.leftDerived_fac_app` is exactly the compatibility with
the comparison of Tag 0BZ2 that the squares need. Nothing is assumed beyond `τ`, which is a
natural transformation of functors between categories of differential graded modules.

*The homotopy-category step.* The universal property asks for a natural transformation out of
`Q ⋙ (- |_A ⊗_A^𝐋 P)` defined on the whole homotopy category of `A'`, so `τ` has to be carried
from differential graded modules to homotopy classes. That is
`CategoryTheory.Quotient.natTransLift` applied to `τ` conjugated by the comparison of Tag 09LM
(`DifferentialGraded.Bimodule.tensorCompFunctor_quotient`) on either side and by
`DifferentialGradedModule.restrictScalarsHomotopyFunctorIso` on the source.

*Abstract diagram lemmas.* The identities below are composed in a localized category, where
`CategoryTheory.Category.assoc` does not rewrite: the two sides present `CategoryTheory.Quiver.Hom`
at different instance paths. They are therefore proved for abstract categories and functors and
instantiated by `exact`, which is the device of
`DifferentialGradedModule.derivedTrans_comp_aux`.

*The transition map of the modules is taken as a parameter.* The map
`X ⟶ X'|_A` of the tower is read in the derived category as
`DifferentialGradedModule.derivedTrans`; that map is passed as an explicit argument together with
the identification of it, to be substituted away, so that the statement is usable at whatever
presentation of it a consumer has.

## References

* [Stacks Project, Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) is the derived tensor
  product and its universal property, [Tag 0BZ2](https://stacks.math.columbia.edu/tag/0BZ2) the
  comparison with the plain tensor product, [Tag 09LM](https://stacks.math.columbia.edu/tag/09LM)
  the plain tensor product and its compatibility with homotopy classes,
  [Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX) restriction of scalars and
  [Tag 09KM](https://stacks.math.columbia.edu/tag/09KM) the orthogonality under which the
  comparison of Tag 0BZ2 is invertible.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

/-! ### Abstract diagram lemmas

The identities below are stated for abstract categories and functors; they are instantiated at
the homotopy and derived categories of differential graded modules further down. -/

/-- **Naturality of a localized comparison.** Let `ε : Q₁ ⋙ L ⟶ T ⋙ Q₂` and let
`γ : S ⋙ q₂ ≅ q₁ ⋙ T` identify two presentations of a functor on homotopy classes. Then the
composite `ε.app (q₁.obj X) ≫ Q₂.map (γ.inv.app X)` is natural in `X`. -/
theorem localizedComparison_naturality_aux
    {M₁ M₂ H₁ H₂ E₁ E₂ : Type*} [Category M₁] [Category M₂] [Category H₁] [Category H₂]
    [Category E₁] [Category E₂] {q₁ : M₁ ⥤ H₁} {q₂ : M₂ ⥤ H₂} {Q₁ : H₁ ⥤ E₁} {Q₂ : H₂ ⥤ E₂}
    {L : E₁ ⥤ E₂} {T : H₁ ⥤ H₂} {S : M₁ ⥤ M₂} (ε : Q₁ ⋙ L ⟶ T ⋙ Q₂) (γ : S ⋙ q₂ ≅ q₁ ⋙ T)
    {X Y : M₁} (g : X ⟶ Y) :
    L.map (Q₁.map (q₁.map g)) ≫ ε.app (q₁.obj Y) ≫ Q₂.map (γ.inv.app Y) =
      (ε.app (q₁.obj X) ≫ Q₂.map (γ.inv.app X)) ≫ Q₂.map (q₂.map (S.map g)) := by
  have hε : L.map (Q₁.map (q₁.map g)) ≫ ε.app (q₁.obj Y) =
      ε.app (q₁.obj X) ≫ Q₂.map (T.map (q₁.map g)) := ε.naturality (q₁.map g)
  have hγ : T.map (q₁.map g) ≫ γ.inv.app Y = γ.inv.app X ≫ q₂.map (S.map g) :=
    γ.inv.naturality g
  rw [← Category.assoc, hε, Category.assoc, ← Functor.map_comp, hγ, Functor.map_comp,
    Category.assoc]

/-- **A functor applied to an identity drops out of a composite.** Stated for abstract
categories: in a quotient or localized category the identity of an object is presented at
several instance paths, and `CategoryTheory.Functor.map_id` then refuses to rewrite. -/
theorem map_id_comp_aux {E F : Type*} [Category E] [Category F] (G : E ⥤ F) {X : E} {Y : F}
    (i : X ⟶ X) (hi : i = 𝟙 X) (g : G.obj X ⟶ Y) : G.map i ≫ g = g := by
  rw [hi, G.map_id, Category.id_comp]

/-- **The transition map of a tower, read through two localized comparisons.** Stated for
abstract categories and functors, and instantiated at the derived categories of differential
graded modules in
`DifferentialGraded.Bimodule.derivedTensorRestrictTrans_towerMap`: `bInv` and `bHom` are the two
directions of the factorization of restriction of scalars, `c` the comparison of the derived
functors, `e` and `e₀` the comparisons with the plain functors, `σ` the comparison of the plain
functors on homotopy classes and `k`, `f` the two directions of the identification of the plain
functor with its presentation on homotopy classes. -/
theorem towerMap_aux {D E F : Type*} [Category D] [Category E] [Category F]
    (L : D ⥤ E) (G : F ⥤ E) {d₀ d₁ d₂ : D} {o : E} {x₀ x₁ y y' z t : F}
    (a : d₀ ⟶ d₁) (bInv : d₁ ⟶ d₂) (bHom : d₂ ⟶ d₁) (hb : bInv ≫ bHom = 𝟙 d₁)
    (c : L.obj d₂ ⟶ o) (e : o ⟶ G.obj t) (f : t ⟶ z)
    (e₁ : L.obj d₁ ⟶ G.obj y) (σ : y ⟶ t) (f₁ : y ⟶ y') (h : y' ⟶ z) (k : z ⟶ t)
    (e₀ : L.obj d₀ ⟶ G.obj x₀) (f₀ : x₀ ⟶ x₁) (g₀ : x₁ ⟶ y') (g : x₁ ⟶ z)
    (hc : c ≫ e = L.map bHom ≫ e₁ ≫ G.map σ)
    (hσ : σ = f₁ ≫ h ≫ k) (hk : k ≫ f = 𝟙 z)
    (hnat : L.map a ≫ e₁ ≫ G.map f₁ = (e₀ ≫ G.map f₀) ≫ G.map g₀)
    (hg : g₀ ≫ h = g) :
    (L.map (a ≫ bInv) ≫ c) ≫ e ≫ G.map f = (e₀ ≫ G.map f₀) ≫ G.map g := by
  have hσf : σ ≫ f = f₁ ≫ h := by
    rw [hσ, Category.assoc, Category.assoc, hk, Category.comp_id]
  have step1 : (L.map (a ≫ bInv) ≫ c) ≫ e ≫ G.map f
      = L.map a ≫ e₁ ≫ G.map (σ ≫ f) := by
    rw [L.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc c e, hc]
    simp only [Category.assoc, ← L.map_comp_assoc, hb, L.map_id, Category.id_comp,
      ← G.map_comp]
  rw [step1, hσf, G.map_comp, ← Category.assoc, ← Category.assoc, ← hg, G.map_comp]
  rw [Category.assoc, Category.assoc, ← Category.assoc e₁, ← Category.assoc (L.map a), hnat]
  simp only [Category.assoc]

/-- **Two tower transition maps and a square of the plain objects.** Stated for abstract
categories and functors, and instantiated at the derived categories of differential graded
modules in `DifferentialGraded.Bimodule.derivedTensorObjIsoOfTensorIso_naturality`: `T₁` and `T₂`
are the two transition maps, `i₁`, `i₁'`, `i₂`, `i₂'` the identifications of their sources and
targets with plain objects, `pl₁` and `pl₂` the plain transition maps and `eh`, `eh'` the two
horizontal plain maps. -/
theorem towerSquare_aux {M F E : Type*} [Category M] [Category F] [Category E]
    (q : M ⥤ F) (G : F ⥤ E) {o₁ o₁' o₂ o₂' : E} {m₁ m₁' m₂ m₂' : M}
    (T₁ : o₁ ⟶ o₁') (T₂ : o₂ ⟶ o₂')
    (i₁ : o₁ ≅ G.obj (q.obj m₁)) (i₁' : o₁' ≅ G.obj (q.obj m₁'))
    (i₂ : o₂ ≅ G.obj (q.obj m₂)) (i₂' : o₂' ≅ G.obj (q.obj m₂'))
    (pl₁ : m₁ ⟶ m₁') (pl₂ : m₂ ⟶ m₂') (eh : m₁ ⟶ m₂) (eh' : m₁' ⟶ m₂')
    (h₁ : T₁ ≫ i₁'.hom = i₁.hom ≫ G.map (q.map pl₁))
    (h₂ : T₂ ≫ i₂'.hom = i₂.hom ≫ G.map (q.map pl₂))
    (hsq : pl₁ ≫ eh' = eh ≫ pl₂) :
    T₁ ≫ i₁'.hom ≫ G.map (q.map eh') ≫ i₂'.inv =
      (i₁.hom ≫ G.map (q.map eh) ≫ i₂.inv) ≫ T₂ := by
  have hT₂ : T₂ = i₂.hom ≫ G.map (q.map pl₂) ≫ i₂'.inv := by
    rw [← Category.assoc, ← h₂, Category.assoc, i₂'.hom_inv_id, Category.comp_id]
  have hmid : G.map (q.map pl₁) ≫ G.map (q.map eh') =
      G.map (q.map eh) ≫ G.map (q.map pl₂) := by
    rw [← G.map_comp, ← G.map_comp, ← q.map_comp, ← q.map_comp, hsq]
  rw [hT₂, ← Category.assoc T₁, h₁]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (G.map (q.map pl₁)), hmid, Category.assoc]

variable {R : Type u} [CommRing R] {A A' B : DifferentialGradedAlgebra.{u, u} R}

/-! ### The identification with the plain tensor product is natural in the module -/

/-- The identification of a derived tensor product at a module orthogonal on the left to the
acyclic modules with the plain tensor product is the comparison of Tag 0BZ2 followed by the
comparison of Tag 09LM. -/
theorem derivedTensorObjIsoPlain_hom (N : Bimodule A B)
    (X : DifferentialGradedModule.{u, u, u} A)
    (hX : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj X)) :
    (derivedTensorObjIsoPlain N X hX).hom =
      (derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj X) ≫
        (quasiIsomorphisms' B).Q.map ((tensorCompFunctor_quotient N).inv.app X) :=
  rfl

/-- **The identification with the plain tensor product is natural in the module.** For a
homomorphism `g : X ⟶ Y` of differential graded `A`-modules with `X` and `Y` orthogonal on the
left to the acyclic modules, the square relating `X ⊗_A^𝐋 N ≅ X ⊗_A N`, `Y ⊗_A^𝐋 N ≅ Y ⊗_A N`,
the derived tensor product of `g` and the plain tensor product of `g` commutes. -/
theorem derivedTensorObjIsoPlain_naturality (N : Bimodule A B)
    {X Y : DifferentialGradedModule.{u, u, u} A}
    (hX : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj X))
    (hY : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj Y)) (g : X ⟶ Y) :
    (derivedTensorFunctor N).map ((quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map g)) ≫
        (derivedTensorObjIsoPlain N Y hY).hom =
      (derivedTensorObjIsoPlain N X hX).hom ≫
        (quasiIsomorphisms' B).Q.map
          ((toHomotopyCategory B).map ((tensorCompFunctor N).map g)) := by
  rw [derivedTensorObjIsoPlain_hom, derivedTensorObjIsoPlain_hom]
  exact localizedComparison_naturality_aux (derivedTensorFunctorCounit N)
    (tensorCompFunctor_quotient N) g

/-! ### The comparison of the derived tensor functors induced by a plain one -/

/-- The comparison of the plain tensor functors, read on differential graded modules and then
pushed to homotopy classes: for a differential graded `A'`-module `Y` this is the homotopy class
of `τ.app Y : P ⊗_A Y|_A ⟶ P' ⊗_{A'} Y`, conjugated by the comparison of Tag 09LM on either side
and by the compatibility of restriction of scalars with homotopy classes on the source. -/
def restrictTensorHomotopyTransQuotient (φ : A.Hom A') (P : Bimodule A B) (P' : Bimodule A' B)
    (τ : restrictScalarsFunctor φ ⋙ tensorCompFunctor P ⟶ tensorCompFunctor P') :
    toHomotopyCategory A' ⋙ restrictScalarsHomotopyFunctor φ ⋙ tensorHomotopyFunctor P ⟶
      toHomotopyCategory A' ⋙ tensorHomotopyFunctor P' :=
  Functor.whiskerRight (restrictScalarsHomotopyFunctorIso φ).hom (tensorHomotopyFunctor P) ≫
    Functor.whiskerLeft (restrictScalarsFunctor φ) (tensorCompFunctor_quotient P).inv ≫
      Functor.whiskerRight τ (toHomotopyCategory B) ≫ (tensorCompFunctor_quotient P').hom

/-- **The comparison of the plain tensor functors on the homotopy categories.** It descends from
differential graded modules because the homotopy category is their quotient. -/
def restrictTensorHomotopyTrans (φ : A.Hom A') (P : Bimodule A B) (P' : Bimodule A' B)
    (τ : restrictScalarsFunctor φ ⋙ tensorCompFunctor P ⟶ tensorCompFunctor P') :
    restrictScalarsHomotopyFunctor φ ⋙ tensorHomotopyFunctor P ⟶ tensorHomotopyFunctor P' :=
  CategoryTheory.Quotient.natTransLift _ (restrictTensorHomotopyTransQuotient φ P P' τ)

/-- The comparison on the homotopy categories, at the class of a differential graded module. -/
theorem restrictTensorHomotopyTrans_app (φ : A.Hom A') (P : Bimodule A B) (P' : Bimodule A' B)
    (τ : restrictScalarsFunctor φ ⋙ tensorCompFunctor P ⟶ tensorCompFunctor P')
    (Y : DifferentialGradedModule.{u, u, u} A') :
    (restrictTensorHomotopyTrans φ P P' τ).app ((toHomotopyCategory A').obj Y) =
      (tensorCompFunctor_quotient P).inv.app ((restrictScalarsFunctor φ).obj Y) ≫
        (toHomotopyCategory B).map (τ.app Y) ≫ (tensorCompFunctor_quotient P').hom.app Y := by
  exact map_id_comp_aux (tensorHomotopyFunctor P)
    ((restrictScalarsHomotopyFunctorIso φ).hom.app Y) rfl _

/-- The natural transformation out of which the comparison of the derived tensor functors is
lifted: the factorization of derived restriction of scalars, followed by the comparison of
Tag 0BZ2 for `P`, followed by the comparison of the plain tensor functors on the homotopy
categories. -/
def derivedTensorRestrictTransQuotient (φ : A.Hom A') (P : Bimodule A B) (P' : Bimodule A' B)
    (τ : restrictScalarsFunctor φ ⋙ tensorCompFunctor P ⟶ tensorCompFunctor P') :
    (quasiIsomorphisms' A').Q ⋙ derivedRestriction φ ⋙ derivedTensorFunctor P ⟶
      tensorFunctorToDerivedCategory P' :=
  Functor.whiskerRight (derivedRestrictionFactorization φ).hom (derivedTensorFunctor P) ≫
    Functor.whiskerLeft (restrictScalarsHomotopyFunctor φ) (derivedTensorFunctorCounit P) ≫
      Functor.whiskerRight (restrictTensorHomotopyTrans φ P P' τ) (quasiIsomorphisms' B).Q

/-- **The comparison of the derived tensor functors induced by a comparison of the plain ones.**
It is the lift of `DifferentialGraded.Bimodule.derivedTensorRestrictTransQuotient` through the
universal property of `- ⊗_{A'}^𝐋 P'` as the left derived functor of plain tensoring with `P'`,
which is Tag 09LS. -/
def derivedTensorRestrictTrans (φ : A.Hom A') (P : Bimodule A B) (P' : Bimodule A' B)
    (τ : restrictScalarsFunctor φ ⋙ tensorCompFunctor P ⟶ tensorCompFunctor P') :
    derivedRestriction φ ⋙ derivedTensorFunctor P ⟶ derivedTensorFunctor P' :=
  (derivedTensorFunctor P').leftDerivedLift (derivedTensorFunctorCounit P')
    (quasiIsomorphisms' A') (derivedRestriction φ ⋙ derivedTensorFunctor P)
    (derivedTensorRestrictTransQuotient φ P P' τ)

/-- **The defining property of the comparison of the derived tensor functors.** Followed by the
comparison of Tag 0BZ2 for `P'`, it is the factorization of derived restriction of scalars
followed by the comparison of Tag 0BZ2 for `P` followed by `τ`. -/
theorem derivedTensorRestrictTrans_app_comp_counit (φ : A.Hom A') (P : Bimodule A B)
    (P' : Bimodule A' B)
    (τ : restrictScalarsFunctor φ ⋙ tensorCompFunctor P ⟶ tensorCompFunctor P')
    (Z : HomotopyCategory A') :
    (derivedTensorRestrictTrans φ P P' τ).app ((quasiIsomorphisms' A').Q.obj Z) ≫
        (derivedTensorFunctorCounit P').app Z =
      (derivedTensorRestrictTransQuotient φ P P' τ).app Z :=
  Functor.leftDerived_fac_app _ _ _ _ _ Z

/-- The natural transformation that the comparison of the derived tensor functors is lifted
from, at an object of the homotopy category. -/
theorem derivedTensorRestrictTransQuotient_app (φ : A.Hom A') (P : Bimodule A B)
    (P' : Bimodule A' B)
    (τ : restrictScalarsFunctor φ ⋙ tensorCompFunctor P ⟶ tensorCompFunctor P')
    (Z : HomotopyCategory A') :
    (derivedTensorRestrictTransQuotient φ P P' τ).app Z =
      (derivedTensorFunctor P).map ((derivedRestrictionFactorization φ).hom.app Z) ≫
        (derivedTensorFunctorCounit P).app ((restrictScalarsHomotopyFunctor φ).obj Z) ≫
          (quasiIsomorphisms' B).Q.map ((restrictTensorHomotopyTrans φ P P' τ).app Z) :=
  rfl

/-- **The comparison of the derived tensor functors is pinned by that property.** Any natural
transformation of the derived tensor functors whose composite with the comparison of Tag 0BZ2
for `P'` is the one above is `DifferentialGraded.Bimodule.derivedTensorRestrictTrans`. A
comparison built by some other route — an adjunction, say — is therefore covered by the results
below as soon as it satisfies this one identity. -/
theorem derivedTensorRestrictTrans_unique (φ : A.Hom A') (P : Bimodule A B) (P' : Bimodule A' B)
    (τ : restrictScalarsFunctor φ ⋙ tensorCompFunctor P ⟶ tensorCompFunctor P')
    (c : derivedRestriction φ ⋙ derivedTensorFunctor P ⟶ derivedTensorFunctor P')
    (hc : ∀ Z : HomotopyCategory A',
      c.app ((quasiIsomorphisms' A').Q.obj Z) ≫ (derivedTensorFunctorCounit P').app Z =
        (derivedTensorRestrictTransQuotient φ P P' τ).app Z) :
    c = derivedTensorRestrictTrans φ P P' τ := by
  refine Functor.leftDerived_ext (derivedTensorFunctor P') (derivedTensorFunctorCounit P')
    (quasiIsomorphisms' A') (derivedRestriction φ ⋙ derivedTensorFunctor P) c
    (derivedTensorRestrictTrans φ P P' τ) ?_
  ext Z
  exact (hc Z).trans (derivedTensorRestrictTrans_app_comp_counit φ P P' τ Z).symm

/-! ### The transition map of a derived tensor tower is the plain one -/

/-- **The transition map of a derived tensor tower is the plain one.** Let `φ : A ⟶ A'` be a
homomorphism of differential graded algebras, let `P` be a differential graded `(A, B)`-bimodule,
`P'` a differential graded `(A', B)`-bimodule and `τ` a comparison of the plain tensor functors.
Let `v : X ⟶ X'|_A` be a homomorphism from a differential graded `A`-module to the restriction of
a differential graded `A'`-module, and let `w` be the map it gives in the derived category of `A`
(`DifferentialGradedModule.derivedTrans`). If `X` and `X'` are orthogonal on the left to the
acyclic modules, so that `DifferentialGraded.Bimodule.derivedTensorObjIsoPlain` identifies both
derived tensor products with the plain ones, then the derived tensor product of `w` followed by
the comparison `DifferentialGraded.Bimodule.derivedTensorRestrictTrans` of the derived functors
is, under those identifications, the plain homomorphism
`P ⊗_A X ⟶ P ⊗_A X'|_A ⟶ P' ⊗_{A'} X'`.

This is the naturality that an isomorphism of objects of `D(B, d)` does not provide: it identifies
the transition map of a tower `n ↦ P_n ⊗_{A_n}^𝐋 X_n` of `D(B, d)` with a homomorphism of
differential graded `B`-modules. -/
theorem derivedTensorRestrictTrans_towerMap (φ : A.Hom A') (P : Bimodule A B)
    (P' : Bimodule A' B)
    (τ : restrictScalarsFunctor φ ⋙ tensorCompFunctor P ⟶ tensorCompFunctor P')
    {X : DifferentialGradedModule.{u, u, u} A} {X' : DifferentialGradedModule.{u, u, u} A'}
    (v : X ⟶ restrictScalars φ X')
    (w : (quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj X) ⟶
      (derivedRestriction φ).obj
        ((quasiIsomorphisms' A').Q.obj ((toHomotopyCategory A').obj X')))
    (hw : w = (quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map v) ≫
      (derivedRestrictionFactorization φ).inv.app ((toHomotopyCategory A').obj X'))
    (hX : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj X))
    (hX' : (acyclic' A').leftOrthogonal ((toHomotopyCategory A').obj X')) :
    ((derivedTensorFunctor P).map w ≫
          (derivedTensorRestrictTrans φ P P' τ).app
            ((quasiIsomorphisms' A').Q.obj ((toHomotopyCategory A').obj X'))) ≫
        (derivedTensorObjIsoPlain P' X' hX').hom =
      (derivedTensorObjIsoPlain P X hX).hom ≫
        (quasiIsomorphisms' B).Q.map
          ((toHomotopyCategory B).map ((tensorCompFunctor P).map v ≫ τ.app X')) := by
  subst hw
  have hb : (derivedRestrictionFactorization φ).inv.app ((toHomotopyCategory A').obj X') ≫
      (derivedRestrictionFactorization φ).hom.app ((toHomotopyCategory A').obj X') =
        𝟙 ((quasiIsomorphisms' A).Q.obj
          ((restrictScalarsHomotopyFunctor φ).obj ((toHomotopyCategory A').obj X'))) :=
    (derivedRestrictionFactorization φ).inv_hom_id_app _
  have hc : (derivedTensorRestrictTrans φ P P' τ).app
          ((quasiIsomorphisms' A').Q.obj ((toHomotopyCategory A').obj X')) ≫
        (derivedTensorFunctorCounit P').app ((toHomotopyCategory A').obj X') =
      (derivedTensorFunctor P).map
          ((derivedRestrictionFactorization φ).hom.app ((toHomotopyCategory A').obj X')) ≫
        (derivedTensorFunctorCounit P).app
            ((restrictScalarsHomotopyFunctor φ).obj ((toHomotopyCategory A').obj X')) ≫
          (quasiIsomorphisms' B).Q.map
            ((restrictTensorHomotopyTrans φ P P' τ).app ((toHomotopyCategory A').obj X')) :=
    (derivedTensorRestrictTrans_app_comp_counit φ P P' τ
      ((toHomotopyCategory A').obj X')).trans
      (derivedTensorRestrictTransQuotient_app φ P P' τ ((toHomotopyCategory A').obj X'))
  have hk : (tensorCompFunctor_quotient P').hom.app X' ≫
      (tensorCompFunctor_quotient P').inv.app X' =
        𝟙 ((toHomotopyCategory B).obj ((tensorCompFunctor P').obj X')) :=
    (tensorCompFunctor_quotient P').hom_inv_id_app X'
  have hg : (toHomotopyCategory B).map ((tensorCompFunctor P).map v) ≫
      (toHomotopyCategory B).map (τ.app X') =
        (toHomotopyCategory B).map ((tensorCompFunctor P).map v ≫ τ.app X') :=
    ((toHomotopyCategory B).map_comp _ _).symm
  rw [derivedTensorObjIsoPlain_hom, derivedTensorObjIsoPlain_hom]
  exact towerMap_aux (derivedTensorFunctor P) (quasiIsomorphisms' B).Q _ _ _ hb
    _ _ _ _ _ _ _ _ _ _ _ _ hc (restrictTensorHomotopyTrans_app φ P P' τ X') hk
    (localizedComparison_naturality_aux (derivedTensorFunctorCounit P)
      (tensorCompFunctor_quotient P) v) hg

/-! ### The naturality square -/

/-- The isomorphism of two derived tensor products coming from an isomorphism of the plain ones
is the two identifications with the plain tensor products with the isomorphism between them. -/
theorem derivedTensorObjIsoOfTensorIso_hom (N : Bimodule A B) (N' : Bimodule A' B)
    (X : DifferentialGradedModule.{u, u, u} A) (X' : DifferentialGradedModule.{u, u, u} A')
    (hX : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj X))
    (hX' : (acyclic' A').leftOrthogonal ((toHomotopyCategory A').obj X'))
    (e : tensorObj N X ≅ tensorObj N' X') :
    (derivedTensorObjIsoOfTensorIso N N' X X' hX hX' e).hom =
      (derivedTensorObjIsoPlain N X hX).hom ≫
        (quasiIsomorphisms' B).Q.map ((toHomotopyCategory B).map e.hom) ≫
          (derivedTensorObjIsoPlain N' X' hX').inv :=
  rfl

/-- **The naturality square.** Two derived tensor towers, one over `φ₁ : A₁ ⟶ A₁'` with the
bimodules `P₁`, `P₁'` and the modules `X₁`, `X₁'`, the other over `φ₂ : A₂ ⟶ A₂'` with `P₂`,
`P₂'`, `X₂`, `X₂'`, all four modules orthogonal on the left to the acyclic modules. Suppose their
*plain* transition maps `P₁ ⊗_{A₁} X₁ ⟶ P₁' ⊗_{A₁'} X₁'` and `P₂ ⊗_{A₂} X₂ ⟶ P₂' ⊗_{A₂'} X₂'`
and two isomorphisms `e`, `e'` of the plain tensor products form a commuting square of
homomorphisms of differential graded `B`-modules. Then the isomorphisms
`DifferentialGraded.Bimodule.derivedTensorObjIsoOfTensorIso` that `e` and `e'` induce in
`D(B, d)` form a commuting square with the two derived transition maps.

This is the compatibility with the transition maps of an inverse system that
`DifferentialGraded.Bimodule.derivedTensorObjIsoOfTensorIso` does not carry on its own: it is
deduced here, from a square of homomorphisms of differential graded modules, rather than
assumed. -/
theorem derivedTensorObjIsoOfTensorIso_naturality
    {A₁ A₁' A₂ A₂' : DifferentialGradedAlgebra.{u, u} R}
    (φ₁ : A₁.Hom A₁') (φ₂ : A₂.Hom A₂')
    (P₁ : Bimodule A₁ B) (P₁' : Bimodule A₁' B) (P₂ : Bimodule A₂ B) (P₂' : Bimodule A₂' B)
    (τ₁ : restrictScalarsFunctor φ₁ ⋙ tensorCompFunctor P₁ ⟶ tensorCompFunctor P₁')
    (τ₂ : restrictScalarsFunctor φ₂ ⋙ tensorCompFunctor P₂ ⟶ tensorCompFunctor P₂')
    {X₁ : DifferentialGradedModule.{u, u, u} A₁} {X₁' : DifferentialGradedModule.{u, u, u} A₁'}
    {X₂ : DifferentialGradedModule.{u, u, u} A₂} {X₂' : DifferentialGradedModule.{u, u, u} A₂'}
    (v₁ : X₁ ⟶ restrictScalars φ₁ X₁') (v₂ : X₂ ⟶ restrictScalars φ₂ X₂')
    (w₁ : (quasiIsomorphisms' A₁).Q.obj ((toHomotopyCategory A₁).obj X₁) ⟶
      (derivedRestriction φ₁).obj
        ((quasiIsomorphisms' A₁').Q.obj ((toHomotopyCategory A₁').obj X₁')))
    (hw₁ : w₁ = (quasiIsomorphisms' A₁).Q.map ((toHomotopyCategory A₁).map v₁) ≫
      (derivedRestrictionFactorization φ₁).inv.app ((toHomotopyCategory A₁').obj X₁'))
    (w₂ : (quasiIsomorphisms' A₂).Q.obj ((toHomotopyCategory A₂).obj X₂) ⟶
      (derivedRestriction φ₂).obj
        ((quasiIsomorphisms' A₂').Q.obj ((toHomotopyCategory A₂').obj X₂')))
    (hw₂ : w₂ = (quasiIsomorphisms' A₂).Q.map ((toHomotopyCategory A₂).map v₂) ≫
      (derivedRestrictionFactorization φ₂).inv.app ((toHomotopyCategory A₂').obj X₂'))
    (hX₁ : (acyclic' A₁).leftOrthogonal ((toHomotopyCategory A₁).obj X₁))
    (hX₁' : (acyclic' A₁').leftOrthogonal ((toHomotopyCategory A₁').obj X₁'))
    (hX₂ : (acyclic' A₂).leftOrthogonal ((toHomotopyCategory A₂).obj X₂))
    (hX₂' : (acyclic' A₂').leftOrthogonal ((toHomotopyCategory A₂').obj X₂'))
    (e : tensorObj P₁ X₁ ≅ tensorObj P₂ X₂)
    (e' : tensorObj P₁' X₁' ≅ tensorObj P₂' X₂')
    (hsq : ((tensorCompFunctor P₁).map v₁ ≫ τ₁.app X₁') ≫ e'.hom =
      e.hom ≫ ((tensorCompFunctor P₂).map v₂ ≫ τ₂.app X₂')) :
    ((derivedTensorFunctor P₁).map w₁ ≫
          (derivedTensorRestrictTrans φ₁ P₁ P₁' τ₁).app
            ((quasiIsomorphisms' A₁').Q.obj ((toHomotopyCategory A₁').obj X₁'))) ≫
        (derivedTensorObjIsoOfTensorIso P₁' P₂' X₁' X₂' hX₁' hX₂' e').hom =
      (derivedTensorObjIsoOfTensorIso P₁ P₂ X₁ X₂ hX₁ hX₂ e).hom ≫
        ((derivedTensorFunctor P₂).map w₂ ≫
          (derivedTensorRestrictTrans φ₂ P₂ P₂' τ₂).app
            ((quasiIsomorphisms' A₂').Q.obj ((toHomotopyCategory A₂').obj X₂'))) := by
  rw [derivedTensorObjIsoOfTensorIso_hom, derivedTensorObjIsoOfTensorIso_hom]
  exact towerSquare_aux (toHomotopyCategory B) (quasiIsomorphisms' B).Q _ _ _ _ _ _ _ _ _ _
    (derivedTensorRestrictTrans_towerMap φ₁ P₁ P₁' τ₁ v₁ w₁ hw₁ hX₁ hX₁')
    (derivedTensorRestrictTrans_towerMap φ₂ P₂ P₂' τ₂ v₂ w₂ hw₂ hX₂ hX₂') hsq

end DifferentialGraded.Bimodule

end
