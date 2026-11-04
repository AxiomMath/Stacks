module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.HomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc

/-!
# The canonical descent datum and descent functor of an étale family

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be a family of
algebraic spaces *étale* over `X`, for instance a Zariski covering.  The canonical descent datum
`(M|_{Y i}, can)` of Stacks 04W5 of a quasi-coherent `𝒪_X`-module `M`, and the functor it defines
from the quasi-coherent `𝒪_X`-modules of Stacks 03G9 to the descent data of Stacks 04W3, are
built here with no further input: the associativity coherence of the comparison of inverse
images of Stacks 03LU is `AlgebraicGeometry.Space.modulePullbackCompIsoAssoc`, and along an étale
morphism the inverse image of a quasi-coherent module is quasi-coherent by Stacks 03GA.
Consequently the faithfulness half of Stacks 04W6 holds for an étale covering of an algebraic
space with no hypothesis beyond the covering.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleCanonicalDescentDatum` is the canonical
  descent datum of a quasi-coherent module relative to a family of étale morphisms, and
  `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleCanonicalDescentFunctor` the functor it
  defines.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.IsEtaleEffective` says that a descent datum
  relative to a family of étale morphisms is isomorphic to the canonical descent datum of a
  quasi-coherent module on the target.

## Main results

* `faithful_etaleCanonicalDescentFunctor_of_isEtaleCovering` and
  `faithful_etaleCanonicalDescentFunctor_of_isZariskiCovering`, in the namespace
  `AlgebraicGeometry.Space.QuasiCoherentDescent`: **the canonical descent functor of an étale
  covering of an algebraic space is faithful**, the faithfulness half of Stacks 04W6.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleCanonicalDescentDatum_eq`,
  `.etaleCanonicalDescentHom_eq` and `.etaleCanonicalDescentFunctor_obj_eq`: for a family of
  étale morphisms admitting local presentations of inverse images the datum, the induced
  morphisms and the values of the functor agree with those of
  `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatum` and
  `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentFunctor`, so every statement
  about the latter applies.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEtaleEffective_iff_essImage`: a descent datum
  relative to an étale family is effective exactly when it lies in the essential image of the
  functor.

## Implementation notes

Quasi-coherence of the component modules is the only place étaleness of the family enters; the
pairwise isomorphism and the cocycle condition are those of
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatum`, with the associativity
coherence of Stacks 03LU supplied.

Every morphism and every functor law is proved for a module together with a proof of its
quasi-coherence as separate arguments, and the family of component morphisms of
`AlgebraicGeometry.Space.QuasiCoherentDescent.etaleCanonicalDescentDatum_naturality` is a
parameter pinned by a hypothesis rather than written out, so that the statement is the
compatibility field of `AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.Hom` on the
nose; both arrangements keep the kernel from reducing through the descent datum.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-! ### The canonical descent datum of an étale family -/

/-- The canonical descent datum `(M|_{Y i}, can)` of a quasi-coherent `𝒪_X`-module `M` relative
to a family `(f i : Y i ⟶ X)` of algebraic spaces étale over `X`: the inverse images `(f i)^*M`,
quasi-coherent by Stacks 03GA, with the canonical comparison of the two inverse images of `M` on
each pairwise fibre product. -/
def etaleCanonicalDescentDatum (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) : DescentDatum B S hS Yi f where
  F i := (modulePullback B S hS (f i)).obj M
  quasicoherent i :=
    isQuasicoherentOnSite_modulePullback_of_isEtale B S hS (f i) (hf i) M hM
  transition i j := canonicalComparison (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j)
    (f i) (f j) (pair_condition B S hS Yi f i j) M
  cocycle i j k T vi vj vk vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁ := by
    rw [transitionOn_canonicalComparison B S hS Yi f M
        i j vij vi vj hij₀ hij₁,
      transitionOn_canonicalComparison B S hS Yi f M
        j k vjk vj vk hjk₀ hjk₁,
      transitionOn_canonicalComparison B S hS Yi f M
        i k vik vi vk hik₀ hik₁]
    exact canonicalComparison_trans B S hS vi vj vk (f i) (f j) (f k) _ _ M

/-- The `i`-th component module of the canonical descent datum of an étale family is the inverse
image of `M` along `f i`. -/
@[simp]
theorem etaleCanonicalDescentDatum_F (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (i : I) :
    (etaleCanonicalDescentDatum B S hS Yi f hf M hM).F i =
      (modulePullback B S hS (f i)).obj M :=
  rfl

/-- The pairwise isomorphism of the canonical descent datum of an étale family is the canonical
comparison of the two inverse images of `M` to the pairwise fibre product. -/
@[simp]
theorem etaleCanonicalDescentDatum_transition (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (i j : I) :
    (etaleCanonicalDescentDatum B S hS Yi f hf M hM).transition i j =
      canonicalComparison (pairFst B S hS Yi f i j) (pairSnd B S hS Yi f i j) (f i) (f j)
        (pair_condition B S hS Yi f i j) M :=
  rfl

/-- The canonical descent datum of an étale family is the canonical descent datum of
Stacks 04W5. -/
theorem etaleCanonicalDescentDatum_eq
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) :
    etaleCanonicalDescentDatum B S hS Yi f hf M hM =
      canonicalDescentDatum B S hS Yi f M hM :=
  rfl

/-! ### Morphisms and the descent functor -/

/-- A family of morphisms of the component modules of two canonical descent data of an étale
family which is the family of inverse images of one morphism `φ` of quasi-coherent `𝒪_X`-modules
commutes with the pairwise isomorphisms of those data. -/
theorem etaleCanonicalDescentDatum_naturality (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N)
    (a : ∀ i, (etaleCanonicalDescentDatum B S hS Yi f hf M hM).F i ⟶
      (etaleCanonicalDescentDatum B S hS Yi f hf N hN).F i)
    (ha : ∀ i, a i = (modulePullback B S hS (f i)).map φ) (i j : I) :
    (modulePullback B S hS (pairFst B S hS Yi f i j)).map (a i) ≫
        ((etaleCanonicalDescentDatum B S hS Yi f hf N hN).transition i j).hom =
      ((etaleCanonicalDescentDatum B S hS Yi f hf M hM).transition i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS Yi f i j)).map (a j) := by
  rw [ha i, ha j, etaleCanonicalDescentDatum_transition, etaleCanonicalDescentDatum_transition]
  exact canonicalComparison_naturality B S hS (pairFst B S hS Yi f i j)
    (pairSnd B S hS Yi f i j) (f i) (f j) (pair_condition B S hS Yi f i j) φ

/-- The morphism of canonical descent data of an étale family induced by a morphism of
quasi-coherent `𝒪_X`-modules: the inverse image of that morphism along each member of the
family. -/
def etaleCanonicalDescentHom (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) :
    etaleCanonicalDescentDatum B S hS Yi f hf M hM ⟶
      etaleCanonicalDescentDatum B S hS Yi f hf N hN :=
  DescentDatum.Hom.mk (fun i => (modulePullback B S hS (f i)).map φ)
    (etaleCanonicalDescentDatum_naturality B S hS Yi f hf M N hM hN φ
      (fun i => (modulePullback B S hS (f i)).map φ) (fun _ => rfl))

/-- The `i`-th component of the morphism of canonical descent data of an étale family induced by
a morphism of quasi-coherent modules is the inverse image of that morphism along `f i`. -/
@[simp]
theorem etaleCanonicalDescentHom_app (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) (i : I) :
    (etaleCanonicalDescentHom B S hS Yi f hf M N hM hN φ).app i =
      (modulePullback B S hS (f i)).map φ :=
  rfl

/-- The morphism of canonical descent data of an étale family induced by an identity is an
identity. -/
theorem etaleCanonicalDescentHom_id (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) :
    etaleCanonicalDescentHom B S hS Yi f hf M M hM hM (𝟙 M) =
      𝟙 (etaleCanonicalDescentDatum B S hS Yi f hf M hM) :=
  DescentDatum.Hom.ext fun i => (modulePullback B S hS (f i)).map_id M

/-- The morphism of canonical descent data of an étale family induced by a composite is the
composite of the induced morphisms. -/
theorem etaleCanonicalDescentHom_comp (M N P : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (hP : P.IsQuasicoherentOnSite) (φ : M ⟶ N) (ψ : N ⟶ P) :
    etaleCanonicalDescentHom B S hS Yi f hf M P hM hP (φ ≫ ψ) =
      etaleCanonicalDescentHom B S hS Yi f hf M N hM hN φ ≫
        etaleCanonicalDescentHom B S hS Yi f hf N P hN hP ψ :=
  DescentDatum.Hom.ext fun i => (modulePullback B S hS (f i)).map_comp φ ψ

/-- The morphism of canonical descent data of an étale family induced by a morphism of
quasi-coherent modules is the one induced by it in Stacks 04W5. -/
theorem etaleCanonicalDescentHom_eq
    (M N : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) :
    etaleCanonicalDescentHom B S hS Yi f hf M N hM hN φ =
      canonicalDescentHom B S hS Yi f M N hM hN φ :=
  rfl

/-- The canonical descent functor of a family `(f i : Y i ⟶ X)` of algebraic spaces étale over
`X`: it sends a quasi-coherent `𝒪_X`-module to its canonical descent datum `(M|_{Y i}, can)` of
Stacks 04W5, and a morphism of modules to its inverse images along the members of the family. -/
def etaleCanonicalDescentFunctor :
    QuasicoherentSheaves.{u, u} B S hS X.1 X.2 ⥤ DescentDatum B S hS Yi f where
  obj M := etaleCanonicalDescentDatum B S hS Yi f hf M.obj M.property
  map {M N} φ :=
    etaleCanonicalDescentHom B S hS Yi f hf M.obj N.obj M.property N.property φ.hom
  map_id M := etaleCanonicalDescentHom_id B S hS Yi f hf M.obj M.property
  map_comp {M N P} φ ψ :=
    etaleCanonicalDescentHom_comp B S hS Yi f hf M.obj N.obj P.obj M.property N.property
      P.property φ.hom ψ.hom

/-- The canonical descent functor of an étale family sends a quasi-coherent module to its
canonical descent datum. -/
@[simp]
theorem etaleCanonicalDescentFunctor_obj (M : QuasicoherentSheaves.{u, u} B S hS X.1 X.2) :
    (etaleCanonicalDescentFunctor B S hS Yi f hf).obj M =
      etaleCanonicalDescentDatum B S hS Yi f hf M.obj M.property :=
  rfl

/-- The image of a morphism of quasi-coherent modules under the canonical descent functor of an
étale family is the morphism of canonical descent data it induces. -/
theorem etaleCanonicalDescentFunctor_map {M N : QuasicoherentSheaves.{u, u} B S hS X.1 X.2}
    (φ : M ⟶ N) :
    (etaleCanonicalDescentFunctor B S hS Yi f hf).map φ =
      etaleCanonicalDescentHom B S hS Yi f hf M.obj N.obj M.property N.property φ.hom :=
  rfl

/-- The `i`-th component of the image of a morphism of quasi-coherent modules under the canonical
descent functor of an étale family. -/
@[simp]
theorem etaleCanonicalDescentFunctor_map_app
    {M N : QuasicoherentSheaves.{u, u} B S hS X.1 X.2} (φ : M ⟶ N) (i : I) :
    ((etaleCanonicalDescentFunctor B S hS Yi f hf).map φ).app i =
      (modulePullback B S hS (f i)).map φ.hom :=
  etaleCanonicalDescentHom_app B S hS Yi f hf M.obj N.obj M.property N.property φ.hom i

/-- The canonical descent functor of an étale family agrees on objects with the canonical
descent functor of Stacks 04W5. -/
theorem etaleCanonicalDescentFunctor_obj_eq
    (M : QuasicoherentSheaves.{u, u} B S hS X.1 X.2) :
    (etaleCanonicalDescentFunctor B S hS Yi f hf).obj M =
      (canonicalDescentFunctor B S hS Yi f).obj M :=
  etaleCanonicalDescentDatum_eq B S hS Yi f hf M.obj M.property

/-! ### Effective descent data -/

/-- A descent datum for quasi-coherent modules relative to a family of algebraic spaces étale
over `X` is effective when it is isomorphic to the canonical descent datum of a quasi-coherent
`𝒪_X`-module. -/
def IsEtaleEffective (D : DescentDatum B S hS Yi f) : Prop :=
  ∃ (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite),
    Nonempty (D ≅ etaleCanonicalDescentDatum B S hS Yi f hf M hM)

/-- A canonical descent datum of an étale family is effective. -/
theorem isEtaleEffective_etaleCanonicalDescentDatum (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) :
    IsEtaleEffective B S hS Yi f hf (etaleCanonicalDescentDatum B S hS Yi f hf M hM) :=
  ⟨M, hM, ⟨Iso.refl _⟩⟩

/-- Effectivity relative to the étale family is the effectivity of Stacks 04W5. -/
theorem isEtaleEffective_iff_isEffective
    (D : DescentDatum B S hS Yi f) :
    IsEtaleEffective B S hS Yi f hf D ↔
      IsEffective B S hS Yi f D :=
  Iff.rfl

/-- **The effective descent data of an étale family are the essential image of its canonical
descent functor.** -/
theorem isEtaleEffective_iff_essImage (D : DescentDatum B S hS Yi f) :
    IsEtaleEffective B S hS Yi f hf D ↔
      (etaleCanonicalDescentFunctor B S hS Yi f hf).essImage D := by
  constructor
  · rintro ⟨M, hM, ⟨e⟩⟩
    exact ⟨⟨M, hM⟩, ⟨e.symm⟩⟩
  · rintro ⟨M, ⟨e⟩⟩
    exact ⟨M.obj, M.property, ⟨e.symm⟩⟩

/-! ### Faithfulness -/

/-- **The canonical descent functor of an étale covering of an algebraic space is faithful.**
This is the faithfulness half of Stacks 04W6, with no hypothesis beyond the covering: a morphism
of `𝒪_X`-modules is determined by its inverse images along an étale covering. -/
theorem faithful_etaleCanonicalDescentFunctor_of_isEtaleCovering
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (f i).hom)) :
    (etaleCanonicalDescentFunctor B S hS Yi f hf).Faithful where
  map_injective {M N} φ ψ h := by
    refine ObjectProperty.hom_ext _ (modulePullback_map_injective_of_isEtaleCovering B S hS Yi f
      hcov φ.hom ψ.hom fun i => ?_)
    have hi := congrArg
      (fun a : (etaleCanonicalDescentFunctor B S hS Yi f hf).obj M ⟶
        (etaleCanonicalDescentFunctor B S hS Yi f hf).obj N => a.app i) h
    rw [etaleCanonicalDescentFunctor_map_app, etaleCanonicalDescentFunctor_map_app] at hi
    exact hi

/-- **The canonical descent functor of a Zariski covering of an algebraic space is faithful**, a
Zariski covering being an étale covering by Stacks 0DF1. -/
theorem faithful_etaleCanonicalDescentFunctor_of_isZariskiCovering
    (hcov : IsZariskiCovering B S hS I (fun i => (Yi i).1) (fun i => (f i).hom)) :
    (etaleCanonicalDescentFunctor B S hS Yi f hf).Faithful :=
  faithful_etaleCanonicalDescentFunctor_of_isEtaleCovering B S hS Yi f hf
    (isEtaleCovering_of_isZariskiCovering B S hS X.2 (fun i => (Yi i).2) hcov)

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
