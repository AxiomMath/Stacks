module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.CanonicalDatum

/-!
# The canonical descent functor of a quasi-coherent module

Let `X` be an algebraic space over `S` and let `(f i : Y i ⟶ X)` be a family of algebraic
spaces over it.  Stacks 04W5 attaches to a quasi-coherent `𝒪_X`-module `M` its canonical
descent datum `(M|_{Y i}, can)` relative to the family,
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatum`.  This file makes that
assignment a *functor* from the quasi-coherent `𝒪_X`-modules of Stacks 03G9 to the descent
data of Stacks 04W3, and identifies the effective descent data of Stacks 04W5 as its
essential image.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparisonIso` is the canonical
  comparison of two inverse images as a natural isomorphism of functors, rather than one
  isomorphism for each module.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentHom` is the morphism of
  canonical descent data induced by a morphism of quasi-coherent modules, and
  `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentFunctor` the resulting functor
  from the quasi-coherent `𝒪_X`-modules to the descent data for the family.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_naturality`: the canonical
  comparison of the two inverse images of a module is natural in the module.  This is what
  makes the inverse images of a morphism of modules a morphism of the canonical descent data.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEffective_iff_essImage`: a descent datum is
  effective exactly when it lies in the essential image of the canonical descent functor.

## Implementation notes

Everything here is unconditional, as
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatum` is.  The value of the
functor on an object needs the associativity coherence of the comparison of inverse images of
Stacks 03LU and the quasi-coherence of the inverse images (Stacks 03GA), both through that
definition.

The value of the functor on a *morphism* needs neither.  Naturality of the pairwise
isomorphism in the module is naturality of the comparison of iterated inverse images of
Stacks 03LU, which is a field of `AlgebraicGeometry.Space.modulePullbackCompIso`; that is why
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparisonIso` is built as a natural
isomorphism of functors, so that its naturality is the naturality field of a natural
transformation rather than a statement needing proof, and the cocycle-level coherence that the
object part needs does not enter.

Two shapes of the kernel are worked around below, and the arrangement of the file is what
avoids them.

The first: every morphism and every functor law is proved for a *module together with a proof
of its quasi-coherence as separate arguments*, and only then instantiated at the two
projections `M.obj`, `M.property` of an object of
`AlgebraicGeometry.Space.QuasicoherentSheaves`.  Stating them at the projections instead —
with the full subcategory's object as the only variable — makes the kernel reduce through
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalDescentDatum` with the projections
inside, and it does not finish: even forming a morphism of descent data out of its two fields,
with both fields hypotheses of exactly the right type, then exceeds the kernel's budget, while
the same morphism formed with the module as a plain variable is checked at once.
Instantiating a declaration proved that way at the projections is free, because no reduction
is left to do.

The second: every proof that could have been written inside a structure instance or a functor
literal is instead a standalone declaration with an explicit type —
`canonicalDescentDatum_naturality` for the compatibility field of a morphism of descent data,
`canonicalDescentHom_id` and `canonicalDescentHom_comp` for the two functor laws, and
`CategoryTheory.Iso.trans_eqToIso_symm_app` for the comparison read at a module.  In
`canonicalDescentDatum_naturality` the family of component morphisms is a parameter, pinned to
the inverse images of one morphism by a hypothesis, rather than written out: the statement is
then the compatibility field of
`AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.Hom` on the nose, so instantiating
it at that field asks the kernel for no reduction at all.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Iso

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A composite of an isomorphism of functors, a transport along an equality of functors and
the inverse of an isomorphism of functors, read at an object: the composite of the three
isomorphisms read at that object. -/
theorem trans_eqToIso_symm_app {F G H K : C ⥤ D} (e₁ : F ≅ G) (h : G = H) (e₂ : K ≅ H) (M : C) :
    (e₁ ≪≫ eqToIso h ≪≫ e₂.symm).app M =
      e₁.app M ≪≫ eqToIso (congrArg (fun T : C ⥤ D => T.obj M) h) ≪≫ (e₂.app M).symm := by
  subst h
  apply Iso.ext
  simp

end CategoryTheory.Iso

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS}

/-- The canonical comparison of the two inverse images of a module along two morphisms with
equal composites to its base, as a natural isomorphism of the two functors rather than one
isomorphism for each module. -/
def canonicalComparisonIso {A P Q R : AlgebraicSpaces B S hS} (a : P ⟶ Q) (b : P ⟶ R)
    (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj) :
    modulePullback B S hS fi ⋙ modulePullback B S hS a ≅
      modulePullback B S hS fj ⋙ modulePullback B S hS b :=
  modulePullbackCompIso B S hS a fi ≪≫
    eqToIso (congrArg (modulePullback B S hS) h) ≪≫
    (modulePullbackCompIso B S hS b fj).symm

/-- At a module, the natural isomorphism of
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparisonIso` is the canonical
comparison of the two inverse images of that module. -/
theorem canonicalComparisonIso_app {A P Q R : AlgebraicSpaces B S hS} (a : P ⟶ Q) (b : P ⟶ R)
    (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj)
    (M : Modules.{u, u} B S hS A.1 A.2) :
    (canonicalComparisonIso B S hS a b fi fj h).app M = canonicalComparison a b fi fj h M := by
  rw [canonicalComparison_eq]
  exact Iso.trans_eqToIso_symm_app (modulePullbackCompIso B S hS a fi)
    (congrArg (modulePullback B S hS) h) (modulePullbackCompIso B S hS b fj) M

/-- The canonical comparison of the two inverse images of a module is natural in the module. -/
theorem canonicalComparison_naturality {A P Q R : AlgebraicSpaces B S hS} (a : P ⟶ Q)
    (b : P ⟶ R) (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj)
    {M N : Modules.{u, u} B S hS A.1 A.2} (φ : M ⟶ N) :
    (modulePullback B S hS a).map ((modulePullback B S hS fi).map φ) ≫
        (canonicalComparison a b fi fj h N).hom =
      (canonicalComparison a b fi fj h M).hom ≫
        (modulePullback B S hS b).map ((modulePullback B S hS fj).map φ) := by
  rw [← canonicalComparisonIso_app B S hS a b fi fj h M,
    ← canonicalComparisonIso_app B S hS a b fi fj h N]
  exact (canonicalComparisonIso B S hS a b fi fj h).hom.naturality φ

variable (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)

/-- A family of morphisms of the component modules of two canonical descent data which is the
family of inverse images of one morphism `φ` of quasi-coherent `𝒪_X`-modules commutes with the
pairwise isomorphisms of those data.

The family is a parameter, pinned to the inverse images of `φ` by a hypothesis rather than
written out, so that the statement is the compatibility field of
`AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.Hom` on the nose: the two descent
data enter only through their projections, exactly as they do in that field. -/
theorem canonicalDescentDatum_naturality (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N)
    (a : ∀ i, (canonicalDescentDatum B S hS Y f M hM).F i ⟶
      (canonicalDescentDatum B S hS Y f N hN).F i)
    (ha : ∀ i, a i = (modulePullback B S hS (f i)).map φ) (i j : I) :
    (modulePullback B S hS (pairFst B S hS Y f i j)).map (a i) ≫
        ((canonicalDescentDatum B S hS Y f N hN).transition i j).hom =
      ((canonicalDescentDatum B S hS Y f M hM).transition i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS Y f i j)).map (a j) := by
  rw [ha i, ha j, canonicalDescentDatum_transition, canonicalDescentDatum_transition]
  exact canonicalComparison_naturality B S hS (pairFst B S hS Y f i j)
    (pairSnd B S hS Y f i j) (f i) (f j) (pair_condition B S hS Y f i j) φ

/-- The morphism of canonical descent data induced by a morphism of quasi-coherent
`𝒪_X`-modules: the inverse image of that morphism along each member of the family. -/
def canonicalDescentHom (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) :
    canonicalDescentDatum B S hS Y f M hM ⟶
      canonicalDescentDatum B S hS Y f N hN :=
  DescentDatum.Hom.mk (fun i => (modulePullback B S hS (f i)).map φ)
    (canonicalDescentDatum_naturality B S hS Y f M N hM hN φ
      (fun i => (modulePullback B S hS (f i)).map φ) (fun _ => rfl))

/-- The `i`-th component of the morphism of canonical descent data induced by a morphism of
quasi-coherent modules is the inverse image of that morphism along the `i`-th member of the
family. -/
@[simp]
theorem canonicalDescentHom_app (M N : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) (i : I) :
    (canonicalDescentHom B S hS Y f M N hM hN φ).app i =
      (modulePullback B S hS (f i)).map φ :=
  rfl

/-- The morphism of canonical descent data induced by an identity is an identity. -/
theorem canonicalDescentHom_id (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) :
    canonicalDescentHom B S hS Y f M M hM hM (𝟙 M) =
      𝟙 (canonicalDescentDatum B S hS Y f M hM) :=
  DescentDatum.Hom.ext fun i => (modulePullback B S hS (f i)).map_id M

/-- The morphism of canonical descent data induced by a composite is the composite of the
induced morphisms. -/
theorem canonicalDescentHom_comp (M N P : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (hP : P.IsQuasicoherentOnSite) (φ : M ⟶ N) (ψ : N ⟶ P) :
    canonicalDescentHom B S hS Y f M P hM hP (φ ≫ ψ) =
      canonicalDescentHom B S hS Y f M N hM hN φ ≫
        canonicalDescentHom B S hS Y f N P hN hP ψ :=
  DescentDatum.Hom.ext fun i => (modulePullback B S hS (f i)).map_comp φ ψ

/-- The canonical descent functor of a family `(f i : Y i ⟶ X)` of algebraic spaces over `X`:
it sends a quasi-coherent `𝒪_X`-module to its canonical descent datum `(M|_{Y i}, can)` of
Stacks 04W5, and a morphism of modules to its inverse images along the members of the
family. -/
def canonicalDescentFunctor :
    QuasicoherentSheaves.{u, u} B S hS X.1 X.2 ⥤ DescentDatum B S hS Y f where
  obj M := canonicalDescentDatum B S hS Y f M.obj M.property
  map {M N} φ :=
    canonicalDescentHom B S hS Y f M.obj N.obj M.property N.property φ.hom
  map_id M := canonicalDescentHom_id B S hS Y f M.obj M.property
  map_comp {M N P} φ ψ :=
    canonicalDescentHom_comp B S hS Y f M.obj N.obj P.obj M.property N.property
      P.property φ.hom ψ.hom

/-- The canonical descent functor sends a quasi-coherent module to its canonical descent
datum. -/
@[simp]
theorem canonicalDescentFunctor_obj (M : QuasicoherentSheaves.{u, u} B S hS X.1 X.2) :
    (canonicalDescentFunctor B S hS Y f).obj M =
      canonicalDescentDatum B S hS Y f M.obj M.property :=
  rfl

/-- The image of a morphism of quasi-coherent modules under the canonical descent functor is
the morphism of canonical descent data it induces. -/
theorem canonicalDescentFunctor_map {M N : QuasicoherentSheaves.{u, u} B S hS X.1 X.2}
    (φ : M ⟶ N) :
    (canonicalDescentFunctor B S hS Y f).map φ =
      canonicalDescentHom B S hS Y f M.obj N.obj M.property N.property φ.hom :=
  rfl

/-- The `i`-th component of the image of a morphism of quasi-coherent modules under the
canonical descent functor. -/
@[simp]
theorem canonicalDescentFunctor_map_app
    {M N : QuasicoherentSheaves.{u, u} B S hS X.1 X.2} (φ : M ⟶ N) (i : I) :
    ((canonicalDescentFunctor B S hS Y f).map φ).app i =
      (modulePullback B S hS (f i)).map φ.hom :=
  canonicalDescentHom_app B S hS Y f M.obj N.obj M.property N.property φ.hom i

/-- **The effective descent data are the essential image of the canonical descent functor.**
A descent datum for quasi-coherent modules relative to a family of algebraic spaces over `X`
is effective in the sense of Stacks 04W5 — isomorphic to the canonical descent datum of a
quasi-coherent `𝒪_X`-module — exactly when it lies in the essential image of the canonical
descent functor. -/
theorem isEffective_iff_essImage (D : DescentDatum B S hS Y f) :
    IsEffective B S hS Y f D ↔
      (canonicalDescentFunctor B S hS Y f).essImage D := by
  constructor
  · rintro ⟨M, hM, ⟨e⟩⟩
    exact ⟨⟨M, hM⟩, ⟨e.symm⟩⟩
  · rintro ⟨M, ⟨e⟩⟩
    exact ⟨M.obj, M.property, ⟨e.symm⟩⟩

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
