module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestriction
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyIResolutionExists
public import StacksFrontier.Algebra.DifferentialGraded.Module.RightOrthogonalAcyclic
public import StacksFrontier.CategoryTheory.Functor.Derived.DerivableOfInverts
public import StacksCore.Tactic.StacksAttribute

/-! # Derived Hom as a functor on derived categories

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. `DifferentialGradedModule.DerivedHomData`
(`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHom.lean`) is the data of a right derived
functor `RHom(N, -) : D(B, d) ⥤ D(A, d)` of internal Hom out of `N`, which is Tag 09LI, and
`DifferentialGradedModule.DerivedHomData.ofResolutions` constructs it from a supply of
resolutions orthogonal on the right to the acyclic modules.

This file supplies the three things a consumer of that data needs and which do not depend on how
the data was obtained.

*The functor is unique.* `DifferentialGradedModule.DerivedHomData.functorIso` identifies the
functors of any two such data, canonically, because each is a left Kan extension along the same
localization. So `RHom(N, -)` is well defined up to a canonical isomorphism and a consumer need
not care which construction produced it.

*The resolution hypothesis in its Stacks form.* `ofResolutions` asks for resolutions by modules
orthogonal on the right to the acyclic ones; the Stacks source supplies them as resolutions by
modules with property (I) (Tag 09KU) whose orthogonality is Tag 09KS.
`DifferentialGradedModule.DerivedHomData.ofPropertyIResolutions` is the composite, and feeding it
Tag 09KU (`DifferentialGradedModule.exists_propertyI_resolution`) gives the *unconditional*
Tag 09LI, `DifferentialGradedModule.derivedHomData`. The mirror of this reduction on the left —
the one that makes derived tensor product unconditional — is
`DifferentialGradedModule.exists_quasiIso_leftOrthogonal_acyclic`.

*The degenerate case needs no resolutions.* When internal Hom out of `N` already inverts the
quasi-isomorphisms, the derived functor is the factorisation through the localization and the
data exists outright: `DifferentialGradedModule.DerivedHomData.ofInverts`. This happens for the
regular bimodule `B` of a homomorphism `φ : A → B`, where internal Hom is restriction of scalars
(Tag 0BYX, Example 22.33.2), and `DifferentialGradedModule.DerivedHomData.regular` is therefore
an *unconditional* `DerivedHomData` whose functor is the already-constructed
`DifferentialGradedModule.derivedRestriction`.

## Main definitions

* `DifferentialGradedModule.derivedHomData`: **Tag 09LI**, the right derived functor
  `RHom(N, -)` of internal Hom out of `N`, unconditionally.
* `DifferentialGradedModule.DerivedHomData.ofPropertyIResolutions`: the derived Hom data from
  resolutions by modules with property (I).
* `DifferentialGradedModule.DerivedHomData.ofInverts`: the derived Hom data when internal Hom
  already inverts the quasi-isomorphisms.
* `DifferentialGradedModule.DerivedHomData.functorIso`: the canonical isomorphism between the
  functors of two derived Hom data.
* `DifferentialGradedModule.regularHomFactorization`: the factorisation of internal Hom out of
  the regular bimodule through the localization, with derived restriction of scalars as the
  factor.
* `DifferentialGradedModule.DerivedHomData.regular`: derived Hom out of the regular bimodule, as
  a right derived functor, with no resolutions used.

## Main results

* `DifferentialGradedModule.exists_quasiIso_rightOrthogonal_acyclic_of_propertyI_resolutions`:
  resolutions by modules with property (I) are resolutions by modules orthogonal on the right to
  the acyclic ones, which is Tag 09KS.
* `DifferentialGradedModule.DerivedHomData.functorIsoDerivedRestriction`: the functor of *any*
  derived Hom data for the regular bimodule is canonically derived restriction of scalars.

## Implementation notes

*Why the conditional form is kept alongside the unconditional one.* Nothing here constructs the
resolutions themselves: for an arbitrary bimodule the input
`∀ M, ∃ I f, QuasiIso f ∧ Nonempty (PropertyIFiltration I)` is Tag 09KU, proved in
`StacksFrontier/Algebra/DifferentialGraded/Module/PropertyIResolutionExists.lean`.
`DifferentialGradedModule.DerivedHomData.ofPropertyIResolutions` assumes it as a hypothesis and
therefore carries no tag; `DifferentialGradedModule.derivedHomData` is that composite applied to
the proof, and is the tagged statement. The Hom functor out of an arbitrary bimodule genuinely
does not invert the quasi-isomorphisms, so
`DifferentialGradedModule.DerivedHomData.ofInverts` cannot replace that input; it covers exactly
the bimodules for which internal Hom descends, the regular one among them.

*Why the uniqueness is stated on the functors and not as a structure isomorphism.* Two derived
Hom data agree on the functor up to a canonical isomorphism, but not on the nose, and their
comparison maps correspond under it only after whiskering. The isomorphism of functors is what
Mathlib's `CategoryTheory.Functor.rightDerivedUnique` provides and what every consumer uses; the
compatibility of the comparisons is `CategoryTheory.Functor.rightDerivedNatTrans_fac`, available
on the underlying Kan extension data and not restated here.

*Universes.* The differential graded algebras and their modules are taken at main's
single-universe encoding `StacksDraft.Ch22.Sec4.Tag09JJ`, in which
`DifferentialGradedAlgebra : Type u → Type u` and a module over it again lies in `Type u`. The
Stacks source, and the statements above this one, are universe-polymorphic in the base ring, in each
algebra and in each module separately; folding those needs the encoding widened, which is not
done here. Nothing below depends on the universes being equal, so the widening is an addition of
universe parameters rather than a change of content.

## References

* [Stacks Project, Tag 09LI](https://stacks.math.columbia.edu/tag/09LI); the criterion it
  applies is [Tag 06XN](https://stacks.math.columbia.edu/tag/06XN), the resolutions are
  [Tag 09KU](https://stacks.math.columbia.edu/tag/09KU), their orthogonality is
  [Tag 09KS](https://stacks.math.columbia.edu/tag/09KS), the functor being derived is
  [Tag 0FQQ](https://stacks.math.columbia.edu/tag/0FQQ), and the regular bimodule is
  [Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX).
-/

@[expose] public noncomputable section

open CategoryTheory

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R]

/-! ### Resolutions by modules with property (I) -/

/-- Every differential graded `A`-module admits a quasi-isomorphism into a differential graded
`A`-module whose class in `K(A, d)` is orthogonal on the right to the acyclic modules, as soon as
it admits one into a module with property (I).

This is the hypothesis under which Tag 06XN produces right derived functors on `K(A, d)`, and it
is Tag 09KU — a resolution by a module with property (I) — followed by Tag 09KS — a module with
property (I) is right orthogonal to the acyclic modules. Only the second half is proved here; the
first is the hypothesis `hres`. The mirror statement on the left, where the resolutions are
available unconditionally, is
`DifferentialGradedModule.exists_quasiIso_leftOrthogonal_acyclic`. -/
theorem exists_quasiIso_rightOrthogonal_acyclic_of_propertyI_resolutions
    (A : DifferentialGradedAlgebra.{u, u} R)
    (hres : ∀ M : DifferentialGradedModule.{u, u, u} A,
      ∃ (I : DifferentialGradedModule.{u, u, u} A) (f : M ⟶ I),
      QuasiIso ((forgetToCochainComplex A).map f) ∧ Nonempty (PropertyIFiltration I))
    (M : DifferentialGradedModule.{u, u, u} A) :
    ∃ (I : DifferentialGradedModule.{u, u, u} A) (f : M ⟶ I),
      QuasiIso ((forgetToCochainComplex A).map f) ∧
        (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj I) := by
  obtain ⟨I, f, hf, ⟨F⟩⟩ := hres M
  exact ⟨I, f, hf, rightOrthogonal_acyclic_of_propertyI F⟩

namespace DerivedHomData

section General

variable (A B : DifferentialGradedAlgebra R) (N : DifferentialGradedModule B)
  (L : BimoduleStructure A B N)

/-- **Tag 09LI from Tag 09KU.** The right derived functor of Hom out of `N` exists as soon as
every differential graded `B`-module admits a quasi-isomorphism into a module with property (I).

This is `DifferentialGradedModule.DerivedHomData.ofResolutions` with its hypothesis in the shape
the Stacks source supplies it: the orthogonality of a module with property (I) to the acyclic
ones is Tag 09KS and is discharged here, while the existence of the resolutions is Tag 09KU and
remains the hypothesis `hres`. -/
def ofPropertyIResolutions
    (hres : ∀ M : DifferentialGradedModule B, ∃ (I : DifferentialGradedModule B) (f : M ⟶ I),
      QuasiIso ((forgetToCochainComplex B).map f) ∧ Nonempty (PropertyIFiltration I)) :
    DerivedHomData A B N L :=
  ofResolutions A B N L
    (exists_quasiIso_rightOrthogonal_acyclic_of_propertyI_resolutions B hres)

/-- **The degenerate case of Tag 09LI.** If internal Hom out of `N`, followed by localization of
the target, already inverts the quasi-isomorphisms of differential graded `B`-modules, then it
descends to the derived category and that descent *is* its right derived functor: no resolutions
are needed.

Both conditions recorded by `DifferentialGradedModule.DerivedHomData` come from the inversion
directly — everywhere-definedness in the sense of Tag 05SV from
`CategoryTheory.Functor.isRightDerivable_of_isInvertedBy`, and the universal property from
Mathlib's `CategoryTheory.Functor.isRightDerivedFunctor_of_inverts`, the factorisation being a
left Kan extension along the localization. -/
def ofInverts (hF : (quasiIsomorphisms' B).IsInvertedBy (homToDerivedCategory A B N L)) :
    DerivedHomData A B N L where
  functor := Localization.lift _ hF (quasiIsomorphisms' B).Q
  comparison := (Localization.fac _ hF (quasiIsomorphisms' B).Q).inv
  derivable := Functor.isRightDerivable_of_isInvertedBy _ _ hF
  isRightDerived :=
    Functor.isRightDerivedFunctor_of_inverts _ _ (Localization.fac _ hF (quasiIsomorphisms' B).Q)

/-- **The derived Hom functor is unique.** The functors of two right derived functors of Hom out
of `N` are canonically isomorphic, because each is a left Kan extension of the same functor along
the same localization. So `RHom(N, -)` does not depend on which construction produced it. -/
def functorIso (D D' : DerivedHomData A B N L) : D.functor ≅ D'.functor :=
  haveI := D.isRightDerived
  haveI := D'.isRightDerived
  Functor.rightDerivedUnique D.functor D'.functor D.comparison D'.comparison (quasiIsomorphisms' B)

/-- A functor on derived categories which internal Hom out of `N` factors through, up to
isomorphism, is canonically the derived Hom functor. This is the previous uniqueness statement
with one of the two data replaced by the factorisation it would be built from, which is how a
*named* functor — `DifferentialGradedModule.derivedRestriction`, say — gets identified with
`RHom(N, -)` without going through
`DifferentialGradedModule.DerivedHomData.ofInverts` first. -/
def functorIsoOfFactorization (D : DerivedHomData A B N L)
    {G : (quasiIsomorphisms' B).Localization ⥤ (quasiIsomorphisms' A).Localization}
    (e : (quasiIsomorphisms' B).Q ⋙ G ≅ homToDerivedCategory A B N L) :
    D.functor ≅ G :=
  haveI := D.isRightDerived
  haveI := Functor.isRightDerivedFunctor_of_inverts (quasiIsomorphisms' B) G e
  Functor.rightDerivedUnique D.functor G D.comparison e.inv (quasiIsomorphisms' B)

end General

end DerivedHomData

/-! ### Tag 09LI -/

/-- **Stacks 09LI.** *The right derived functor of `F` exists; we denote it
`RHom(N, -) : D(B, d) ⥤ D(A, d)`.* Here `F` is internal Hom out of the differential graded
`(A, B)`-bimodule `N` read on homotopy categories and followed by localization
(`DifferentialGradedModule.homToDerivedCategory`), and a right derived functor of it, with its
comparison map and the everywhere-definedness of Tag 05SV, is exactly a
`DifferentialGradedModule.DerivedHomData`; so the source's assertion that the derived functor
exists is the construction of one such datum, which this is.

It is `DifferentialGradedModule.DerivedHomData.ofPropertyIResolutions` — the Stacks proof, Tag
06XN applied to the modules with property (I), whose orthogonality to the acyclic modules is
Tag 09KS — fed the existence of the resolutions, Tag 09KU
(`DifferentialGradedModule.exists_propertyI_resolution`). Nothing is assumed.

The functor is determined by this up to the canonical isomorphism
`DifferentialGradedModule.DerivedHomData.functorIso`, so a consumer that only needs *some*
`RHom(N, -)` should take an arbitrary datum rather than this one. -/
@[stacks 09LI]
def derivedHomData (A B : DifferentialGradedAlgebra R) (N : DifferentialGradedModule B)
    (L : BimoduleStructure A B N) : DerivedHomData A B N L :=
  DerivedHomData.ofPropertyIResolutions A B N L (exists_propertyI_resolution B)

/-! ### Derived Hom out of the regular bimodule -/

section Regular

variable {A B : DifferentialGradedAlgebra R}

/-- **Stacks 0BYX.** Internal Hom out of the regular differential graded `(A, B)`-bimodule,
followed by localization of the target, factors through the derived category of `B` as derived
restriction of scalars along `φ`.

This is the composite of the identification of internal Hom out of the regular bimodule with
restriction of scalars (`DifferentialGradedModule.homHomotopyFunctorRegularIso`) and the
defining factorisation of derived restriction
(`DifferentialGradedModule.derivedRestrictionFactorization`). -/
@[stacks 0BYX "the factorization of derived Hom out of the regular bimodule"]
def regularHomFactorization (φ : A.Hom B) :
    (quasiIsomorphisms' B).Q ⋙ derivedRestriction φ ≅
      homToDerivedCategory A B (regularModule B) (regularBimoduleStructure φ) :=
  derivedRestrictionFactorization φ ≪≫
    (Functor.isoWhiskerRight (homHomotopyFunctorRegularIso φ) (quasiIsomorphisms' A).Q).symm

namespace DerivedHomData

/-- **Stacks 0BYX, and Stacks 09LI for the regular bimodule.** Derived Hom out of the regular
differential graded `(A, B)`-bimodule of a homomorphism `φ : A → B`, as a right derived functor
of internal Hom — unconditionally, with the derived functor being the already-constructed
`DifferentialGradedModule.derivedRestriction`.

No resolutions are used: the hypothesis of
`DifferentialGradedModule.DerivedHomData.ofResolutions` — the existence of property (I)
resolutions, Tag 09KU — does not appear, because internal Hom out of the regular bimodule is
restriction of scalars, which does not change the underlying complex and therefore already
inverts the quasi-isomorphisms. -/
@[stacks 0BYX "derived Hom out of the regular bimodule, as a right derived functor"]
def regular (φ : A.Hom B) :
    DerivedHomData A B (regularModule B) (regularBimoduleStructure φ) where
  functor := derivedRestriction φ
  comparison := (regularHomFactorization φ).inv
  derivable := Functor.isRightDerivable_of_isInvertedBy _ _
    (quasiIsomorphisms_isInvertedBy_homToDerivedCategory_regular φ)
  isRightDerived := Functor.isRightDerivedFunctor_of_inverts _ _ (regularHomFactorization φ)

/-- **Stacks 0BYX, Example 22.33.2.** `RHom(B, -) = (-)_A`: the functor of *any* right derived
functor of Hom out of the regular differential graded `(A, B)`-bimodule is canonically derived
restriction of scalars along `φ`. -/
@[stacks 0BYX "RHom(B, -) is restriction of scalars, for any derived Hom datum"]
def functorIsoDerivedRestriction (φ : A.Hom B)
    (D : DerivedHomData A B (regularModule B) (regularBimoduleStructure φ)) :
    D.functor ≅ derivedRestriction φ :=
  functorIsoOfFactorization A B (regularModule B) (regularBimoduleStructure φ) D
    (regularHomFactorization φ)

end DerivedHomData

end Regular

end DifferentialGradedModule

end
