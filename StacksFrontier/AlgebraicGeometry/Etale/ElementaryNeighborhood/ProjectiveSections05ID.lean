module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FreeGlobalSections05KY
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.Flat.DevissageDecomposition
public import StacksFrontier.RingTheory.Flat.EtaleNeighborhoodProjectiveSections
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Projective sections after compatible elementary étale neighbourhoods

Stacks Tag 05ID, the main result of its section, says: for `f : X ⟶ S` locally of finite
presentation and `F` a quasi-coherent `𝒪_X`-module of finite presentation which is flat over `S`
at `x`, there is a commutative square of pointed schemes
```
  (X, x) ← (X', x')
    ↓         ↓
  (S, s) ← (S', s')
```
whose horizontal arrows are elementary étale neighbourhoods, with `X'` and `S'` affine, such that
`Γ(X', g^*F)` is a projective `Γ(S', 𝒪_{S'})`-module.

The source proves it in three moves. Openness of flatness (Tag 0399) shrinks `X` so that `F` is
flat over `S`; Proposition 05HR produces the square together with a *complete dévissage* of
`g^*F/X'/S'` at `x'`; Remark 05I0 reads that dévissage off as a complete dévissage of the ring
datum `Γ(X', g^*F)/Γ(X', 𝒪_{X'})/Γ(S', 𝒪_{S'})` over the prime of `Γ(S', 𝒪_{S'})` belonging to
`s'`; and Lemma 05IB turns a complete dévissage into projectivity of the sections.

This file carries out the last move and everything around it. The ring-level content of Lemma
05IB is already available, as `Module.CompleteDevissage.projective_of_injective_alpha`; what is
added here is the scheme-level statement of Tag 05ID together with the three algebraic side
conditions needed even to *write down* a complete dévissage of the global sections, each derived
from the hypotheses of Tag 05ID rather than assumed:

* `Γ(S', 𝒪_{S'}) → Γ(X', 𝒪_{X'})` is of finite presentation as an algebra, so that it is of
  finite type as a complete dévissage requires. This is local finite presentation of the vertical
  morphism `X' ⟶ S'`, read on global sections because both schemes are affine; the vertical
  morphism is locally of finite presentation because it factors as an étale morphism followed by
  a base change of `f` (`locallyOfFinitePresentation_of_liftBaseChange`, Tag 05KY).
* `Γ(X', g^*F)` is a finite `Γ(X', 𝒪_{X'})`-module, because `g^*F` is of finite type (Tag 01BQ)
  and quasi-coherent (Tag 01BG) and `X'` is affine.
* the `Γ(S', 𝒪_{S'})`-action on the sections, which is restriction of scalars along the vertical
  morphism, is compatible with the algebra structure.

What is left is the hypothesis `hdev` of the main theorem: Proposition 05HR composed with Remark
05I0, in the form of the ring datum it delivers, together with one of the two hypotheses the
proved halves of Tag 05I4 and Lemma 05IB carry — injectivity of the maps `α i`, which the source
obtains from Lemma 05IA after inverting an element outside the prime.

This file is a conditional reduction and carries no `@[stacks 05ID]` attribute. Tag 05ID itself,
with exactly the source's hypotheses and no `hdev`, is
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt`
in `StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsFlatAtPoint`,
which assembles Tag 0399, Proposition 05HR with Remark 05I0 and Lemma 05IB over a general base
instead of assuming them.

The *other* hypothesis of Lemma 05IB, projectivity of the lower algebras over the base, is **not**
assumed here: `Module.CompleteDevissage.projective_lowerAlgebra` already reduces it to two named
external inputs, and it does so over an arbitrary base, with no local ring hypothesis, so it
applies to `Γ(S', 𝒪_{S'})` directly. One of those two inputs, Tag 056T, is discharged by
`AlgebraicGeometry.geometricallyReduced_of_smooth`. The other, constructibility of the
geometrically integral fibre locus over a Noetherian base — the one remaining argument of
Lemma 05FT — is now a theorem,
`Algebra.isConstructible_geometricallyIntegralFibreLocus_of_finiteType`, so neither is a
hypothesis of the main theorem any longer.

The standard-open shrinking of `S'` which Lemma 05IB performs in order to reach the injectivity is
inside `hdev`: the dévissage and the injectivity are both demanded over the very neighbourhood
that the conclusion then produces, so no shrinking is done here and none has to be transported.

## Honest accounting of the reduction

`hdev` is **strictly stronger** than the conclusion, and cannot be derived from it. A complete
dévissage is data — a zigzag of smooth base algebras with finite free presentations stage by
stage — of which projectivity of one module is a single consequence. Concretely, the ring-level
implication used here is strict *inside the class the conclusion describes*. Take
`R = ℝ[x, y, z]/(x² + y² + z² - 1)`, `S = R`, and let `N` be the module of sections of the
tangent bundle of the real `2`-sphere, that is the kernel of `R³ → R`,
`(a, b, c) ↦ a x + b y + c z`. Then `N` is a finite `S`-module and is projective over `R` of rank
`2`, so it satisfies the conclusion; but it has no complete dévissage over any prime with
injective `α i`. Such a dévissage would exhibit `N` as `⨁ i, (B i)^(⊕ r i)` over `R`
(`Module.CompleteDevissage.nonempty_linearEquiv_directSum`), and each `B i` occurring with
`r i ≠ 0` would then be a finite `R`-module as well as smooth over `R`, hence finite étale over
`R`, hence — having geometrically irreducible, so nonempty and of degree one, fibres — isomorphic
to `R`. That makes `N` free; but a basis of `N` would contain a nowhere vanishing tangent vector
field on the sphere, which the hairy ball theorem forbids.

At the scheme level, on the other hand, `hdev` **excludes nothing**: it is a theorem of the
source, so the reduction restricts no case of Tag 05ID. It assumes the whole geometric content of
Tag 05ID, which is Proposition 05HR and its six inputs 05H6, 05HF, 05HA, 05HE, 05HK, 05HM, rather
than trading the statement for an equivalent one; that content is proved elsewhere in the library,
and the unconditional theorem
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt`
uses it.

Two deliberate weakenings of `hdev` relative to what Remark 05I0 actually delivers, both of which
make the theorem stronger: the prime of `Γ(S', 𝒪_{S'})` is existentially quantified instead of
being pinned to the one belonging to `s'`, because
`Module.CompleteDevissage.projective_of_injective_alpha` holds for an arbitrary prime of the base;
and flatness of `F` over `S` at `x` is consumed as the antecedent of `hdev` rather than restated,
so that it is used where the source uses it — inside Tag 0399, Proposition 05HR and Lemma 05IA —
and the main theorem has no unused hypothesis.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.EtaleNeighborhood.algebraFinitePresentation_globalSections`: for compatible
  affine étale neighbourhoods over a morphism locally of finite presentation, the global sections
  of the upper neighbourhood are a finitely presented algebra over those of the lower one.
* `AlgebraicGeometry.EtaleNeighborhood.moduleFinite_pullback_globalSections`: the global sections
  of the pullback of a finitely presented quasi-coherent module to an affine étale neighbourhood
  form a finite module.
* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections`: the conclusion of
  Tag 05ID, conditional on the dévissage of global sections that Proposition 05HR and Remark
  05I0 deliver, its injectivity hypothesis from Lemma 05IA, and the remaining argument of
  Lemma 05FT.

## Implementation notes

The scalar actions are the ones Tag 05ID specifies and are kept verbatim: the
`Γ(S', 𝒪_{S'})`-module structure on `Γ(X', g^*F)` is `Module.compHom` along the map on global
sections induced by the vertical morphism, and the algebra structure used to state the dévissage
is `RingHom.toAlgebra` of the same homomorphism, so that the scalar tower is `rfl`.

Being of finite type is not found by instance search from being of finitely presented, the
universe of the local generating data being a parameter of both classes; Mathlib's instance is
therefore named explicitly.

## References

* [Stacks Project, Tag 05ID](https://stacks.math.columbia.edu/tag/05ID)
* [Stacks Project, Tag 05HR](https://stacks.math.columbia.edu/tag/05HR)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
* [Stacks Project, Tag 05IB](https://stacks.math.columbia.edu/tag/05IB)
* [Stacks Project, Tag 05IA](https://stacks.math.columbia.edu/tag/05IA)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
* [Stacks Project, Tag 01BQ](https://stacks.math.columbia.edu/tag/01BQ)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace EtaleNeighborhood

variable {X S : Scheme.{u}} (f : X ⟶ S) {x : X}

/-- For an étale neighbourhood `U` of `(X, x)` lying over an étale neighbourhood `V` of
`(S, f x)`, both affine, with `f` locally of finite presentation, the global sections of `U` form
a finitely presented algebra over the global sections of `V`.

The vertical morphism `U ⟶ V` is locally of finite presentation because it factors as the étale
comparison morphism `U ⟶ X ×_S V` followed by a base change of `f`, and local finite presentation
of a morphism between affine schemes is finite presentation of the induced homomorphism on global
sections. This is the finiteness of the algebra over which Tag 05ID states a complete
dévissage. -/
theorem algebraFinitePresentation_globalSections [LocallyOfFinitePresentation f]
    (V : EtaleNeighborhood S (f x)) (U : EtaleNeighborhood X x) (h : U.scheme ⟶ V.scheme)
    (hover : h ≫ V.toBase = U.toBase ≫ f) [IsAffine U.scheme] [IsAffine V.scheme] :
    letI : Algebra Γ(V.scheme, ⊤) Γ(U.scheme, ⊤) := h.appTop.hom.toAlgebra
    Algebra.FinitePresentation Γ(V.scheme, ⊤) Γ(U.scheme, ⊤) :=
  HasRingHomProperty.appTop (@LocallyOfFinitePresentation) h
    (locallyOfFinitePresentation_of_liftBaseChange f V U h hover)

/-- The global sections of the pullback of a quasi-coherent module of finite type to an affine
étale neighbourhood form a finite module over the global sections of the neighbourhood.

The pullback is of finite type by Tag 01BQ and quasi-coherent by Tag 01BG, and the sections of
such a module over an affine open are a finite module. This is the finiteness of the module over
which Tag 05ID states a complete dévissage. -/
theorem moduleFinite_pullback_globalSections (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (U : EtaleNeighborhood X x) [IsAffine U.scheme] :
    Module.Finite Γ(U.scheme, ⊤) Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) := by
  have hft : ((Scheme.Modules.pullback U.toBase).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType U.toBase.toLRSHom.toShHom F
  exact moduleFinite_sections_on_affine _ ⊤ (isAffineOpen_top U.scheme)

end EtaleNeighborhood

/-- The conclusion of Stacks Project, Tag 05ID, conditional on the hypothesis `hdev`: a finitely
presented quasi-coherent module which is flat over the base at a point, and whose sections carry
the dévissage of `hdev`, has projective global sections after compatible affine elementary étale
localization of the source and of the base. This is a reduction, not Tag 05ID; Tag 05ID itself,
with no `hdev`, is
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt`.

The hypothesis `hdev` is Proposition 05HR composed with Remark 05I0: the square of pointed
schemes together with a complete dévissage of the global sections of the pulled-back module over
the global sections of the new base, carrying the injectivity of the maps `α i` that the proved
halves of Tag 05I4 and Lemma 05IB also carry and that Lemma 05IA supplies. The other hypothesis
of Lemma 05IB, projectivity of the lower algebras, is supplied by
`Module.CompleteDevissage.projective_lowerAlgebra`, whose own input — the one remaining argument
of Lemma 05FT, constructibility of the geometrically integral fibre locus — is now a theorem.
Everything else in the statement, including
the three algebraic side conditions under which a complete dévissage of the global sections can be
written down at all, is derived here. See the module docstring for why `hdev` is strictly stronger
than the conclusion and nevertheless excludes no case of Tag 05ID. -/
theorem exists_elementaryEtaleNeighborhood_projective_sections
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFinitePresentation f] [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hflat : IsFlatOverAt
      (LocallyRingedSpace.forgetToSheafedSpace.map f.toLRSHom) F x)
    (hdev : IsFlatOverAt (LocallyRingedSpace.forgetToSheafedSpace.map f.toLRSHom) F x →
      ∃ (V : EtaleNeighborhood S (f x)) (U : EtaleNeighborhood X x) (h : U.scheme ⟶ V.scheme)
        (_ : V.IsElementary) (_ : U.IsElementary)
        (hover : h ≫ V.toBase = U.toBase ≫ f) (_ : h U.point = V.point)
        (_ : IsAffine U.scheme) (_ : IsAffine V.scheme)
        (r : Ideal Γ(V.scheme, ⊤)) (_ : r.IsPrime),
        letI : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
        letI : Algebra Γ(V.scheme, ⊤) Γ(U.scheme, ⊤) := h.appTop.hom.toAlgebra
        letI : Algebra.FinitePresentation Γ(V.scheme, ⊤) Γ(U.scheme, ⊤) :=
          EtaleNeighborhood.algebraFinitePresentation_globalSections f V U h hover
        letI : Module Γ(V.scheme, ⊤) Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) :=
          Module.compHom _ h.appTop.hom
        letI : Module.Finite Γ(U.scheme, ⊤) Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) :=
          EtaleNeighborhood.moduleFinite_pullback_globalSections F U
        letI : IsScalarTower Γ(V.scheme, ⊤) Γ(U.scheme, ⊤)
            Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) :=
          IsScalarTower.of_algebraMap_smul fun _ _ => rfl
        ∃ D : Module.CompleteDevissage Γ(V.scheme, ⊤) Γ(U.scheme, ⊤)
            Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) r,
          ∀ i, letI : Module (D.B i) (D.M i) :=
              Module.compHom (D.M i) (D.toLeft i).toRingHom
            Function.Injective (D.alpha i)) :
    ∃ (V : EtaleNeighborhood S (f x))
      (U : EtaleNeighborhood X x) (h : U.scheme ⟶ V.scheme),
      V.IsElementary ∧ U.IsElementary ∧
        (h ≫ V.toBase = U.toBase ≫ f) ∧ (h U.point = V.point) ∧
        IsAffine U.scheme ∧ IsAffine V.scheme ∧
        (let M := (Scheme.Modules.pullback U.toBase).obj F
         letI : Module Γ(V.scheme, ⊤) Γ(M, ⊤) :=
           Module.compHom Γ(M, ⊤) h.appTop.hom
         Module.Projective Γ(V.scheme, ⊤) Γ(M, ⊤)) := by
  obtain ⟨V, U, h, hVel, hUel, hover, hpt, hUaff, hVaff, r, hr, D, hinj⟩ := hdev hflat
  refine ⟨V, U, h, hVel, hUel, hover, hpt, hUaff, hVaff, ?_⟩
  let : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  let : Algebra Γ(V.scheme, ⊤) Γ(U.scheme, ⊤) := h.appTop.hom.toAlgebra
  let : Algebra.FinitePresentation Γ(V.scheme, ⊤) Γ(U.scheme, ⊤) :=
    EtaleNeighborhood.algebraFinitePresentation_globalSections f V U h hover
  let : Module Γ(V.scheme, ⊤) Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) :=
    Module.compHom _ h.appTop.hom
  let : Module.Finite Γ(U.scheme, ⊤) Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) :=
    EtaleNeighborhood.moduleFinite_pullback_globalSections F U
  let : IsScalarTower Γ(V.scheme, ⊤) Γ(U.scheme, ⊤)
      Γ((Scheme.Modules.pullback U.toBase).obj F, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact D.projective_of_injective_alpha hinj

end AlgebraicGeometry

end
