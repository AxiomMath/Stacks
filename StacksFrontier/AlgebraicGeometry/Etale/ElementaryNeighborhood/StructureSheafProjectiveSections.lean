module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSections05ID
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsFlatAtPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus

/-!
# Projective sections of the structure sheaf after elementary étale neighbourhoods

Stacks Tag 05IE is the case `ℱ = 𝒪_X` of Tag 05ID: for `f : X ⟶ S` locally of finite
presentation and `x : X` at which `f` is flat over `S`, there is a commutative square of pointed
schemes
```
  (X, x) ←ᵍ (X', x')
    ↓          ↓
  (S, s) ← (S', s')
```
whose horizontal arrows are elementary étale neighbourhoods, with `X'` and `S'` affine, such that
`Γ(X', 𝒪_{X'})` is a projective `Γ(S', 𝒪_{S'})`-module. Its proof in the source is one sentence:
"This is a special case of Proposition 05ID."

That sentence is the whole content of this file, and it is not vacuous in Lean, because the two
tags speak about different objects. Tag 05ID is a statement about a *module*: its flatness
hypothesis is Tag 08KT, flatness of `ℱ` over `S` at `x`, and its conclusion is projectivity of
`Γ(X', g^*ℱ)`. Tag 05IE is a statement about a *morphism*: its hypothesis is Tag 02N3, flatness
of `f` at `x`, and its conclusion is projectivity of `Γ(X', 𝒪_{X'})`. Specialising one to the
other needs three identifications, all of which are available:

* `AlgebraicGeometry.Scheme.unitModule X` is quasi-coherent and — by
  `AlgebraicGeometry.Scheme.unitModule_isFinitePresentation`, which transports
  `Stacks.SheafOfModules.Site.unit_isFinitePresentation` to the `X.Modules` ascription — of finite
  presentation, so Tag 05ID applies to it;
* `AlgebraicGeometry.isFlatOverAt_unit_iff_isFlatAt` turns flatness of the morphism at `x` into
  flatness of the structure sheaf over the base at `x`;
* `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` identifies `g^*𝒪_X` with `𝒪_{X'}`, and
  `AlgebraicGeometry.Scheme.Modules.pullbackUnitSectionsLinearEquiv` reads that identification on
  global sections, where it is `Γ(X', 𝒪_{X'})`-linear and therefore also linear for the
  restriction of scalars along `Γ(S', 𝒪_{S'}) ⟶ Γ(X', 𝒪_{X'})` that both sides carry.

## The two forms of Tag 05IE

This library has Tag 05ID and a conditional reduction of it, and Tag 05IE is proved from each.

`exists_elementaryEtaleNeighborhood_projective_structureSheafSections_of_isFlatAt` instantiates
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt` at
the structure sheaf. Its hypotheses are the source's, and only the source's: `f` locally of
finite presentation and `f` flat at `x`.

`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_structureSheafSections`
instantiates `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections` instead,
and so carries that theorem's hypothesis `hdev` with `ℱ` at the structure sheaf: a complete
dévissage at the point, in the sense of Proposition 05HR composed with Remark 05I0, whose maps
`α i` of Lemma 05IA are injective. The unconditional form does not discharge `hdev`, since Tag
05ID concludes projectivity of the sections and projectivity does not return a dévissage, so the
two statements are proved separately rather than one from the other; the conditional one serves
consumers that already hold such a dévissage.

Tag 05IE has no Noetherian hypothesis, and neither form adds one: the general forms of Tag 05ID
are the ones used, not
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_of_isLocallyNoetherian`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.sectionsTopLinearEquivOfIso`: isomorphic modules on a scheme
  have linearly isomorphic global sections.
* `AlgebraicGeometry.Scheme.Modules.pullbackUnitSectionsLinearEquiv`: the global sections of the
  pullback of the structure sheaf of the target are the global sections of the source.

## Main results

* `AlgebraicGeometry.Scheme.unitModule_isFinitePresentation`: the structure sheaf of a scheme,
  viewed as a module over itself at the `X.Modules` ascription, is of finite presentation.
* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_structureSheafSections`:
  **Tag 05IE**, from the hypothesis `hdev` of the conditional reduction
  `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections` at the structure
  sheaf.
* `exists_elementaryEtaleNeighborhood_projective_structureSheafSections_of_isFlatAt`, in the same
  namespace: **Tag 05IE** with no hypothesis beyond the source's, obtained from the unconditional
  form of Tag 05ID.

## Implementation notes

The scalar actions are the ones Tag 05IE specifies and are kept in the spelling Tag 05ID uses:
the `Γ(S', 𝒪_{S'})`-module structure on `Γ(X', 𝒪_{X'})` is `Module.compHom` along the map on
global sections induced by the vertical morphism `X' ⟶ S'`.

In the conditional form, flatness of `f` at `x` is a hypothesis of the theorem rather than the
antecedent of `hdev`, unlike in Tag 05ID: it is consumed there, to produce the module-level
flatness that `hdev` asks for, so it is not an idle hypothesis.

`AlgebraicGeometry.Scheme.Modules.sectionsTopLinearEquivOfIso` goes through
`SheafOfModules.evaluation`, whose values are objects of `ModuleCat Γ(X, ⊤)`,
rather than through `AlgebraicGeometry.Scheme.Modules.Hom.app`, whose values are objects of
`AddCommGrpCat`: the linearity of the latter is a separate lemma
(`AlgebraicGeometry.Scheme.Modules.Hom.app_smul`) rather than part of its type, so assembling a
`LinearEquiv` from it means rebuilding by hand what `CategoryTheory.Iso.toLinearEquiv` already
provides.

The finite-presentation instance has to be restated at `AlgebraicGeometry.Scheme.unitModule X`
because `AlgebraicGeometry.Scheme.Modules` is a `def` rather than an `abbrev`, so the instance
registered for `SheafOfModules.unit X.ringCatSheaf` is not found at the ascribed
type; `AlgebraicGeometry.Scheme.unitModule`'s quasi-coherence instance is restated for the same
reason where it is defined.

## References

* [Stacks Project, Tag 05IE](https://stacks.math.columbia.edu/tag/05IE)
* [Stacks Project, Tag 05ID](https://stacks.math.columbia.edu/tag/05ID)
* [Stacks Project, Tag 05HR](https://stacks.math.columbia.edu/tag/05HR)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
* [Stacks Project, Tag 05IA](https://stacks.math.columbia.edu/tag/05IA)
* [Stacks Project, Tag 02N3](https://stacks.math.columbia.edu/tag/02N3)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **The structure sheaf of a scheme, as a module over itself, is of finite presentation**, at
the ascription `X.Modules`.

This is `Stacks.SheafOfModules.Site.unit_isFinitePresentation`, which is registered for
`SheafOfModules.unit X.ringCatSheaf`; `AlgebraicGeometry.Scheme.Modules` being a
`def`, the instance is not found at the ascribed type without this restatement, exactly as for
the quasi-coherence instance of `AlgebraicGeometry.Scheme.unitModule`. -/
instance Scheme.unitModule_isFinitePresentation (X : Scheme.{u}) :
    (Scheme.unitModule X).IsFinitePresentation :=
  inferInstanceAs (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation

/-- **Isomorphic modules on a scheme have linearly isomorphic global sections.** The isomorphism
is the one the isomorphism of modules induces on sections over `⊤`, which is linear over
`Γ(X, ⊤)` because it is a morphism of `𝒪_X`-modules. -/
def Scheme.Modules.sectionsTopLinearEquivOfIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(N, ⊤) :=
  ((SheafOfModules.evaluation (R := X.ringCatSheaf) (op (⊤ : X.Opens))).mapIso e).toLinearEquiv

/-- **The global sections of the pullback of the structure sheaf are the global sections of the
source.** This reads `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` — the identification of
`f^*𝒪_Y` with `𝒪_X` — on sections over `⊤`. It is the identification
`Γ(X', g^*𝒪_X) = Γ(X', 𝒪_{X'})` which makes Tag 05IE the case `ℱ = 𝒪_X` of Tag 05ID. -/
def Scheme.Modules.pullbackUnitSectionsLinearEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Γ((Scheme.Modules.pullback f).obj (Scheme.unitModule Y), ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
  Scheme.Modules.sectionsTopLinearEquivOfIso (Scheme.Modules.pullbackUnitIso f)

/-- **Projectivity passes from `Γ(Y, g^*𝒪_X)` to `Γ(Y, 𝒪_Y)`.** For `g : Y ⟶ X` and
`h : Y ⟶ Z`, if the global sections of the pullback of the structure sheaf of `X` are projective
over `Γ(Z, ⊤)` along `h`, then so are the global sections of `Y`: the two are identified by
`AlgebraicGeometry.Scheme.Modules.pullbackUnitSectionsLinearEquiv`, which is `Γ(Y, ⊤)`-linear and
hence linear for the restriction of scalars along `h`. -/
private theorem projective_appTop_of_projective_pullbackUnit {X Y Z : Scheme.{u}} (g : Y ⟶ X)
    (h : Y ⟶ Z)
    (hproj : letI : Module Γ(Z, ⊤) Γ((Scheme.Modules.pullback g).obj (Scheme.unitModule X), ⊤) :=
        Module.compHom _ h.appTop.hom
      Module.Projective Γ(Z, ⊤) Γ((Scheme.Modules.pullback g).obj (Scheme.unitModule X), ⊤)) :
    letI : Module Γ(Z, ⊤) Γ(Y, ⊤) := Module.compHom Γ(Y, ⊤) h.appTop.hom
    Module.Projective Γ(Z, ⊤) Γ(Y, ⊤) := by
  let eU := Scheme.Modules.pullbackUnitSectionsLinearEquiv g
  let : Module Γ(Z, ⊤) Γ((Scheme.Modules.pullback g).obj (Scheme.unitModule X), ⊤) :=
    Module.compHom _ h.appTop.hom
  let : Module Γ(Z, ⊤) Γ(Y, ⊤) := Module.compHom Γ(Y, ⊤) h.appTop.hom
  exact Module.Projective.of_equiv' (R := Γ(Z, ⊤))
    { eU.toAddEquiv with map_smul' := fun r m => eU.map_smul (h.appTop.hom r) m }

/-- **Stacks Project, Tag 05IE.** Let `f : X ⟶ S` be locally of finite presentation and let
`x : X`. If `f` is flat at `x` over `S`, then there is a commutative square of pointed schemes
```
  (X, x) ←ᵍ (X', x')
    ↓          ↓
  (S, s) ← (S', s')
```
whose horizontal arrows are elementary étale neighbourhoods, with `X'` and `S'` affine, such that
`Γ(X', 𝒪_{X'})` is a projective `Γ(S', 𝒪_{S'})`-module.

This is the case `ℱ = 𝒪_X` of Tag 05ID, as in the source. The flatness hypothesis is converted
from the morphism to the structure sheaf by
`AlgebraicGeometry.isFlatOverAt_unit_iff_isFlatAt`, and the conclusion is converted back from
`Γ(X', g^*𝒪_X)` to `Γ(X', 𝒪_{X'})` by
`AlgebraicGeometry.Scheme.Modules.pullbackUnitSectionsLinearEquiv`; the finite presentation of
`𝒪_X` as a module, which Tag 05ID requires of `ℱ`, is
`AlgebraicGeometry.Scheme.unitModule_isFinitePresentation`.

The hypothesis `hdev` is the hypothesis of the conditional reduction of Tag 05ID,
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections`, instantiated at
the structure sheaf: Proposition 05HR composed with Remark 05I0, carrying the injectivity of the
maps `α i` of Lemma 05IA. Nothing is assumed beyond it — in particular no Noetherian hypothesis,
which Tag 05IE does not have. The form without `hdev` is
`exists_elementaryEtaleNeighborhood_projective_structureSheafSections_of_isFlatAt`. -/
@[stacks 05IE "the full conclusion; assumes only `hdev` of Tag 05ID at the structure sheaf"]
theorem exists_elementaryEtaleNeighborhood_projective_structureSheafSections
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) [LocallyOfFinitePresentation f]
    (hflat : IsFlatAt (LocallyRingedSpace.forgetToSheafedSpace.map f.toLRSHom) x)
    (hdev : IsFlatOverAt (LocallyRingedSpace.forgetToSheafedSpace.map f.toLRSHom)
        (Scheme.unitModule X) x →
      ∃ (V : EtaleNeighborhood S (f x)) (U : EtaleNeighborhood X x) (h : U.scheme ⟶ V.scheme)
        (_ : V.IsElementary) (_ : U.IsElementary)
        (hover : h ≫ V.toBase = U.toBase ≫ f) (_ : h U.point = V.point)
        (_ : IsAffine U.scheme) (_ : IsAffine V.scheme)
        (r : Ideal Γ(V.scheme, ⊤)) (_ : r.IsPrime),
        letI : (Scheme.unitModule X).IsFiniteType :=
          SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (Scheme.unitModule X)
        letI : Algebra Γ(V.scheme, ⊤) Γ(U.scheme, ⊤) := h.appTop.hom.toAlgebra
        letI : Algebra.FinitePresentation Γ(V.scheme, ⊤) Γ(U.scheme, ⊤) :=
          EtaleNeighborhood.algebraFinitePresentation_globalSections f V U h hover
        letI : Module Γ(V.scheme, ⊤)
            Γ((Scheme.Modules.pullback U.toBase).obj (Scheme.unitModule X), ⊤) :=
          Module.compHom _ h.appTop.hom
        letI : Module.Finite Γ(U.scheme, ⊤)
            Γ((Scheme.Modules.pullback U.toBase).obj (Scheme.unitModule X), ⊤) :=
          EtaleNeighborhood.moduleFinite_pullback_globalSections (Scheme.unitModule X) U
        letI : IsScalarTower Γ(V.scheme, ⊤) Γ(U.scheme, ⊤)
            Γ((Scheme.Modules.pullback U.toBase).obj (Scheme.unitModule X), ⊤) :=
          IsScalarTower.of_algebraMap_smul fun _ _ => rfl
        ∃ D : Module.CompleteDevissage Γ(V.scheme, ⊤) Γ(U.scheme, ⊤)
            Γ((Scheme.Modules.pullback U.toBase).obj (Scheme.unitModule X), ⊤) r,
          ∀ i, letI : Module (D.B i) (D.M i) :=
              Module.compHom (D.M i) (D.toLeft i).toRingHom
            Function.Injective (D.alpha i)) :
    ∃ (V : EtaleNeighborhood S (f x)) (U : EtaleNeighborhood X x) (h : U.scheme ⟶ V.scheme),
      V.IsElementary ∧ U.IsElementary ∧
        (h ≫ V.toBase = U.toBase ≫ f) ∧ (h U.point = V.point) ∧
        IsAffine U.scheme ∧ IsAffine V.scheme ∧
        (letI : Module Γ(V.scheme, ⊤) Γ(U.scheme, ⊤) :=
           Module.compHom Γ(U.scheme, ⊤) h.appTop.hom
         Module.Projective Γ(V.scheme, ⊤) Γ(U.scheme, ⊤)) := by
  obtain ⟨V, U, h, hVel, hUel, hover, hpt, hUaff, hVaff, hproj⟩ :=
    exists_elementaryEtaleNeighborhood_projective_sections f (Scheme.unitModule X) x
      ((isFlatOverAt_unit_iff_isFlatAt f x).mpr hflat) hdev
  exact ⟨V, U, h, hVel, hUel, hover, hpt, hUaff, hVaff,
    projective_appTop_of_projective_pullbackUnit U.toBase h hproj⟩

/-- **Stacks Project, Tag 05IE.** Let `f : X ⟶ S` be locally of finite presentation and let
`x : X`. If `f` is flat at `x` over `S`, then there is a commutative square of pointed schemes
```
  (X, x) ←ᵍ (X', x')
    ↓          ↓
  (S, s) ← (S', s')
```
whose horizontal arrows are elementary étale neighbourhoods, with `X'` and `S'` affine, such that
`Γ(X', 𝒪_{X'})` is a projective `Γ(S', 𝒪_{S'})`-module.

This is the case `ℱ = 𝒪_X` of Tag 05ID, as in the source, whose proof of Tag 05IE is the single
sentence "This is a special case of Proposition 05ID". The specialisation needs the three
identifications of the module docstring: `AlgebraicGeometry.Scheme.unitModule X` is quasi-coherent
and, by `AlgebraicGeometry.Scheme.unitModule_isFinitePresentation`, of finite presentation, so Tag
05ID applies to it; `AlgebraicGeometry.isFlatOverAt_unit_iff_isFlatAt` turns flatness of the
morphism at `x` into flatness of the structure sheaf over the base at `x`; and
`AlgebraicGeometry.Scheme.Modules.pullbackUnitSectionsLinearEquiv` identifies `Γ(X', g^*𝒪_X)` with
`Γ(X', 𝒪_{X'})`, compatibly with the restriction of scalars along
`Γ(S', 𝒪_{S'}) ⟶ Γ(X', 𝒪_{X'})` that both sides carry.

Unlike
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_structureSheafSections`, this
carries no hypothesis beyond the source's: the unconditional form of Tag 05ID,
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt`, is
used in place of the conditional
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections`, so there is nothing
left to assume. -/
@[stacks 05IE]
theorem exists_elementaryEtaleNeighborhood_projective_structureSheafSections_of_isFlatAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) [LocallyOfFinitePresentation f]
    (hflat : IsFlatAt f.toLRSHom.toShHom x) :
    ∃ (V : EtaleNeighborhood S (f x)) (U : EtaleNeighborhood X x) (h : U.scheme ⟶ V.scheme),
      V.IsElementary ∧ U.IsElementary ∧
        (h ≫ V.toBase = U.toBase ≫ f) ∧ (h U.point = V.point) ∧
        IsAffine U.scheme ∧ IsAffine V.scheme ∧
        (letI : Module Γ(V.scheme, ⊤) Γ(U.scheme, ⊤) :=
           Module.compHom Γ(U.scheme, ⊤) h.appTop.hom
         Module.Projective Γ(V.scheme, ⊤) Γ(U.scheme, ⊤)) := by
  obtain ⟨V, U, h, hVel, hUel, hover, hpt, hUaff, hVaff, hproj⟩ :=
    exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt f
      (Scheme.unitModule X) x ((isFlatOverAt_unit_iff_isFlatAt f x).mpr hflat)
  exact ⟨V, U, h, hVel, hUel, hover, hpt, hUaff, hVaff,
    projective_appTop_of_projective_pullbackUnit U.toBase h hproj⟩

end AlgebraicGeometry

end
