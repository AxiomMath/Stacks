module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSections05ID
public import StacksFrontier.RingTheory.Flat.DevissageDecompositionNoetherian

/-!
# Projective sections after elementary étale neighbourhoods, over a locally Noetherian base

`StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSections05ID` states Tag
05ID — a finitely presented quasi-coherent module flat over the base at a point has projective
global sections after compatible affine elementary étale neighbourhoods — under two named
hypotheses:

* `hConstr`, constructibility of `Algebra.geometricallyIntegralFibreLocus` for a flat algebra of
  finite type over a Noetherian ring, which is the one remaining argument of Stacks 05FT
  (EGA IV 9.7.7), and
* `hdev`, Proposition 05HR composed with Remark 05I0: the square of pointed schemes together with
  a complete dévissage of the global sections whose maps `alpha i` are injective.

`hConstr` enters that proof at exactly one place,
`Module.CompleteDevissage.projective_lowerAlgebra` over the base `Γ(V.scheme, ⊤)`, and it enters
only to produce projectivity of the lower algebras of the dévissage. **Over a Noetherian base it is
not needed**, because the Noetherian case of Stacks 05FT is Stacks 05FS, which is proved; that is
`Module.CompleteDevissage.projective_lowerAlgebra_of_isNoetherianRing`. This file assumes the base
scheme `S` locally Noetherian and so removes `hConstr` outright, with nothing put in its place.

The base of the dévissage is not `S` but `Γ(V.scheme, ⊤)` for an affine étale neighbourhood `V` of
`(S, f x)`. The bridge is `AlgebraicGeometry.EtaleNeighborhood.isNoetherianRing_globalSections`:
`V.toBase` is étale, hence locally of finite type, so `V.scheme` is locally Noetherian by
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, and `V.scheme` is affine, so its
global sections are the sections on an affine open of a locally Noetherian scheme.

## What is and is not proved

`hConstr` is gone; `hdev` remains, and so the theorem below is **still conditional**. For that
reason **no declaration in this file carries a `@[stacks 05ID]` attribute**: being sorry-free and
axiom-clean does not make a conditional statement a proof of the tag, and `hdev` is the whole
geometric content of Tag 05ID — Proposition 05HR and its six lemma inputs 05H6, 05HF, 05HA, 05HE,
05HK, 05HM. Tag 05ID itself, with no Noetherian hypothesis and no `hdev`, is
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt`
in `StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsFlatAtPoint`,
which proves that content rather than assuming it, and which supersedes the theorem below. As the
module docstring of the conditional file
explains at length, `hdev` is a *deferral* and not a weakening: it is strictly stronger than the
conclusion at the ring level (the separating witness being the sections of the tangent bundle of
the real `2`-sphere, by the hairy ball theorem), but at the scheme level it is a theorem of the
source and therefore excludes no case of Tag 05ID.

The Noetherian hypothesis, by contrast, *is* a restriction of generality: Tag 05ID carries no
Noetherian hypothesis, and — unlike Stacks 053R — this restriction is **not** mirrored by any case
split in the source. The source proves Tag 05ID in general, through Proposition 05HR, and nothing
in its argument passes through a Noetherian base. So this is the weaker of the two possible
dispositions of `hConstr`: it sidesteps EGA IV 9.7.7 rather than proving it, at the cost of a
hypothesis the tag does not have. Reducing `hConstr` itself is not an option here — the good halves
of the generic-fibre dichotomy that it would reduce to are already proved *equivalent* to the
constructibility they serve, by
`Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus_iff_isConstructible` and
`Algebra.exists_basicOpen_subset_geometricallyIrreducibleFibreLocus_iff_isConstructible`, so any
such reduction is circular.

## Main results

* `AlgebraicGeometry.EtaleNeighborhood.isNoetherianRing_globalSections`: the global sections of an
  affine étale neighbourhood of a locally Noetherian scheme form a Noetherian ring.
* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_of_isLocallyNoetherian`
  is Tag 05ID over a locally Noetherian base, with `hConstr` removed and `hdev` retained.
* `AlgebraicGeometry.not_projective_of_isNoetherianRing_of_moduleFinite`: a guard, recording that
  the Noetherian hypothesis cannot trivialise the conclusion.

## Implementation notes

The statement of the main theorem is that of
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections` with the binder
`hConstr` deleted and the instance binder `[IsLocallyNoetherian S]` added, and is otherwise
character-for-character the same, including the scalar actions, which are the ones Tag 05ID
specifies: `Module.compHom` along the map on global sections induced by the vertical morphism, and
`RingHom.toAlgebra` of the same homomorphism, so that the scalar tower is `rfl`.

### Why neither hypothesis is idle

`[IsLocallyNoetherian S]` is used once, to synthesize `IsNoetherianRing Γ(V.scheme, ⊤)` for
`Module.CompleteDevissage.projective_lowerAlgebra_of_isNoetherianRing`; deleting it leaves that
application as the sole failure. It cannot trivialise the conclusion, because projectivity over the
base is not a consequence of the side conditions it supplies:
`AlgebraicGeometry.not_projective_of_isNoetherianRing_of_moduleFinite` exhibits a Noetherian ring,
an algebra of finite type over it and a finite module over that algebra which is not projective
over the base. Nor can it degenerate the dévissage: a `Module.CompleteDevissage` indexes its stages
by `Fin (D.stepCount + 1)`, which is never empty, so the stagewise hypotheses are always consumed
at least once — unlike `Module.CompleteDevissageAt`, which has an empty constructor, available only
for the zero module (`Module.CompleteDevissageAt.subsingleton_of_length_eq_zero`).

`hdev` is used twice and is the only source of the data in the conclusion: the neighbourhoods `V`,
`U` and the morphism `h` that the conclusion exhibits are precisely the ones it produces, and its
injectivity clause is consumed by
`Module.CompleteDevissage.projective_of_injective_alpha`. Weakening either clause breaks exactly
one step of the proof and nothing else.

## References

* [Stacks Project, Tag 05ID](https://stacks.math.columbia.edu/tag/05ID)
* [Stacks Project, Tag 05HR](https://stacks.math.columbia.edu/tag/05HR)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
* [Stacks Project, Tag 05IB](https://stacks.math.columbia.edu/tag/05IB)
* [Stacks Project, Tag 05I4](https://stacks.math.columbia.edu/tag/05I4)
* [Stacks Project, Tag 05FS](https://stacks.math.columbia.edu/tag/05FS)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace EtaleNeighborhood

variable {S : Scheme.{u}} {s : S}

/-- The global sections of an affine étale neighbourhood of a locally Noetherian scheme form a
Noetherian ring.

The structure morphism is étale, hence locally of finite type, so the neighbourhood is locally
Noetherian; being affine, its global sections are the sections on an affine open. This is what
supplies the Noetherian base of
`Module.CompleteDevissage.projective_lowerAlgebra_of_isNoetherianRing` in the theorem below, the
base of the dévissage of Tag 05ID being the global sections of the new base rather than `S`
itself. -/
theorem isNoetherianRing_globalSections [IsLocallyNoetherian S] (V : EtaleNeighborhood S s)
    [IsAffine V.scheme] : IsNoetherianRing Γ(V.scheme, ⊤) :=
  have : IsLocallyNoetherian V.scheme := LocallyOfFiniteType.isLocallyNoetherian V.toBase
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top V.scheme⟩

end EtaleNeighborhood

/-- **Guard: a Noetherian base does not make projectivity of the sections automatic.** The ring
`ℤ` is Noetherian, `ℤ` is an algebra of finite type over it, and `ZMod 2` is a finite module over
that algebra which is *not* projective over `ℤ`.

These are exactly the standing hypotheses that the Noetherian variant of Tag 05ID below puts on the
dévissage datum `Γ(X', g^*F)/Γ(X', 𝒪_{X'})/Γ(S', 𝒪_{S'})`, so the conclusion `Module.Projective`
is not a consequence of them and the hypothesis `[IsLocallyNoetherian S]` cannot have trivialised
it. A projective module is flat, a flat module over a domain has every nonzero scalar acting
injectively, and `2` kills `ZMod 2`. -/
theorem not_projective_of_isNoetherianRing_of_moduleFinite :
    IsNoetherianRing ℤ ∧ Algebra.FiniteType ℤ ℤ ∧ Module.Finite ℤ (ZMod 2) ∧
      ¬ Module.Projective ℤ (ZMod 2) := by
  refine ⟨inferInstance, inferInstance, inferInstance, fun h => ?_⟩
  have : Module.Flat ℤ (ZMod 2) := Module.Flat.of_projective
  have hreg : IsSMulRegular (ZMod 2) (2 : ℤ) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors
      (by simp [mem_nonZeroDivisors_iff_ne_zero])
  exact one_ne_zero (hreg (show (2 : ℤ) • (1 : ZMod 2) = (2 : ℤ) • (0 : ZMod 2) by decide))

/-- **Stacks Project, Tag 05ID over a locally Noetherian base.** A finitely presented
quasi-coherent module which is flat over the base at a point has projective global sections after
compatible affine elementary étale localization of the source and of the base, when the base is
locally Noetherian.

This is `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections` with the
hypothesis `hConstr` — constructibility of the geometrically integral fibre locus, the one
remaining argument of Stacks 05FT — **removed**, at the price of `[IsLocallyNoetherian S]`: over a
Noetherian base the projectivity of the lower algebras that `hConstr` was there to supply comes
from Stacks 05FS instead, through
`Module.CompleteDevissage.projective_lowerAlgebra_of_isNoetherianRing`.

The hypothesis `hdev` is unchanged and still present: it is Proposition 05HR composed with
Remark 05I0, and it carries the whole geometric content of Tag 05ID. **This statement is therefore
conditional and is not a proof of Tag 05ID**, which is why no declaration in this file is tagged;
Tag 05ID is
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt`.
Tag 05ID also carries no Noetherian hypothesis, and unlike Stacks 053R this restriction is not
mirrored by a case split in the source: Tag 05ID is proved there in general. See the module
docstring. -/
theorem exists_elementaryEtaleNeighborhood_projective_sections_of_isLocallyNoetherian
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFinitePresentation f] [F.IsQuasicoherent] [F.IsFinitePresentation]
    [IsLocallyNoetherian S]
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
  let : IsNoetherianRing Γ(V.scheme, ⊤) := EtaleNeighborhood.isNoetherianRing_globalSections V
  exact D.projective_of_injective_alpha hinj

end AlgebraicGeometry

end
