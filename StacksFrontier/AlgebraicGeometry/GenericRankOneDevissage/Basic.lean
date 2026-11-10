module

public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IrreducibleSupportCriterion
public import StacksFrontier.AlgebraicGeometry.CoherentDevissageGlue.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic

/-!
# Dévissage of coherent modules over the integral closed subschemes of a Noetherian scheme

Let `X` be a Noetherian scheme and let `P` be a property of coherent `𝒪_X`-modules such that

1. for every short exact sequence of coherent modules, if two out of the three terms have `P`
   then so does the third, and
2. for every integral closed subscheme `Z ⊆ X` with generic point `ξ` there is a coherent
   module `𝒢` with `Supp 𝒢 = Z`, with `𝒢_ξ` annihilated by `𝔪_ξ`, and with
   `dim_{κ(ξ)} 𝒢_ξ = 1`, for which `P` holds.

Then `P` holds for every coherent module on `X`. This is the global dévissage criterion of
[Stacks, Tag 01YI], and the content added here over its two inputs is the Noetherian induction
on closed subsets.

Both inputs are available. The criterion of [Stacks, Tag 01YG] reduces the conclusion to the
direct images `i_* ℐ` of quasi-coherent ideals `ℐ ⊆ 𝒪_Z` along the closed immersions
`i : Z ⟶ X` of integral closed subschemes, and the criterion of [Stacks, Tag 01YH] settles all
modules supported inside one irreducible closed subset `Z₀` from the data of (1), of a module
`𝒢` as in (2) for `Z₀`, and of `P` on the direct images coming from integral closed subschemes
*strictly* inside `Z₀`. Running the latter at `Z₀ = ` the range of `i` turns that last input
into the inductive hypothesis of a well-founded induction on closed subsets, which is what
`pushforward_ideal_property_of_genericRankOne` carries out.

## Main results

* `pushforward_ideal_property_of_genericRankOne`: from (1) and (2) alone, `P` holds for the
  direct image of every quasi-coherent ideal along every integral closed subscheme of `X`.
* `property_terminal_of_genericRankOne`: a property satisfying (1) which holds for one coherent
  module holds for the zero module.
* `property_of_genericRankOne`: from (1), (2) and `P` on the zero module, `P` holds for every
  coherent module.
* `property_of_genericRankOne_of_exists_isIntegral`: the same conclusion from (1), (2) and the
  existence of one integral closed subscheme of `X`, which replaces the hypothesis on the zero
  module.

## Implementation notes

**The well-founded induction runs on `TopologicalSpace.Closeds X` under `<`.** The underlying
space of a Noetherian scheme is Noetherian, so the strict order on its closed sets is
well-founded; the motive is `P` for the direct images of quasi-coherent ideals off the integral
closed subschemes whose range is the given closed set. Taking the motive at the *equality*
`Set.range i.base = C` rather than at an inclusion is what makes the inductive hypothesis apply
to a strictly smaller subscheme with `rfl`.

**The generic point is taken on the image rather than on the source.** A term
`genericPoint Z` needs an `IrreducibleSpace Z` instance, which `IsIntegral Z` supplies only
through a lemma and so is unavailable while a signature is being elaborated.
`Stacks.AlgebraicGeometry.CoherentDevissageGlue.isGenericPoint_toImage_genericPoint` instead
produces a point of `X` together with the proof that it is a generic point of
`Set.range i.base`, and condition (2) is therefore stated for every generic point of that
range. Since a scheme is sober the generic point of an irreducible closed subset is unique, so
this is the same condition as the source's.

**Every hypothesis is in the signature of a `theorem`.** There is no section variable and no
statement-carrying definition here, so the printed type of each result below is its full
content.

**`dim_{κ(ξ)} 𝒢_ξ = 1` is `Module.length` one of the stalk over the local ring at `ξ`.** This is
the spelling of [Stacks, Tag 01YH], whose own notes record why the two agree: annihilation by
`𝔪_ξ` makes the stalk a `κ(ξ)`-vector space, and its length is then its dimension. Condition (2)
is stated here exactly as that criterion consumes it, so no translation intervenes.

### [Stacks, Tag 01YI] is false as stated, and is carried here in its corrected forms

*The conclusion of 01YI does not follow from its two stated hypotheses.* Let `X` be the empty
scheme — `Spec` of the zero ring, which is Noetherian — and let `P` be the identically false
property. An integral scheme is irreducible and hence nonempty, so `X` has no integral closed
subscheme and condition (2) holds vacuously; `P` never holds, so the antecedent of condition (1)
is never met and (1) holds too. The zero module is coherent, and `P` fails for it.

What the two results above add to (1) and (2) is exactly what repairs this, in the two
inequivalent ways: `P` on the zero module, which is also the hypothesis the project's statement
of [Stacks, Tag 01YG] adds for the same reason, or the existence of one integral closed
subscheme, which is the weaker of the two and is implied by `Nonempty X`. Both are
strengthenings of the source's hypotheses, so neither statement is literally the source's; each
carries the tag with the correction named in its attribute.

Narrowing `property_of_genericRankOne_of_exists_isIntegral` to `[Nonempty X]`, which is as close
to the source as a true statement reaches, needs a reduced induced closed subscheme structure on
the closure of a point. Two declarations would supply it and neither exists at this pin:
`AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal`, reducedness of
`(Scheme.IdealSheafData.vanishingIdeal Z).subscheme` for a closed `Z`, which with
`AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced` would make the reduced closure
of a point an integral closed subscheme; or an existence statement for a closed point of a
nonempty Noetherian scheme, which with
`AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion` would make
`Spec (X.residueField x)` one.

## References

* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
* [Stacks Project, Tag 01YI](https://stacks.math.columbia.edu/tag/01YI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.GenericRankOneDevissage

/-- **The direct images of quasi-coherent ideals have the property, from conditions (1) and (2)
of [Stacks, Tag 01YI] alone.** For a property `P` of coherent modules on a Noetherian scheme `X`
which propagates along a short exact sequence of coherent modules from any two of its terms to
the third, and which holds for one coherent module supported exactly on each integral closed
subscheme, with generic stalk killed by the maximal ideal there and of length one over it, `P`
holds for the direct image of every quasi-coherent ideal `ℐ ⊆ 𝒪_Z` along the closed immersion of
every integral closed subscheme `Z ⟶ X`.

This is the Noetherian induction of [Stacks, Tag 01YI]: the criterion of [Stacks, Tag 01YH] at
the range of the immersion consumes the modules coming from the integral closed subschemes
strictly inside it, which are supplied by the inductive hypothesis. -/
theorem pushforward_ideal_property_of_genericRankOne (X : Scheme.{u}) [IsNoetherian X]
    (P : X.Modules → Prop)
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧
        (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁)))
    (hgeneric : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (ξ : X), IsGenericPoint ξ (Set.range i.base) →
      ∃ G : X.Modules, G.IsCoherent ∧
        SheafOfModules.supp G = Set.range i.base ∧
        Stacks.ClosedImmersion.StalkKilledByMaximalIdeal G ξ ∧
        (letI : Module (X.presheaf.stalk ξ) (G.presheaf.stalk ξ) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) G.val ξ
         Module.length (X.presheaf.stalk ξ) (G.presheaf.stalk ξ) = 1) ∧
        P G) :
    ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (H : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      H.toSheafOfModules.IsQuasicoherent →
      P ((Scheme.Modules.pushforward i).obj H.toSheafOfModules) := by
  classical
  let motive : Closeds X → Prop := fun C =>
    ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z],
      Set.range i.base = (C : Set X) →
      ∀ H : (SheafOfModules.unit Z.ringCatSheaf).Submodule,
        H.toSheafOfModules.IsQuasicoherent →
        P ((Scheme.Modules.pushforward i).obj H.toSheafOfModules)
  have hmotive : ∀ C : Closeds X, motive C := by
    intro C
    refine (wellFounded_lt : WellFounded (fun A B : Closeds X => A < B)).induction
      (C := motive) C ?_
    intro C ih Z i hi hZ hirange H hH
    have hclosed : IsClosed (Set.range i.base) := i.isClosedEmbedding.isClosed_range
    have hxi : IsGenericPoint (i.ker.subschemeι (genericPoint i.ker.subscheme))
        (Set.range i.base) :=
      CoherentDevissageGlue.isGenericPoint_toImage_genericPoint i
    have hirr : IsIrreducible (Set.range i.base) := hxi ▸ isIrreducible_singleton.closure
    have hproper : ∀ (Z' : Scheme.{u}) (i' : Z' ⟶ X) [IsClosedImmersion i']
        [IsIntegral Z'], Set.range i'.base ⊂ Set.range i.base →
        ∀ (I' : (SheafOfModules.unit Z'.ringCatSheaf).Submodule)
          [I'.toSheafOfModules.IsQuasicoherent],
          P ((Scheme.Modules.pushforward i').obj I'.toSheafOfModules) := by
      intro Z' i' hi' hZ' hlt I' hI'
      have hsub : Set.range i'.base ⊂ (C : Set X) := hirange ▸ hlt
      refine ih ⟨Set.range i'.base, i'.isClosedEmbedding.isClosed_range⟩ ?_ Z' i' rfl I' hI'
      exact lt_of_le_of_ne hsub.1 fun h =>
        hsub.2 (congrArg (fun D : Closeds X => (D : Set X)) h).symm.le
    exact IrreducibleSupportDevissage.property_of_irreducible_support X
      (Set.range i.base) hclosed hirr _ hxi P hexact hproper (hgeneric Z i _ hxi)
      ((Scheme.Modules.pushforward i).obj H.toSheafOfModules)
      (ClosedImmersionCoherentImage.isCoherent_pushforward_submodule_unit i H hH)
      (by
        refine (CoherentDevissageGlue.supp_pushforward_subset_support_ker i
          H.toSheafOfModules).trans ?_
        exact (Stacks.AffineClosedUnion.support_ker_eq_range i).le)
  intro Z i hi hZ H hH
  exact hmotive ⟨Set.range i.base, i.isClosedEmbedding.isClosed_range⟩ Z i rfl H hH

/-- **A two-out-of-three property of coherent modules which holds for one coherent module holds
for the zero module.** Apply condition (1) of [Stacks, Tag 01YI] to `0 → 𝒢 → 𝒢 → 0 → 0`, whose
outer two terms are `𝒢` and whose third term is the zero module. -/
theorem property_terminal_of_genericRankOne (X : Scheme.{u}) (P : X.Modules → Prop)
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧
        (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁)))
    {G : X.Modules} (hG : G.IsCoherent) (hP : P G) : P (⊤_ X.Modules) := by
  let T : X.Modules := ⊤_ X.Modules
  have hT : IsZero T := IsTerminal.isZero terminalIsTerminal
  let S : ShortComplex X.Modules := ShortComplex.mk (𝟙 G) (0 : G ⟶ T) (by simp [T])
  have hepi : Epi (0 : G ⟶ T) := ⟨fun f g _ => hT.eq_of_src f g⟩
  have hExact : S.Exact :=
    (S.exact_iff_epi (by change (0 : G ⟶ T) = 0; rfl)).2 (by dsimp [S]; infer_instance)
  have hShort : S.ShortExact := ShortComplex.ShortExact.mk' hExact
    (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance)
  have hparts := hexact S hShort hG hG CoherentDevissage.isCoherent_terminal
  simpa [S, T] using hparts.1 ⟨hP, hP⟩

/-- **The dévissage criterion of [Stacks, Tag 01YI], with the zero module added to its
hypotheses.** On a Noetherian scheme `X`, a property `P` of coherent modules which holds for the
zero module, propagates along a short exact sequence of coherent modules from any two of its
terms to the third, and holds for one coherent module supported exactly on each integral closed
subscheme with generic stalk killed by the maximal ideal there and of length one over it, holds
for every coherent module.

The criterion of [Stacks, Tag 01YG] reduces this to the direct images of quasi-coherent ideals
on integral closed subschemes, which is
`pushforward_ideal_property_of_genericRankOne`. The hypothesis on the zero module cannot be
dropped: on the empty scheme, which is Noetherian and has no integral closed subscheme, the
identically false property satisfies the other two hypotheses. -/
@[stacks 01YI "corrected: the source statement is false on the empty scheme, where condition (2)
is vacuous and the identically false property satisfies both hypotheses, so `P` on the zero
module is added"]
theorem property_of_genericRankOne (X : Scheme.{u}) [IsNoetherian X]
    (P : X.Modules → Prop) (hzero : P (⊤_ X.Modules))
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧
        (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁)))
    (hgeneric : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (ξ : X), IsGenericPoint ξ (Set.range i.base) →
      ∃ G : X.Modules, G.IsCoherent ∧
        SheafOfModules.supp G = Set.range i.base ∧
        Stacks.ClosedImmersion.StalkKilledByMaximalIdeal G ξ ∧
        (letI : Module (X.presheaf.stalk ξ) (G.presheaf.stalk ξ) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) G.val ξ
         Module.length (X.presheaf.stalk ξ) (G.presheaf.stalk ξ) = 1) ∧
        P G) :
    ∀ F : X.Modules, F.IsCoherent → P F := by
  refine CoherentDevissage.property_of_isCoherent X P hzero
    (fun S hS h1 h2 h3 hp1 hp3 => (hexact S hS h1 h2 h3).2.1 ⟨hp1, hp3⟩) ?_
  intro Z i hi hZ H hH
  exact pushforward_ideal_property_of_genericRankOne X P hexact hgeneric Z i H hH

/-- **The dévissage criterion of [Stacks, Tag 01YI], with one integral closed subscheme added to
its hypotheses.** On a Noetherian scheme carrying at least one integral closed subscheme, a
property `P` of coherent modules satisfying conditions (1) and (2) of [Stacks, Tag 01YI] holds
for every coherent module.

Condition (2) at that one subscheme produces a coherent module for which `P` holds, and
condition (1) then carries `P` to the zero module, so the hypothesis of
`property_of_genericRankOne` is met. The added hypothesis is implied by `Nonempty X` and
implies it, and it cannot be dropped: on the empty scheme the identically false property
satisfies conditions (1) and (2) and fails for the coherent zero module. -/
@[stacks 01YI "corrected: the source statement is false on the empty scheme, where condition (2)
is vacuous and the identically false property satisfies both hypotheses, so the existence of one
integral closed subscheme is added"]
theorem property_of_genericRankOne_of_exists_isIntegral (X : Scheme.{u}) [IsNoetherian X]
    (hne : ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧ IsIntegral Z)
    (P : X.Modules → Prop)
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧
        (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁)))
    (hgeneric : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (ξ : X), IsGenericPoint ξ (Set.range i.base) →
      ∃ G : X.Modules, G.IsCoherent ∧
        SheafOfModules.supp G = Set.range i.base ∧
        Stacks.ClosedImmersion.StalkKilledByMaximalIdeal G ξ ∧
        (letI : Module (X.presheaf.stalk ξ) (G.presheaf.stalk ξ) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := X.presheaf) G.val ξ
         Module.length (X.presheaf.stalk ξ) (G.presheaf.stalk ξ) = 1) ∧
        P G) :
    ∀ F : X.Modules, F.IsCoherent → P F := by
  obtain ⟨Z, i, hi, hZ⟩ := hne
  obtain ⟨G, hGc, -, -, -, hGP⟩ :=
    hgeneric Z i _ (CoherentDevissageGlue.isGenericPoint_toImage_genericPoint i)
  exact property_of_genericRankOne X P
    (property_terminal_of_genericRankOne X P hexact hGc hGP) hexact hgeneric

end Stacks.AlgebraicGeometry.GenericRankOneDevissage

end
