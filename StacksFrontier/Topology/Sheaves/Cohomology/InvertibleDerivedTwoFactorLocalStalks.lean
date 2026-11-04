module

public import Mathlib.Algebra.Field.ULift
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedLocalStalk

/-!
# A product decomposition with two nonzero factors over a space whose stalks are local rings

Clause (3) of Stacks 0FPG is stated under the hypothesis that every stalk `𝒪_{X, x}` is a local
ring, and the statements of
`StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedLocalStalk` quantify over a
`ProductDecomposition` *and* that hypothesis. Each was separately witnessed and the pair was not:
`InvertibleDerivedTwoFactorWitness.witnessDecomposition` has two nonzero factors but lives on a
one-point space, where the structure sheaf is `ℤ × ℤ` and the single stalk is not local — indeed
`not_exists_nhd_unique_factor_witness` uses exactly that. This file witnesses the two together.

The space is the **two-point discrete space** with `ℚ` concentrated at each point: the factor in
degree `0` is the skyscraper of `ℚ` at `p₀`, the factor in degree `1` the skyscraper of `ℚ` at
`p₁`, and the zero ring in every other degree. Each point has a smallest open neighbourhood, its
own singleton, on which only one factor has sections, so each stalk is `ℚ` — a field, hence a
local ring — while both factors are nonzero.

## Main results

* `Stacks.Cohomology.isLocalRing_stalk_of_isMin`: **the stalk at a point with a smallest open
  neighbourhood `U` is a local ring as soon as `𝒪(U)` is**. Proved through surjectivity of the
  germ, not through any computation of the stalk as a limit.
* `...TwoFactorWitness.isLocalRing_sections_of_subsingleton`: where one factor survives, the ring
  of sections of the structure sheaf is a local ring as soon as that factor's is.
* `...TwoFactorWitness.localStalkWitnessDecomposition`: the decomposition.
* `...TwoFactorWitness.isLocalRing_stalk_localStalkWitness`: **every** stalk of its structure
  sheaf is a local ring.
* `...TwoFactorWitness.not_offDiagonallyDegenerate_localStalkWitnessDecomposition`: and it is not
  off-diagonally degenerate — both factors have sections.
* `...TwoFactorWitness.exists_localStalks_not_offDiagonallyDegenerate`: the two together, as the
  single statement that the joint datum of
  `ProductDecomposition.exists_nhd_unique_factor` and `exists_cover_restrict_iso_single` has a
  non-degenerate inhabitant.

## Implementation notes

`surjective_germ_of_isMin` needs no minimality beyond `U ≤ V` for every open `V` containing the
point, which a singleton in a discrete space satisfies; `nontrivial_stalk_of_isMin` then forces
any open on which the germ of `1` and the germ of `0` agree to be `U` itself, so `1 = 0` would
already hold in `𝒪(U)`. Neither statement computes `𝒪_{X, x}`, and in particular neither needs
the stalk of a product of sheaves of rings to be the product of the stalks — the lemma that the
module docstring of `InvertibleDerivedObjects` used to claim the clause-(3) equivalence waits on.

The ring of sections of the structure sheaf over a singleton is identified with the surviving
factor by `ProductDecomposition.isIso_compHom_of_subsingleton`, which is the general statement
that where one factor survives the structure sheaf *is* that factor.

Statements about the skyscraper factors are proved first in the spelling that mentions only the
topological space `T` and then transported to the decomposition's spelling by a single `exact`:
the two spellings of the site, `Opens.grothendieckTopology T` and
`Opens.grothendieckTopology (twoFactorSpace p₀ p₁ R S).carrier`, are definitionally equal but a
`rw` across them leaves a term that is not type-correct at `implicit` transparency.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules.RingSheafProductFactor

universe u

namespace Stacks.Cohomology

/-! ### Stalks at a point with a smallest open neighbourhood -/

/-- **The germ over a smallest open neighbourhood is surjective.** Every element of the stalk is
the germ of a section over some neighbourhood `V` of `x`, and `U ≤ V`, so restricting that
section to `U` gives a preimage. -/
public theorem surjective_germ_of_isMin {T : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} T)
    (x : T) (U : Opens T) (hxU : x ∈ U) (hmin : ∀ V : Opens T, x ∈ V → U ≤ V) :
    Function.Surjective (F.germ U x hxU).hom := by
  intro t
  obtain ⟨V, hxV, s, hs⟩ := F.exists_germ_eq t
  refine ⟨F.map (homOfLE (hmin V hxV)).op s, ?_⟩
  rw [← hs]
  exact F.germ_res_apply (homOfLE (hmin V hxV)) x hxU s

/-- **The stalk at a point with a smallest open neighbourhood `U` is nontrivial as soon as
`𝒪(U)` is.** If the germs of `1` and `0` agreed, they would already agree over some
neighbourhood of `x`, which minimality forces to be `U`. -/
public theorem nontrivial_stalk_of_isMin {T : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} T)
    (x : T) (U : Opens T) (hxU : x ∈ U) (hmin : ∀ V : Opens T, x ∈ V → U ≤ V)
    [Nontrivial (F.obj (op U))] :
    Nontrivial (F.stalk x) := by
  refine ⟨⟨F.germ U x hxU 1, F.germ U x hxU 0, fun h => ?_⟩⟩
  obtain ⟨W, hxW, iU, iV, hW⟩ := F.germ_eq x hxU hxU (1 : F.obj (op U)) 0 h
  have hWU : W = U := le_antisymm (leOfHom iU) (hmin W hxW)
  subst hWU
  rw [map_one, map_zero] at hW
  exact one_ne_zero hW

/-- **The stalk at a point with a smallest open neighbourhood `U` is a local ring as soon as
`𝒪(U)` is**: the germ is a surjective ring homomorphism out of a local ring onto a nontrivial
ring. -/
public theorem isLocalRing_stalk_of_isMin {T : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} T)
    (x : T) (U : Opens T) (hxU : x ∈ U) (hmin : ∀ V : Opens T, x ∈ V → U ≤ V)
    [IsLocalRing (F.obj (op U))] :
    IsLocalRing (F.stalk x) :=
  have : Nontrivial (F.stalk x) := nontrivial_stalk_of_isMin F x U hxU hmin
  IsLocalRing.of_surjective' (F.germ U x hxU).hom (surjective_germ_of_isMin F x U hxU hmin)

namespace InvertibleDerived.TwoFactorWitness

/-! ### Where one factor survives, the sections of the structure sheaf are that factor -/

/-- **The ring of sections of the structure sheaf is a local ring where one factor survives and
that factor's sections form one.** The `n₀`-th component map is an isomorphism of the rings of
sections (`ProductDecomposition.isIso_compHom_of_subsingleton`), and a local ring transports
along the inverse. -/
public theorem isLocalRing_sections_of_subsingleton {X : RingedSpace.{u, u}}
    (D : InvertibleDerived.ProductDecomposition X) {n₀ : ℤ} {V : Opens X.carrier}
    (hsub : ∀ n, n ≠ n₀ → Subsingleton ((D.factor n).obj.obj (op V)))
    [IsLocalRing ((D.factor n₀).obj.obj (op V))] :
    IsLocalRing (X.presheaf.obj (op V)) := by
  have := D.isIso_compHom_of_subsingleton hsub (le_refl V)
  have hbij := (ConcreteCategory.isIso_iff_bijective (D.compHom n₀ (op V))).mp inferInstance
  have : Nontrivial (X.presheaf.obj (op V)) := hbij.surjective.nontrivial
  exact IsLocalRing.of_surjective' (asIso (D.compHom n₀ (op V))).inv.hom
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).surjective

/-! ### The skyscraper factors -/

variable {T : TopCat.{u}} (p₀ p₁ : T) (R S : CommRingCat.{u})

/-- Off its point the skyscraper sheaf of rings has no sections beyond zero: its value there is a
terminal object of `CommRingCat`. -/
public theorem subsingleton_skyscraperRingSheaf_obj_of_notMem {U : Opens T} (hU : p₀ ∉ U) :
    Subsingleton ((skyscraperRingSheaf p₀ R).obj.obj (op U)) := by
  classical
  have he : (skyscraperRingSheaf p₀ R).obj.obj (op U) = ⊤_ CommRingCat.{u} := by
    dsimp only [skyscraperRingSheaf, skyscraperSheaf, skyscraperPresheaf]
    simp [hU]
  rw [he]
  have := Concrete.uniqueOfTerminalOfPreserves (⊤_ CommRingCat.{u})
    (terminalIsTerminal (C := CommRingCat.{u}))
  infer_instance

/-- At its point the sections of the skyscraper sheaf of a local ring form a local ring. -/
public theorem isLocalRing_skyscraperRingSheaf_obj_of_mem [IsLocalRing R] {U : Opens T}
    (hU : p₀ ∈ U) :
    IsLocalRing ((skyscraperRingSheaf p₀ R).obj.obj (op U)) := by
  rw [skyscraperRingSheaf_obj_of_mem p₀ R hU]
  infer_instance

/-- Over an open set containing `p₀` but not `p₁`, every factor of the two-factor decomposition
other than the degree-zero one has no sections. -/
public theorem subsingleton_twoFactor_of_ne_zero {U : Opens T} (h1 : p₁ ∉ U) {n : ℤ}
    (hn : n ≠ 0) :
    Subsingleton (((twoFactorDecomposition p₀ p₁ R S).factor n).obj.obj (op U)) := by
  by_cases hn1 : n = 1
  · subst hn1
    exact subsingleton_skyscraperRingSheaf_obj_of_notMem p₁ S h1
  · exact subsingleton_twoFactorFamily_of_ne p₀ p₁ R S hn hn1 (op U)

/-- Over an open set containing `p₁` but not `p₀`, every factor other than the degree-one one has
no sections. -/
public theorem subsingleton_twoFactor_of_ne_one {U : Opens T} (h0 : p₀ ∉ U) {n : ℤ}
    (hn : n ≠ 1) :
    Subsingleton (((twoFactorDecomposition p₀ p₁ R S).factor n).obj.obj (op U)) := by
  by_cases hn0 : n = 0
  · subst hn0
    exact subsingleton_skyscraperRingSheaf_obj_of_notMem p₀ R h0
  · exact subsingleton_twoFactorFamily_of_ne p₀ p₁ R S hn0 hn (op U)

/-- At `p₀` the sections of the degree-zero factor of a local ring form a local ring. -/
public theorem isLocalRing_twoFactor_zero [IsLocalRing R] {U : Opens T} (hU : p₀ ∈ U) :
    IsLocalRing (((twoFactorDecomposition p₀ p₁ R S).factor 0).obj.obj (op U)) := by
  exact isLocalRing_skyscraperRingSheaf_obj_of_mem p₀ R hU

/-- At `p₁` the sections of the degree-one factor of a local ring form a local ring. -/
public theorem isLocalRing_twoFactor_one [IsLocalRing S] {U : Opens T} (hU : p₁ ∈ U) :
    IsLocalRing (((twoFactorDecomposition p₀ p₁ R S).factor 1).obj.obj (op U)) := by
  exact isLocalRing_skyscraperRingSheaf_obj_of_mem p₁ S hU

/-! ### The two-point discrete witness -/

/-- The two-point discrete space. -/
public abbrev twoPointTop : TopCat.{u} := TopCat.discrete.obj (ULift.{u} Bool)

/-- The first of the two points. -/
public abbrev pt₀ : twoPointTop.{u} := ULift.up false

/-- The second of the two points. -/
public abbrev pt₁ : twoPointTop.{u} := ULift.up true

/-- The rationals, as an object of `CommRingCat`; a field, hence a local ring. -/
public abbrev ratField : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℚ)

/-- `ratField` is a local ring, being a field. -/
public instance : IsLocalRing (ratField.{u}) :=
  inferInstanceAs (IsLocalRing (ULift.{u} ℚ))

/-- `ratField` is nontrivial. -/
public instance : Nontrivial (ratField.{u}) :=
  inferInstanceAs (Nontrivial (ULift.{u} ℚ))

/-- The two points of the two-point space are distinct. -/
public theorem pt₀_ne_pt₁ : pt₀.{u} ≠ pt₁.{u} := fun h =>
  absurd (congrArg ULift.down h) (by decide)

/-- **The ringed space of the joint witness**: the two-point discrete space, with `ℚ` at each
point. -/
public abbrev localStalkWitnessSpace : RingedSpace.{u, u} :=
  twoFactorSpace pt₀.{u} pt₁.{u} ratField.{u} ratField.{u}

/-- **A product decomposition with two nonzero factors over a space all of whose stalks are local
rings.** -/
public abbrev localStalkWitnessDecomposition :
    InvertibleDerived.ProductDecomposition localStalkWitnessSpace.{u} :=
  twoFactorDecomposition pt₀.{u} pt₁.{u} ratField.{u} ratField.{u}

/-- The singleton of a point of the two-point discrete space, as an open set. -/
public abbrev ptOpen (x : twoPointTop.{u}) : Opens twoPointTop.{u} :=
  ⟨{x}, isOpen_discrete _⟩

/-- A point lies in its own singleton open. -/
public theorem mem_ptOpen (x : twoPointTop.{u}) : x ∈ ptOpen x := rfl

/-- The singleton of a point is its smallest open neighbourhood. -/
public theorem ptOpen_isMin (x : twoPointTop.{u}) (V : Opens twoPointTop.{u}) (hxV : x ∈ V) :
    ptOpen x ≤ V := Set.singleton_subset_iff.mpr hxV

/-- Every point of the two-point space is `pt₀` or `pt₁`. -/
public theorem eq_pt₀_or_pt₁ (x : twoPointTop.{u}) : x = pt₀.{u} ∨ x = pt₁.{u} := by
  cases x with
  | up b => cases b
            · exact Or.inl rfl
            · exact Or.inr rfl

/-- **Every stalk of the witness space is a local ring.** The singleton of a point is its
smallest open neighbourhood; over it only one factor survives, so the sections of the structure
sheaf there are `ℚ`. -/
public theorem isLocalRing_stalk_localStalkWitness (x : twoPointTop.{u}) :
    IsLocalRing (localStalkWitnessSpace.{u}.presheaf.stalk x) := by
  have key : IsLocalRing (localStalkWitnessSpace.{u}.presheaf.obj (op (ptOpen x))) := by
    rcases eq_pt₀_or_pt₁ x with h | h
    · subst h
      have := isLocalRing_twoFactor_zero pt₀.{u} pt₁.{u} ratField.{u} ratField.{u}
        (mem_ptOpen pt₀.{u})
      exact isLocalRing_sections_of_subsingleton localStalkWitnessDecomposition.{u}
        (fun n hn => subsingleton_twoFactor_of_ne_zero pt₀.{u} pt₁.{u} ratField.{u} ratField.{u}
          (fun hmem => pt₀_ne_pt₁.{u} (Set.eq_of_mem_singleton hmem).symm) hn)
    · subst h
      have := isLocalRing_twoFactor_one pt₀.{u} pt₁.{u} ratField.{u} ratField.{u}
        (mem_ptOpen pt₁.{u})
      exact isLocalRing_sections_of_subsingleton localStalkWitnessDecomposition.{u}
        (fun n hn => subsingleton_twoFactor_of_ne_one pt₀.{u} pt₁.{u} ratField.{u} ratField.{u}
          (fun hmem => pt₀_ne_pt₁.{u} (Set.eq_of_mem_singleton hmem)) hn)
  exact isLocalRing_stalk_of_isMin localStalkWitnessSpace.{u}.presheaf x (ptOpen x)
    (mem_ptOpen x) (ptOpen_isMin x)

/-- **The witness decomposition is not off-diagonally degenerate**: both factors have sections,
the degree-zero one at `pt₀` and the degree-one one at `pt₁`. -/
public theorem not_offDiagonallyDegenerate_localStalkWitnessDecomposition :
    ¬ OffDiagonallyDegenerate localStalkWitnessDecomposition.{u} :=
  not_offDiagonallyDegenerate_twoFactorDecomposition _ _ _ _

/-- **The joint datum of `ProductDecomposition.exists_nhd_unique_factor` and
`exists_cover_restrict_iso_single` has a non-degenerate inhabitant**: a ringed space all of whose
stalks are local rings, carrying a locally finite direct product decomposition of its structure
sheaf which is not off-diagonally degenerate. -/
public theorem exists_localStalks_not_offDiagonallyDegenerate :
    ∃ (X : RingedSpace.{u, u}) (D : InvertibleDerived.ProductDecomposition X),
      (∀ x : X.carrier, IsLocalRing (X.presheaf.stalk x)) ∧
        ¬ OffDiagonallyDegenerate D :=
  ⟨localStalkWitnessSpace.{u}, localStalkWitnessDecomposition.{u},
    isLocalRing_stalk_localStalkWitness.{u},
    not_offDiagonallyDegenerate_localStalkWitnessDecomposition.{u}⟩

end InvertibleDerived.TwoFactorWitness

end Stacks.Cohomology

end
