module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ValuationGermDeath

/-!
# Germ death at the centers of small rank, from germ death at valuation rings

This file proves the Zariski–Riemann step of Gabber's germ-killing argument (Travaux de Gabber,
Exposé XVIII-A, last remark of §2): `AlgebraicGeometry.Scheme.ZariskiRiemann.ValuationGermDeath n`
implies `AlgebraicGeometry.Scheme.ZariskiRiemann.CenteredGermDeath n`, given the cofilteredness of
the proper models and a list of standard inputs, each stated as a separate proposition.

Let `M` be a proper model with `G = R^q j_* F`, `U ⟶ Y` étale, `g ∈ G(U)` and `w ∈ U` over a point
`y` of the closed fibre at which every centered valuation ring has rational rank `< q`. For a
refinement `π : Y' ⟶ Y`, a geometric point `s` of `Y'` and a lift `ℓ` of `s ≫ π` to `U`, the
germ of `g` at `ℓ` **dies at `s`**
(`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.DeadAt`) if its image under the
transition map of stalks vanishes. The **dead set**
(`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.deadSet`) is the set of points of
`U ×_Y Y'` having an open neighbourhood all of whose geometric points carry dying germs; it is
open by construction.

The argument:

1. For each valuation ring `V` centered at `y`, a geometric point `v` of `Spec V` at the closed
   point has finitely many lifts `ℓ` of `v ≫ c_Y` to `U` at `w`
   (`AlgebraicGeometry.Scheme.ZariskiRiemann.FiniteLiftsAtPoint`); germ death at `V`
   (`ValuationGermDeath`) kills each of their germs on a refinement, and a common refinement
   `Y_V` kills all of them. Every point of `U ×_Y Y_V` over `w` and `c_{Y_V}(V)` carries such a
   geometric point (Mathlib's `AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed`), so
   lies in the dead set (`AlgebraicGeometry.Scheme.ZariskiRiemann.GermDeathSpreads`). The dead set
   is open, so it contains all points over `w` and `y'` for `y'` in an open neighbourhood `N_V` of
   `c_{Y_V}(V)` in the fibre over `y`
   (`AlgebraicGeometry.Scheme.ZariskiRiemann.FibreOpenOverEtale`), and the valuation rings whose
   center on `Y_V` lies in `N_V` contain a basic open set of the Zariski–Riemann space
   (`AlgebraicGeometry.Scheme.ZariskiRiemann.CenterOpenBasic`).
2. The Zariski–Riemann fibre over `y` is quasi-compact
   (`AlgebraicGeometry.Scheme.ZariskiRiemann.ZariskiRiemannFibreQuasiCompact`): finitely many `V`
   suffice, with one common refinement `Y''`.
3. Every point of `U ×_Y Y''` over `w` is dead: over a point outside the closure of `j''(η)` the
   stalks vanish (`AlgebraicGeometry.Scheme.ZariskiRiemann.StalkZeroOffClosure`); a point in the
   closure is the center of a valuation ring centered at `y`
   (`AlgebraicGeometry.Scheme.ZariskiRiemann.ExistsValuationCenter`), which lies in one of the
   finitely many basic sets, and death is stable under refinement
   (`AlgebraicGeometry.Scheme.ZariskiRiemann.DeadAtStableUnderRefinement`).
4. The complement of the dead set is closed and `U ×_Y Y'' ⟶ U` is proper, so its image `Z` is
   closed and misses `w`; on `W = U ∖ Z` every germ dies at every geometric point, so the
   refinement kills `g|W` (`AlgebraicGeometry.Scheme.ZariskiRiemann.KillsOfForallDeadAt`).

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.DeadAt`
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.germPoint`
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.deadSet`
* the input statements `GermDeathSpreads`, `StalkZeroOffClosure`, `DeadAtStableUnderRefinement`,
  `KillsOfForallDeadAt`, `FibreOpenOverEtale`, `ExistsValuationCenter`, `CenterOpenBasic`,
  `FiniteLiftsAtPoint`, `ZariskiRiemannFibreQuasiCompact` (in
  `AlgebraicGeometry.Scheme.ZariskiRiemann`)

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.exists_refinement_factoring_all` — finitely
  many refinements of a model have a common refinement.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.centeredGermDeath_of_valuationGermDeath`

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* O. Zariski, P. Samuel, *Commutative Algebra*, Vol. II, Chapter VI, §17
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

open Stacks.EtaleCohomology

/-- The morphism `Spec Ω ⟶ U` of a lift `ℓ` of a geometric point `t` of `Y` to an étale `U ⟶ Y`
(an element of the fibre of the point of the small étale site defined by `t`). -/
def etaleLiftHom {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {t : Spec (.of Ω) ⟶ Y} {U : Y.Etale} (ℓ : (Scheme.pointSmallEtale t).fiber.obj U) :
    Spec (.of Ω) ⟶ U.left :=
  ℓ.left

/-- A lift of `t` to `U` lies over `t`. -/
@[reassoc]
theorem etaleLiftHom_comp {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {t : Spec (.of Ω) ⟶ Y} {U : Y.Etale} (ℓ : (Scheme.pointSmallEtale t).fiber.obj U) :
    etaleLiftHom ℓ ≫ U.hom = t :=
  Over.w ℓ

/-- The lift along `h : W ⟶ U` of a lift to `W` is the lift to `U` of the composite. -/
theorem etaleLiftHom_map {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {t : Spec (.of Ω) ⟶ Y} {W U : Y.Etale} (h : W ⟶ U)
    (ℓ : (Scheme.pointSmallEtale t).fiber.obj W) :
    etaleLiftHom ((Scheme.pointSmallEtale t).fiber.map h ℓ) = etaleLiftHom ℓ ≫ h.left :=
  rfl

namespace ProperModel

variable {B : Type u} [CommRing B] [IsDomain B]

/-- **A germ dying at a geometric point of a refinement.** For a refinement `π : Y' ⟶ Y`, an étale
`U ⟶ Y`, `g ∈ (R^q j_* F)(U)`, a geometric point `s` of `Y'` and a lift `ℓ` of `t = s ≫ π` to
`U`, the image of the germ of `g` at `(U, ℓ)` under the transition map
`(R^q j_* F)_{s ≫ π} ⟶ (R^q j'_* F)_s` vanishes. -/
def Refinement.DeadAt {M' M : ProperModel B} (φ : Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (U : M.Y.Etale)
    (g : (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.obj (op U))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ M'.Y)
    {t : Spec (.of Ω) ⟶ M.Y} (ht : s ≫ φ.π = t) (ℓ : (Scheme.pointSmallEtale t).fiber.obj U) :
    Prop :=
  (eqToHom (show (smallEtaleStalkAb t).obj
        (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) =
      (smallEtaleStalkAb (s ≫ φ.π)).obj
        (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) by rw [ht]) ≫
    φ.stalkTransition F q s)
    ((Scheme.pointSmallEtale t).toPresheafFiber U ℓ
      (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj g :
      (smallEtaleStalkAb t).obj (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F)) = 0

/-- The point of `U ×_Y Y'` of a geometric point `s` of `Y'` with a lift `ℓ` of `s ≫ π` to `U`. -/
def Refinement.germPoint {M' M : ProperModel B} (φ : Refinement M' M) (U : M.Y.Etale)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ M'.Y)
    {t : Spec (.of Ω) ⟶ M.Y} (ht : s ≫ φ.π = t) (ℓ : (Scheme.pointSmallEtale t).fiber.obj U) :
    ↥(pullback U.hom φ.π) :=
  pullback.lift (etaleLiftHom ℓ) s (by rw [ht]; exact etaleLiftHom_comp ℓ) (default : Spec (.of Ω))

/-- **The dead set** of `g` on a refinement: the points of `U ×_Y Y'` with an open
neighbourhood at all of whose geometric points the germ of `g` dies. -/
def Refinement.deadSet {M' M : ProperModel B} (φ : Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (U : M.Y.Etale)
    (g : (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.obj (op U)) :
    Set ↥(pullback U.hom φ.π) :=
  {u' | ∃ O : Set ↥(pullback U.hom φ.π), IsOpen O ∧ u' ∈ O ∧
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ M'.Y)
      (t : Spec (.of Ω) ⟶ M.Y) (ht : s ≫ φ.π = t) (ℓ : (Scheme.pointSmallEtale t).fiber.obj U),
      φ.germPoint U s ht ℓ ∈ O → φ.DeadAt F q U g s ht ℓ}

omit [IsDomain B] in
/-- The dead set is open. -/
theorem Refinement.isOpen_deadSet {M' M : ProperModel B} (φ : Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (U : M.Y.Etale)
    (g : (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.obj (op U)) :
    IsOpen (φ.deadSet F q U g) :=
  isOpen_iff_forall_mem_open.2 fun _ ⟨O, hO, huO, hall⟩ ↦
    ⟨O, fun _ hu' ↦ ⟨O, hO, hu', hall⟩, hO, huO⟩

omit [IsDomain B] in
/-- Death at a geometric point only depends on the refinement up to equality. -/
theorem Refinement.DeadAt.of_eq {M' M : ProperModel B} {φ φ' : Refinement M' M} (h : φ = φ')
    {F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}} {q : ℕ}
    {U : M.Y.Etale}
    {g : (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.obj (op U)}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] {s : Spec (.of Ω) ⟶ M'.Y}
    {t : Spec (.of Ω) ⟶ M.Y} {ht : s ≫ φ.π = t} {ht' : s ≫ φ'.π = t}
    {ℓ : (Scheme.pointSmallEtale t).fiber.obj U} (hd : φ.DeadAt F q U g s ht ℓ) :
    φ'.DeadAt F q U g s ht' ℓ := by
  subst h
  exact hd

omit [IsDomain B] in
/-- Death of the germ of a restriction `g|W` at a lift `ℓ` to `W` is death of the germ of `g` at
the composite lift to `U`. -/
theorem Refinement.deadAt_map_iff {M' M : ProperModel B} (φ : Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    {W U : M.Y.Etale} (h : W ⟶ U)
    (g : (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.obj (op U))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ M'.Y)
    {t : Spec (.of Ω) ⟶ M.Y} (ht : s ≫ φ.π = t) (ℓ : (Scheme.pointSmallEtale t).fiber.obj W) :
    φ.DeadAt F q W ((((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.map h.op g)
        s ht ℓ ↔
      φ.DeadAt F q U g s ht ((Scheme.pointSmallEtale t).fiber.map h ℓ) := by
  unfold Refinement.DeadAt
  rw [GrothendieckTopology.Point.toPresheafFiber_w_apply]

/-- **Finitely many refinements of a model have a common refinement**, given that two always do. -/
theorem exists_refinement_factoring_all (hcof : RefinementsCofiltered B) (M : ProperModel B)
    {J : Type*} [Finite J] (M₁ : J → ProperModel B) (φ : ∀ j, Refinement (M₁ j) M) :
    ∃ (M'' : ProperModel B) (ψ : Refinement M'' M),
      ∀ j, ∃ ρ : Refinement M'' (M₁ j), ρ.comp (φ j) = ψ := by
  classical
  have := Fintype.ofFinite J
  suffices h : ∀ T : Finset J, ∃ (M'' : ProperModel B) (ψ : Refinement M'' M),
      ∀ j ∈ T, ∃ ρ : Refinement M'' (M₁ j), ρ.comp (φ j) = ψ by
    obtain ⟨M'', ψ, hψ⟩ := h Finset.univ
    exact ⟨M'', ψ, fun j ↦ hψ j (Finset.mem_univ j)⟩
  intro T
  induction T using Finset.induction_on with
  | empty => exact ⟨M, Refinement.id M, fun j hj ↦ absurd hj (Finset.notMem_empty j)⟩
  | insert j T _ ih =>
    obtain ⟨M₂, ψ, hψ⟩ := ih
    obtain ⟨M₃, ρ₁, ρ₂, hρ⟩ := hcof M₂ (M₁ j) M ψ (φ j)
    refine ⟨M₃, ρ₁.comp ψ, fun i hi ↦ ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨ρ₂, Refinement.ext hρ.symm⟩
    · obtain ⟨ρ, rfl⟩ := hψ i hi
      refine ⟨ρ₁.comp ρ, Refinement.ext ?_⟩
      change (ρ₁.π ≫ ρ.π) ≫ (φ i).π = ρ₁.π ≫ (ρ.π ≫ (φ i).π)
      rw [Category.assoc]

end ProperModel

/-- **A dying germ dies on a neighbourhood** (the support of a section of an étale sheaf is
closed). If the germ of `g` dies at a geometric point `(s, ℓ)` of `U ×_Y Y'`, the point of
`U ×_Y Y'` it defines lies in the dead set. In the source: the image of the germ is the germ of the
pulled back section of `R^q j'_* F` over `U ×_Y Y'`; it vanishes on an étale neighbourhood `E`,
whose image is open, and every geometric point of that image lifts to `E`. -/
def GermDeathSpreads : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B] (M' M : ProperModel B)
    (φ : ProperModel.Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (U : M.Y.Etale)
    (g : (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.obj (op U))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ M'.Y) (t : Spec (.of Ω) ⟶ M.Y)
    (ht : s ≫ φ.π = t) (ℓ : (Scheme.pointSmallEtale t).fiber.obj U),
    φ.DeadAt F q U g s ht ℓ → φ.germPoint U s ht ℓ ∈ φ.deadSet F q U g

/-- **`R^q j_* F` vanishes off the closure of `j(η)`**: its stalk at a geometric point of a
model whose image is not in the closure of the image of `j` is zero (`η ×_Y Spec 𝒪^{sh}` is
empty there). -/
def StalkZeroOffClosure : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B] (M : ProperModel B)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ M.Y),
    s (default : Spec (.of Ω)) ∉ closure (Set.range M.j) →
      IsZero ((smallEtaleStalkAb s).obj
        (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F))

/-- **Death is stable under further refinement**, at stalks: the transition map of a composite
refinement `Y'' ⟶ Y' ⟶ Y` at `s` factors through the transition map of `Y' ⟶ Y` at the image of
`s` (the stalk form of the cocycle condition behind
`AlgebraicGeometry.Scheme.ZariskiRiemann.killsStableUnderRefinement`). -/
def DeadAtStableUnderRefinement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B] (M'' M' M : ProperModel B)
    (ψ : ProperModel.Refinement M'' M') (φ : ProperModel.Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (U : M.Y.Etale)
    (g : (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.obj (op U))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ M''.Y) (s' : Spec (.of Ω) ⟶ M'.Y)
    (_ : s ≫ ψ.π = s') (t : Spec (.of Ω) ⟶ M.Y) (ht : s' ≫ φ.π = t)
    (ht' : s ≫ (ψ.comp φ).π = t) (ℓ : (Scheme.pointSmallEtale t).fiber.obj U),
    φ.DeadAt F q U g s' ht ℓ → (ψ.comp φ).DeadAt F q U g s ht' ℓ

/-- **Killing is checked on germs**: a refinement kills the morphism `ℤ_W ⟶ R^q j_* F` of a
section `h` as soon as every germ of `h` dies at every geometric point (the stalk of
`π⁻¹ ℤ_W` at `s` is generated by the lifts of `s ≫ π` to `W`; with
`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.kills_iff_forall_stalk`). -/
def KillsOfForallDeadAt : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B] (M' M : ProperModel B)
    (φ : ProperModel.Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (W : M.Y.Etale)
    (h : (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.obj (op W)),
    (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ M'.Y)
      (ℓ : (Scheme.pointSmallEtale (s ≫ φ.π)).fiber.obj W), φ.DeadAt F q W h s rfl ℓ) →
    φ.Kills F q (ProperModel.germHom W h)

/-- **Open sets of `U ×_Y Y'` along the fibre over a point of `U`.** For `U ⟶ Y` étale, any
`π : Y' ⟶ Y`, an open `O ⊆ U ×_Y Y'` and `w ∈ U`: if `O` contains every point over `w` and `y₀`,
then it contains every point over `w` and `y'`, for all `y'` in some open neighbourhood of `y₀`
in the fibre of `π` through `y₀`. (The points over `w` form `Spec κ(w) ×_Y Y'`, which is finite
over the fibre of `Y'` over the image of `w`, hence maps closed sets to closed sets.) -/
def FibreOpenOverEtale : Prop :=
  ∀ {Y Y' : Scheme.{u}} (π : Y' ⟶ Y) (U : Y.Etale) (O : Set ↥(pullback U.hom π)), IsOpen O →
    ∀ (w : ↥U.left) (y₀ : ↥Y'),
      (∀ u' : ↥(pullback U.hom π), pullback.fst U.hom π u' = w →
        pullback.snd U.hom π u' = y₀ → u' ∈ O) →
      ∃ N : Set ↥Y', IsOpen N ∧ y₀ ∈ N ∧ ∀ y' ∈ N, π y' = π y₀ →
        ∀ u' : ↥(pullback U.hom π), pullback.fst U.hom π u' = w →
          pullback.snd U.hom π u' = y' → u' ∈ O

/-- **Points in the closure of `j(η)` are centers**: a point `y` of a proper model over the
closed point of the local domain `B`, in the closure of the image of `j`, is the center of a
valuation ring of `Frac B` dominating `B` (a valuation ring dominating the image of `𝒪_{Y,y}` in
`Frac B`). -/
def ExistsValuationCenter : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B] [IsLocalRing B] (M : ProperModel B) (y : ↥M.Y),
    y ∈ closure (Set.range M.j) → M.f y = IsLocalRing.closedPoint B →
    ∃ (V : ValuationSubring (FractionRing B))
      (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V),
      IsLocalHom (valuationSubringBaseMap V hV) ∧ M.centerPoint V hV = y

/-- **The center map is continuous for the Zariski–Riemann topology**: if the center of `V` on a
model lies in an open `N`, there is a finite subset `S ⊆ V` of `Frac B` (generators of an affine
open neighbourhood of the center inside `N`) such that every valuation ring containing `B` and
`S` has its center in `N`. -/
def CenterOpenBasic : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B] (M : ProperModel B)
    (V : ValuationSubring (FractionRing B)) (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V)
    (N : Set ↥M.Y), IsOpen N → M.centerPoint V hV ∈ N →
    ∃ S : Finset (FractionRing B), (∀ x ∈ S, x ∈ V) ∧
      ∀ (V' : ValuationSubring (FractionRing B))
        (hV' : ∀ b : B, algebraMap B (FractionRing B) b ∈ V'),
        (∀ x ∈ S, x ∈ V') → M.centerPoint V' hV' ∈ N

/-- **Finitely many lifts at a point**: for `U ⟶ Y` étale, a geometric point `t` of `Y` and
`w ∈ U`, the lifts of `t` to `U` through `w` are finite in number (they correspond to
`κ(t(pt))`-embeddings of the finite separable extension `κ(w)` into `Ω`). -/
def FiniteLiftsAtPoint : Prop :=
  ∀ {Y : Scheme.{u}} (U : Y.Etale) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ Y) (w : ↥U.left),
    {ℓ : (Scheme.pointSmallEtale t).fiber.obj U |
      etaleLiftHom ℓ (default : Spec (.of Ω)) = w}.Finite

/-- **The Zariski–Riemann fibre over a point is quasi-compact**, for covers by basic open sets:
if each valuation ring of `Frac B` dominating the local domain `B` and centered at `y` contains one
of the finite sets `S i`, finitely many of the `S i` suffice. -/
def ZariskiRiemannFibreQuasiCompact : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B] [IsLocalRing B] (M : ProperModel B) (y : ↥M.Y)
    {I : Type u} (S : I → Finset (FractionRing B)),
    (∀ (V : ValuationSubring (FractionRing B))
      (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V),
      IsLocalHom (valuationSubringBaseMap V hV) → M.centerPoint V hV = y →
      ∃ i, ∀ x ∈ S i, x ∈ V) →
    ∃ J : Finset I, ∀ (V : ValuationSubring (FractionRing B))
      (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V),
      IsLocalHom (valuationSubringBaseMap V hV) → M.centerPoint V hV = y →
      ∃ i ∈ J, ∀ x ∈ S i, x ∈ V

/-- An element of a zero abelian group is zero. -/
private theorem eq_zero_of_isZero_addCommGrpCat {A : AddCommGrpCat.{u + 1}} (hA : IsZero A)
    (x : A) : x = 0 := by
  have h : (𝟙 A : A ⟶ A) = 0 := hA.eq_of_src _ _
  simpa using congrArg (fun f : A ⟶ A ↦ f x) h

/-- **Germ death at the centers of small rank from germ death at valuation rings** (the
Zariski–Riemann step of Exposé XVIII-A, last remark of §2), given the cofilteredness of the proper
models and the inputs `GermDeathSpreads`, `StalkZeroOffClosure`, `DeadAtStableUnderRefinement`,
`KillsOfForallDeadAt`, `FibreOpenOverEtale`, `ExistsValuationCenter`, `CenterOpenBasic`,
`FiniteLiftsAtPoint` and `ZariskiRiemannFibreQuasiCompact`. See the module docstring for the
argument. -/
theorem centeredGermDeath_of_valuationGermDeath {n : ℕ} (hVGD : ValuationGermDeath.{u} n)
    (hcof : ∀ (B : Type u) [CommRing B] [IsDomain B], RefinementsCofiltered B)
    (hspread : GermDeathSpreads.{u}) (hzero : StalkZeroOffClosure.{u})
    (hstab : DeadAtStableUnderRefinement.{u}) (hkills : KillsOfForallDeadAt.{u})
    (hfibre : FibreOpenOverEtale.{u}) (hcenter : ExistsValuationCenter.{u})
    (hbasic : CenterOpenBasic.{u}) (hfin : FiniteLiftsAtPoint.{u})
    (hcpt : ZariskiRiemannFibreQuasiCompact.{u}) : CenteredGermDeath.{u} n := by
  intro B _ _ _ _ hn F hF M q U g w hw hrank
  have : Etale U.hom := U.prop
  -- Step 1: one refinement and one basic open set per valuation ring centered at `y`.
  have step1 : ∀ (V : ValuationSubring (FractionRing B))
      (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V),
      IsLocalHom (valuationSubringBaseMap V hV) → M.centerPoint V hV = U.hom w →
      ∃ (M₁ : ProperModel B) (φ : ProperModel.Refinement M₁ M) (S : Finset (FractionRing B)),
        (∀ x ∈ S, x ∈ V) ∧
        ∀ (V' : ValuationSubring (FractionRing B))
          (hV' : ∀ b : B, algebraMap B (FractionRing B) b ∈ V'),
          M.centerPoint V' hV' = U.hom w → (∀ x ∈ S, x ∈ V') →
          ∀ u' : ↥(pullback U.hom φ.π), pullback.fst U.hom φ.π u' = w →
            pullback.snd U.hom φ.π u' = M₁.centerPoint V' hV' → u' ∈ φ.deadSet F q U g := by
    intro V hV hloc hc
    obtain ⟨Ω, _, _, v, hv⟩ := exists_geometricPoint_closedPoint V
    have hcen : ∀ {M₂ M₃ : ProperModel B} (φ : ProperModel.Refinement M₂ M₃),
        (v ≫ M₂.center V hV) ≫ φ.π = v ≫ M₃.center V hV := fun φ ↦ by
      rw [Category.assoc, ← φ.center_eq hV]
    let L := {ℓ : (Scheme.pointSmallEtale (v ≫ M.center V hV)).fiber.obj U |
      etaleLiftHom ℓ (default : Spec (.of Ω)) = w}
    have : Finite L := (hfin U Ω (v ≫ M.center V hV) w).to_subtype
    have hgerm : ∀ ℓ : L, ∃ (M₂ : ProperModel B) (φ : ProperModel.Refinement M₂ M),
        φ.DeadAt F q U g (v ≫ M₂.center V hV) (hcen φ) ℓ.1 :=
      fun ℓ ↦ hVGD B hn F hF M q V hV hloc (hrank V hV hloc hc) Ω v hv
        ((Scheme.pointSmallEtale (v ≫ M.center V hV)).toPresheafFiber U ℓ.1
          (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj g)
    choose M₂ φ₂ hφ₂ using hgerm
    obtain ⟨M₁, φ, hρ⟩ := ProperModel.exists_refinement_factoring_all (hcof B) M M₂ φ₂
    have hdead : ∀ ℓ : L, φ.DeadAt F q U g (v ≫ M₁.center V hV) (hcen φ) ℓ.1 := by
      intro ℓ
      obtain ⟨ρ, hρℓ⟩ := hρ ℓ
      exact (hstab B M₁ (M₂ ℓ) M ρ (φ₂ ℓ) F q U g Ω _ _ (hcen ρ) _ (hcen _)
        (hcen (ρ.comp _)) ℓ.1 (hφ₂ ℓ)).of_eq hρℓ
    have hcd : ∀ u' : ↥(pullback U.hom φ.π), pullback.fst U.hom φ.π u' = w →
        pullback.snd U.hom φ.π u' = M₁.centerPoint V hV → u' ∈ φ.deadSet F q U g := by
      intro u' hu1 hu2
      have hs : pullback.snd U.hom φ.π u' = (v ≫ M₁.center V hV) (default : Spec (.of Ω)) := by
        rw [hu2, Scheme.Hom.comp_apply, hv]
        rfl
      obtain ⟨l, hl, hlu⟩ := exists_fac_of_etale_of_isSepClosed (pullback.snd U.hom φ.π)
        (v ≫ M₁.center V hV) u' hs
      have hw' : (l ≫ pullback.fst U.hom φ.π) ≫ U.hom = v ≫ M.center V hV := by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hl, hcen]
      let ℓ : (Scheme.pointSmallEtale (v ≫ M.center V hV)).fiber.obj U :=
        Over.homMk (l ≫ pullback.fst U.hom φ.π) hw'
      have hℓ : ℓ ∈ L := by
        change (l ≫ pullback.fst U.hom φ.π) (default : Spec (.of Ω)) = w
        rw [Scheme.Hom.comp_apply, hlu, hu1]
      have hlift : pullback.lift (etaleLiftHom ℓ) (v ≫ M₁.center V hV)
          (by rw [hcen]; exact etaleLiftHom_comp ℓ) = l := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
          rfl
        · rw [pullback.lift_snd, hl]
      have hpt : φ.germPoint U (v ≫ M₁.center V hV) (hcen φ) ℓ = u' := by
        rw [ProperModel.Refinement.germPoint, hlift]
        exact hlu
      rw [← hpt]
      exact hspread B M₁ M φ F q U g Ω _ _ _ ℓ (hdead ⟨ℓ, hℓ⟩)
    obtain ⟨N, hN, hcN, hNdead⟩ := hfibre φ.π U _ (φ.isOpen_deadSet F q U g) w
      (M₁.centerPoint V hV) hcd
    obtain ⟨S, hSV, hS⟩ := hbasic B M₁ V hV N hN hcN
    refine ⟨M₁, φ, S, hSV, fun V' hV' hc' hSV' u' hu1 hu2 ↦ ?_⟩
    refine hNdead _ (hS V' hV' hSV') ?_ u' hu1 hu2
    rw [φ.π_centerPoint hV', φ.π_centerPoint hV, hc', hc]
  -- Step 2: finitely many of them, by quasi-compactness of the Zariski–Riemann fibre.
  let I := {V : ValuationSubring (FractionRing B) //
    ∃ hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V,
      IsLocalHom (valuationSubringBaseMap V hV) ∧ M.centerPoint V hV = U.hom w}
  choose M₁ φ₁ S hSV hS using fun i : I ↦ step1 i.1 i.2.fst i.2.snd.1 i.2.snd.2
  obtain ⟨J, hJ⟩ := hcpt B M (U.hom w) S fun V hV hloc hc ↦ ⟨⟨V, hV, hloc, hc⟩, hSV _⟩
  -- Step 3: one common refinement.
  obtain ⟨M'', ψ, hρ⟩ := ProperModel.exists_refinement_factoring_all (hcof B) M
    (fun i : J ↦ M₁ i.1) (fun i ↦ φ₁ i.1)
  -- Step 4: every point of `U ×_Y Y''` over `w` is dead.
  have hall : ∀ u'' : ↥(pullback U.hom ψ.π), pullback.fst U.hom ψ.π u'' = w →
      u'' ∈ ψ.deadSet F q U g := by
    intro u'' hu
    have hπ : ψ.π (pullback.snd U.hom ψ.π u'') = U.hom w := by
      rw [← hu, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    by_cases hcl : pullback.snd U.hom ψ.π u'' ∈ closure (Set.range M''.j)
    · have hf : M''.f (pullback.snd U.hom ψ.π u'') = IsLocalRing.closedPoint B := by
        rw [← ψ.comm, Scheme.Hom.comp_apply, hπ, hw]
      obtain ⟨V', hV', hloc', hc'⟩ := hcenter B M'' _ hcl hf
      have hcy : M.centerPoint V' hV' = U.hom w := by
        rw [← ψ.π_centerPoint hV', hc', hπ]
      obtain ⟨i, hiJ, hiS⟩ := hJ V' hV' hloc' hcy
      obtain ⟨ρ, hρi⟩ := hρ ⟨i, hiJ⟩
      have heq : ψ.π ≫ 𝟙 M.Y = ρ.π ≫ (φ₁ i).π := by
        rw [Category.comp_id, ← hρi]
        rfl
      let mp := pullback.map U.hom ψ.π U.hom (φ₁ i).π (𝟙 _) ρ.π (𝟙 _) (by simp) heq
      have h1 : mp ≫ pullback.fst U.hom (φ₁ i).π = pullback.fst U.hom ψ.π := by
        simp [mp]
      have h2 : mp ≫ pullback.snd U.hom (φ₁ i).π = pullback.snd U.hom ψ.π ≫ ρ.π := by
        simp [mp]
      have hmem := hS i V' hV' hcy hiS (mp u'')
        (by rw [← Scheme.Hom.comp_apply, h1, hu])
        (by rw [← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply, ← hc',
          ρ.π_centerPoint hV'])
      obtain ⟨O', hO', huO', hdO'⟩ := hmem
      refine ⟨mp ⁻¹' O', hO'.preimage mp.continuous, huO', ?_⟩
      intro Ω _ _ s2 t2 ht2 ℓ2 hpt2
      have ht2' : (s2 ≫ ρ.π) ≫ (φ₁ i).π = t2 := by
        rw [Category.assoc, ← ht2, ← hρi]
        rfl
      have hmor : pullback.lift (etaleLiftHom ℓ2) (s2 ≫ ρ.π)
          (by rw [ht2']; exact etaleLiftHom_comp ℓ2) =
          pullback.lift (etaleLiftHom ℓ2) s2 (by rw [ht2]; exact etaleLiftHom_comp ℓ2) ≫ mp := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst, Category.assoc, h1, pullback.lift_fst]
        · rw [pullback.lift_snd, Category.assoc, h2, pullback.lift_snd_assoc]
      have hptm : (φ₁ i).germPoint U (s2 ≫ ρ.π) ht2' ℓ2 = mp (ψ.germPoint U s2 ht2 ℓ2) := by
        rw [ProperModel.Refinement.germPoint, ProperModel.Refinement.germPoint, hmor,
          Scheme.Hom.comp_apply]
      have hd := hdO' Ω (s2 ≫ ρ.π) t2 ht2' ℓ2 (by rw [hptm]; exact hpt2)
      exact (hstab B M'' (M₁ i) M ρ (φ₁ i) F q U g Ω s2 (s2 ≫ ρ.π) rfl t2 ht2'
        (by rw [hρi]; exact ht2) ℓ2 hd).of_eq hρi
    · refine ⟨pullback.snd U.hom ψ.π ⁻¹' (closure (Set.range M''.j))ᶜ,
        isClosed_closure.isOpen_compl.preimage (pullback.snd U.hom ψ.π).continuous, hcl, ?_⟩
      intro Ω _ _ s2 t2 ht2 ℓ2 hpt2
      have hsnd : pullback.snd U.hom ψ.π (ψ.germPoint U s2 ht2 ℓ2) = s2 default := by
        rw [ProperModel.Refinement.germPoint, ← Scheme.Hom.comp_apply, pullback.lift_snd]
      have hs2 : s2 (default : Spec (.of Ω)) ∉ closure (Set.range M''.j) := by
        rwa [← hsnd]
      exact eq_zero_of_isZero_addCommGrpCat
        (hzero B M'' ((etaleAbelianInverseImage.{u, 0} (𝟙 _)).obj F) q Ω s2 hs2) _
  -- Step 5: the image of the complement of the dead set is closed and misses `w`.
  have : IsProper ψ.π := by
    have : IsProper (ψ.π ≫ M.f) := by rw [ψ.comm]; infer_instance
    exact IsProper.of_comp (f := ψ.π) (g := M.f)
  let Z := pullback.fst U.hom ψ.π '' (ψ.deadSet F q U g)ᶜ
  have hZ : IsClosed Z :=
    (pullback.fst U.hom ψ.π).isClosedMap _ (ψ.isOpen_deadSet F q U g).isClosed_compl
  have hwZ : w ∉ Z := fun ⟨u'', hu''1, hu''2⟩ ↦ hu''1 (hall u'' hu''2)
  let Uo : U.left.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  let W : M.Y.Etale := Scheme.Etale.mk (Uo.ι ≫ U.hom)
  let h : W ⟶ U := MorphismProperty.Over.homMk Uo.ι rfl trivial
  refine ⟨W, h, ⟨w, hwZ⟩, rfl, M'', ψ, hkills B M'' M ψ F q W _ fun Ω _ _ s ℓ ↦ ?_⟩
  -- Step 6: on `W` every germ dies.
  let ℓ' := (Scheme.pointSmallEtale (s ≫ ψ.π)).fiber.map h ℓ
  have hfst : pullback.fst U.hom ψ.π (ψ.germPoint U s rfl ℓ') =
      Uo.ι (etaleLiftHom ℓ (default : Spec (.of Ω))) := by
    rw [ProperModel.Refinement.germPoint, ← Scheme.Hom.comp_apply, pullback.lift_fst,
      etaleLiftHom_map, Scheme.Hom.comp_apply]
    rfl
  have hUo : Uo.ι (etaleLiftHom ℓ (default : Spec (.of Ω))) ∈ (Uo : Set ↥U.left) := by
    rw [← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  have hmem : ψ.germPoint U s rfl ℓ' ∈ ψ.deadSet F q U g := by
    by_contra hnot
    exact hUo ⟨_, hnot, hfst⟩
  obtain ⟨O, _, hO, hd⟩ := hmem
  exact (ψ.deadAt_map_iff F q h g s rfl ℓ).2 (hd Ω s (s ≫ ψ.π) rfl ℓ' hO)

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
