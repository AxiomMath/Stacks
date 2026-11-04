module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroQuasiCompact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnitULift
public import StacksFrontier.Topology.Sheaves.Spectral.CompactBasisColimit
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite presentations by extensions by zero, and their cokernels

Let `C` be a site with a distinguished collection `B` of objects such that every object of `C`
has a covering by members of `B` and every member of `B` is quasi-compact (conditions (1) and
(2) of Stacks 0937), and let `R` be a sheaf of rings on `C`. Stacks Equation 18.30.7.2 (Tag
093D) singles out the sheaves of `R`-modules of the form

`Coker(⊕_{j = 1, …, m} j_{V_j!} O_{V_j} ⟶ ⊕_{i = 1, …, n} j_{U_i!} O_{U_i})`

with all `U_i` and `V_j` in `B`. This file defines that condition and proves **Stacks 093E**:
the collection of such modules is stable under cokernels of maps between its members.

## Main definitions

* `Stacks.SheafOfModules.HasFiniteExtensionByZeroPresentation`: Equation 18.30.7.2 as a
  predicate on a sheaf of modules.

## Main results

* `Stacks.SheafOfModules.cokernelIsoCokernelOfFactorizations`: a comparison of cokernels in a
  category with zero morphisms, which is the bookkeeping at the heart of the argument.
* `Stacks.SheafOfModules.exists_hypercover_subordinate`: condition (1) in the form "every
  covering sieve is refined by a covering family of distinguished objects".
* `Stacks.SheafOfModules.exists_finite_lift_extensionByZeroUnit`: given an epimorphism
  `q : A ⟶ G` and a map `j_{W!} O_W ⟶ G` with `W` distinguished, a *finite* family of
  distinguished objects covering `W` on each member of which the map lifts through `q`.
* `Stacks.SheafOfModules.hasFiniteExtensionByZeroPresentation_of_ulift` and
  `Stacks.SheafOfModules.exists_ulift_of_hasFiniteExtensionByZeroPresentation`: the predicate
  does not depend on which of the two spellings of `j_{U!} O_U` the presentation is written at.
* `Stacks.SheafOfModules.hasFiniteExtensionByZeroPresentation_cokernel`: **Stacks Project,
  Tag 093E.**

## Implementation notes

**The statement is the Stacks statement, at the module universe where `Mod(O)` is abelian.**
Stacks works throughout in `Mod(O)`, which is abelian by its standing conventions, and the
cokernel of the lemma is the cokernel there. The module universe is therefore fixed to
`max u₁ v₁ w t`, the universe at which `Stacks.SheafOfModules.extensionByZeroUnit` is
constructed: the site is essentially small there, so `HasSheafify J AddCommGrpCat` and
`J.WEqualsLocallyBijective AddCommGrpCat` are theorems rather than hypotheses, and
`SheafOfModules` is abelian. No `HasCokernel` hypothesis and no `ULift` wrapper on the module
being presented are needed, and the predicate is about the module itself.

**That pin is forced, not chosen.** `extensionByZeroUnit.{u₁, v₁, w, t} R U` lives in
`SheafOfModules.{max u₁ v₁ w t} R`, so the predicate can only speak about modules whose universe
contains `max u₁ v₁ w`; `max u₁ v₁ w t` with `t` free is exactly "any such universe", and there
is no generalization of *this* statement to a smaller module universe. The statement at an
arbitrary module universe is a *different* theorem: `f : F ⟶ G` in `SheafOfModules.{v} R` for an
arbitrary `v`, with
`[HasCokernel f]` as a hypothesis (the category is not known to have cokernels there), and the
conclusion about `(moduleULift _).obj (cokernel f)`. Modulo the predicate and generator
spellings, which are definitionally equal — see
`hasFiniteExtensionByZeroPresentation_of_ulift` and
`exists_ulift_of_hasFiniteExtensionByZeroPresentation` — that theorem reduces to exactly one
transfer statement: that `moduleULift` carries the cokernel of `f` to the cokernel of the lift
of `f`.

What is available towards that transfer, at an arbitrary module universe:
`Stacks.SheafOfModules.isLocallySurjective_cokernel_π` and
`Stacks.SheafOfModules.epi_moduleULift_map_cokernel_π` give the epimorphism half, and
`Stacks.SheafOfModules.mono_moduleULift_map` transports monomorphisms. What is missing is the
monomorphism half of the comparison `cokernel (moduleULift f) ⟶ moduleULift (cokernel f)`,
which unwinds to: the kernel of `cokernel.π f` is the local closure of the image of `f`. That is
the statement that the reflection of `G/im f` into `SheafOfModules.{v} R` has a locally
injective unit — i.e. sheafification theory at the module universe `v`, which Mathlib supplies
only under `UnivLE.{u₁, v}` and `UnivLE.{v₁, v}`.

**Why the index types of the auxiliary results are `Type (max u₁ v₁)`.**
`CategoryTheory.GrothendieckTopology.IsQuasiCompactObject` and
`Stacks.QuasiCompactObjectsSituation.HasEnoughObjects` both quantify over covering families
indexed by `Type (max u₁ v₁)`, because that is the universe in which every covering sieve of an
object is generated by a family. The index types produced by the auxiliary results are therefore
in that universe, and `hasFiniteExtensionByZeroPresentation_of_finite` is what converts such a
family into the `Fin n` form of the predicate; the two index universes there are independent for
exactly this reason.

**The proof.** This is Stacks' own argument. Write `G = Coker(b : B ⟶ A)` and
`F = Coker(b' : B' ⟶ A')` with `A = ⊕ j_{U_i!} O_{U_i}` and `A' = ⊕ j_{W_k!} O_{W_k}`, and let
`q : A ⟶ G`, `p : A' ⟶ F` be the two quotient maps. Since `p` is an epimorphism,
`Coker(f) ≅ Coker(ψ)` for `ψ = p ≫ f : A' ⟶ G`. The restriction of `ψ` to the `k`-th summand is
a section of `G` over `W_k` by Stacks 0G1V; as `q` is an epimorphism it lifts to `A` after
restriction along some covering of `W_k`, which condition (1) lets us take to consist of
distinguished objects, and condition (2) with Stacks 0G1W cuts that covering down to a *finite*
subfamily `{Z_{k,c} → W_k}` whose extensions by zero still map onto `j_{W_k!} O_{W_k}`. Then
`Coker(ψ)` is the cokernel of the map into `A` whose summands are the lifts over the `Z_{k,c}`
together with `b`; that last step is `cokernelIsoCokernelOfFactorizations`.

**No local surjectivity is needed for Stacks 0G1W** (see
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroQuasiCompact`), but it *is* needed
for the lifting step, which is why `EpiLocallySurjective` is imported.

The two `local instance`s below are a fourth copy of a derivation that
`ExtensionByZeroUnit.lean`, `ExtensionByZeroQuasiCompact.lean` and `ExtensionByZeroUnitULift.lean`
also carry privately; a public declaration of another module cannot refer to a `private` one.
If they are ever made public, all four copies should cite them.

## References

* [Stacks Project, Tag 093E](https://stacks.math.columbia.edu/tag/093E)
* [Stacks Project, Tag 093D](https://stacks.math.columbia.edu/tag/093D)
* [Stacks Project, Tag 0937](https://stacks.math.columbia.edu/tag/0937)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 0G1W](https://stacks.math.columbia.edu/tag/0G1W)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u₁ v₁ w t

namespace Stacks.SheafOfModules

/-! ### A comparison of cokernels -/

section CokernelComparison

variable {𝒜 : Type*} [Category 𝒜] [HasZeroMorphisms 𝒜]

/-- **Replacing the relations in a cokernel presentation.** Let `b : B ⟶ A` be a morphism, let
`q : A ⟶ Coker(b)` be the quotient map, and let `ψ : A' ⟶ Coker(b)` be a morphism. Suppose given
`γ : D ⟶ A` through which `b` factors (by `v`) and such that `γ ≫ q` factors through `ψ` (by
`θ`), and suppose that after precomposition with some epimorphism `ε : E ⟶ A'` the morphism
`ε ≫ ψ` factors as `u ≫ γ ≫ q`. Then `Coker(γ) ≅ Coker(ψ)`.

Read in the situation of Stacks 093E: `γ` is the map whose summands are `b` together with lifts
through `q` of the restrictions of `ψ` to a covering, and the hypotheses say that those lifts
generate `ψ` locally. -/
noncomputable def cokernelIsoCokernelOfFactorizations {B A A' D E : 𝒜} (b : B ⟶ A)
    [HasCokernel b] (ψ : A' ⟶ cokernel b) (γ : D ⟶ A) [HasCokernel γ] [HasCokernel ψ]
    (v : B ⟶ D) (θ : D ⟶ A') (ε : E ⟶ A') [Epi ε] (u : E ⟶ D) (hv : v ≫ γ = b)
    (hθ : θ ≫ ψ = γ ≫ cokernel.π b) (hu : u ≫ γ ≫ cokernel.π b = ε ≫ ψ) :
    cokernel γ ≅ cokernel ψ := by
  have hb : b ≫ cokernel.π γ = 0 := by
    rw [← hv, Category.assoc, cokernel.condition, comp_zero]
  have hqg : cokernel.π b ≫ cokernel.desc b (cokernel.π γ) hb = cokernel.π γ :=
    cokernel.π_desc _ _ _
  have hψg : ψ ≫ cokernel.desc b (cokernel.π γ) hb = 0 := by
    refine (cancel_epi ε).1 ?_
    calc ε ≫ ψ ≫ cokernel.desc b (cokernel.π γ) hb
        = (ε ≫ ψ) ≫ cokernel.desc b (cokernel.π γ) hb := by rw [Category.assoc]
      _ = (u ≫ γ ≫ cokernel.π b) ≫ cokernel.desc b (cokernel.π γ) hb := by rw [hu]
      _ = u ≫ γ ≫ cokernel.π b ≫ cokernel.desc b (cokernel.π γ) hb := by
          rw [Category.assoc, Category.assoc]
      _ = u ≫ γ ≫ cokernel.π γ := by rw [hqg]
      _ = ε ≫ 0 := by rw [cokernel.condition, comp_zero, comp_zero]
  have hγψ : γ ≫ cokernel.π b ≫ cokernel.π ψ = 0 := by
    rw [← Category.assoc, ← hθ, Category.assoc, cokernel.condition, comp_zero]
  refine
    { hom := cokernel.desc γ (cokernel.π b ≫ cokernel.π ψ) hγψ
      inv := cokernel.desc ψ (cokernel.desc b (cokernel.π γ) hb) hψg
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · refine (cancel_epi (cokernel.π γ)).1 ?_
    rw [Category.comp_id, ← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc,
      hqg]
  · refine (cancel_epi (cokernel.π ψ)).1 ?_
    rw [Category.comp_id, ← Category.assoc, cokernel.π_desc]
    refine (cancel_epi (cokernel.π b)).1 ?_
    rw [← Category.assoc, hqg, cokernel.π_desc]

/-- Conjugating a morphism by isomorphisms does not change the isomorphism class of its
cokernel. -/
private theorem nonempty_cokernel_conj_iso [HasCokernels 𝒜] {X X' Y Y' G : 𝒜} (f : X ⟶ Y)
    (α : X' ≅ X) (β : Y ≅ Y') (e : cokernel f ≅ G) :
    Nonempty (cokernel (α.hom ≫ f ≫ β.hom) ≅ G) :=
  ⟨cokernelEpiComp _ _ ≪≫ cokernelCompIsIso f _ ≪≫ e⟩

end CokernelComparison

/-! ### Refining a covering sieve by distinguished objects -/

section Refinement

variable {C : Type u₁} [Category.{v₁} C]

/-- **Condition (1) of Stacks 0937, in sieve-refinement form.** If every object of `C` has a
covering by distinguished objects, then every covering sieve `T` of `W` is refined by a covering
family of `W` all of whose members are distinguished and lie in `T`. -/
@[simps]
def sieveRefinementHypercover (𝒱 : ∀ U : C, PreZeroHypercover.{max u₁ v₁} U) {W : C}
    (T : Sieve W) : PreZeroHypercover.{max u₁ v₁} W where
  I₀ := Σ p : Σ V : C, { g : V ⟶ W // T g }, (𝒱 p.1).I₀
  X x := (𝒱 x.1.1).X x.2
  f x := (𝒱 x.1.1).f x.2 ≫ x.1.2.1

/-- If every object of `C` has a covering by distinguished objects, then every covering sieve `T`
of `W` contains the morphisms of a covering family of `W` by distinguished objects. -/
theorem exists_hypercover_subordinate (S : QuasiCompactObjectsSituation C)
    (hEnough : S.HasEnoughObjects) {W : C} {T : Sieve W} (hT : T ∈ S.topology W) :
    ∃ 𝒲 : PreZeroHypercover.{max u₁ v₁} W, 𝒲.sieve₀ ∈ S.topology W ∧
      (∀ c, 𝒲.X c ∈ S.objects) ∧ ∀ c, T (𝒲.f c) := by
  choose 𝒱 h𝒱mem h𝒱obj using hEnough
  refine ⟨sieveRefinementHypercover 𝒱 T, ?_, fun x => h𝒱obj _ _,
    fun x => T.downward_closed x.1.2.2 _⟩
  refine S.topology.transitive hT _ ?_
  intro Y₀ g hg
  refine S.topology.superset_covering ?_ (h𝒱mem Y₀)
  rintro Z₀ h₀ ⟨Z₁, a, b₀, ⟨c⟩, rfl⟩
  show (sieveRefinementHypercover 𝒱 T).sieve₀ ((a ≫ (𝒱 Y₀).f c) ≫ g)
  rw [Category.assoc]
  exact (sieveRefinementHypercover 𝒱 T).sieve₀.downward_closed
    ((sieveRefinementHypercover 𝒱 T).sieve₀_f ⟨⟨Y₀, g, hg⟩, c⟩) a

end Refinement

/-! ### Finite presentations by extensions by zero -/

section Presentation

variable {C : Type u₁} [Category.{v₁} C]

attribute [local instance] siteHasSheafify siteWEqualsLocallyBijective

variable (S : QuasiCompactObjectsSituation C) (R : Sheaf S.topology RingCat.{w})

/-- **Stacks Project, Equation 18.30.7.2 (Tag 093D).** A sheaf of `R`-modules *has a finite
presentation by extensions by zero* if it is isomorphic to the cokernel of a morphism between
two finite direct sums of extensions by zero `j_{U!} O_U` of the structure sheaf at
distinguished objects `U`. -/
@[stacks 093D "the modules of Equation 18.30.7.2"]
def HasFiniteExtensionByZeroPresentation.{u₁', v₁', w', t'} {C : Type u₁'} [Category.{v₁'} C]
    (S : QuasiCompactObjectsSituation C) (R : Sheaf S.topology RingCat.{w'})
    (G : SheafOfModules.{max u₁' v₁' w' t'} R) : Prop :=
  ∃ (n m : ℕ) (U : Fin n → C) (V : Fin m → C),
    (∀ i, U i ∈ S.objects) ∧ (∀ j, V j ∈ S.objects) ∧
      ∃ f : (∐ fun j ↦ extensionByZeroUnit.{u₁', v₁', w', t'} R (V j)) ⟶
          (∐ fun i ↦ extensionByZeroUnit.{u₁', v₁', w', t'} R (U i)),
        Nonempty (cokernel f ≅ G)

/-- A presentation whose two index types are arbitrary finite types is a finite presentation:
reindex both coproducts by `Fin`. The two index universes are independent, because the proof of
Stacks 093E produces the relations indexed in `Type (max u₁ v₁)` while the generators stay
indexed by `Fin n`. -/
theorem hasFiniteExtensionByZeroPresentation_of_finite {ι : Type*} {κ : Type*} [Finite ι]
    [Finite κ] (U : ι → C) (V : κ → C) (hU : ∀ i, U i ∈ S.objects) (hV : ∀ j, V j ∈ S.objects)
    {G : SheafOfModules.{max u₁ v₁ w t} R}
    [HasCoproduct fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i)]
    [HasCoproduct fun j ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (V j)]
    (f : (∐ fun j ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (V j)) ⟶
      (∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i)))
    (e : cokernel f ≅ G) :
    HasFiniteExtensionByZeroPresentation.{u₁, v₁, w, t} S R G := by
  obtain ⟨n, ⟨eU⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨m, ⟨eV⟩⟩ := Finite.exists_equiv_fin κ
  exact ⟨n, m, U ∘ eU.symm, V ∘ eV.symm, fun i => hU _, fun j => hV _, _,
    nonempty_cokernel_conj_iso f
      (Sigma.reindex eV.symm fun j ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (V j))
      (Sigma.reindex eU.symm fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i)).symm e⟩

/-- A finite presentation built from the **other** spelling of `j_{U!} O_U`, the one that lifts
the whole module rather than the index set, is a finite presentation: the two spellings are
identified summand by summand by `extensionByZeroUnitULiftIso`.

This is what lets a presentation stated with `extensionByZeroUnitULift` — the spelling Stacks
093C is written at — be read as a presentation in the sense of
`HasFiniteExtensionByZeroPresentation`, which is the spelling Stacks 0G1V and 0G1W are proved
at here. -/
theorem hasFiniteExtensionByZeroPresentation_of_ulift {n m : ℕ} (U : Fin n → C) (V : Fin m → C)
    (hU : ∀ i, U i ∈ S.objects) (hV : ∀ j, V j ∈ S.objects)
    {G : SheafOfModules.{max u₁ v₁ w t} R}
    (f : (∐ fun j ↦ extensionByZeroUnitULift.{u₁, v₁, w, t} R (V j)) ⟶
      ∐ fun i ↦ extensionByZeroUnitULift.{u₁, v₁, w, t} R (U i))
    (e : cokernel f ≅ G) :
    HasFiniteExtensionByZeroPresentation.{u₁, v₁, w, t} S R G := by
  exact ⟨n, m, U, V, hU, hV, _, nonempty_cokernel_conj_iso f
    (Sigma.whiskerEquiv (Equiv.refl (Fin m))
      (fun j ↦ (extensionByZeroUnitULiftIso.{u₁, v₁, w, t} R (V j)).symm)).symm
    (Sigma.whiskerEquiv (Equiv.refl (Fin n))
      (fun i ↦ (extensionByZeroUnitULiftIso.{u₁, v₁, w, t} R (U i)).symm)) e⟩

/-- The converse of `hasFiniteExtensionByZeroPresentation_of_ulift`: a finite presentation can
always be rewritten with the other spelling `extensionByZeroUnitULift` of `j_{U!} O_U`, by
conjugating the relations map with `extensionByZeroUnitULiftIso` summand by summand.

Together with `hasFiniteExtensionByZeroPresentation_of_ulift` this says that the predicate is
independent of which of the two spellings of `j_{U!} O_U` the presentation is written at, which
is what lets a statement phrased at the Stacks 093C spelling be compared with this one. -/
theorem exists_ulift_of_hasFiniteExtensionByZeroPresentation
    {G : SheafOfModules.{max u₁ v₁ w t} R}
    (h : HasFiniteExtensionByZeroPresentation.{u₁, v₁, w, t} S R G) :
    ∃ (n m : ℕ) (U : Fin n → C) (V : Fin m → C),
      (∀ i, U i ∈ S.objects) ∧ (∀ j, V j ∈ S.objects) ∧
        ∃ f : (∐ fun j ↦ extensionByZeroUnitULift.{u₁, v₁, w, t} R (V j)) ⟶
            ∐ fun i ↦ extensionByZeroUnitULift.{u₁, v₁, w, t} R (U i),
          Nonempty (cokernel f ≅ G) := by
  obtain ⟨n, m, U, V, hU, hV, b, ⟨e⟩⟩ := h
  exact ⟨n, m, U, V, hU, hV, _, nonempty_cokernel_conj_iso b
    (Sigma.whiskerEquiv (Equiv.refl (Fin m))
      (fun j ↦ (extensionByZeroUnitULiftIso.{u₁, v₁, w, t} R (V j)).symm))
    (Sigma.whiskerEquiv (Equiv.refl (Fin n))
      (fun i ↦ (extensionByZeroUnitULiftIso.{u₁, v₁, w, t} R (U i)).symm)).symm e⟩

/-! ### The lifting step -/

/-- **The lifting step of Stacks 093E.** Let `q : A ⟶ G` be an epimorphism of sheaves of
modules and let `ψ : j_{W!} O_W ⟶ G` with `W` distinguished. Then there is a *finite* family of
distinguished objects `Z c` over `W` whose extensions by zero map onto `j_{W!} O_W`, and over
each of which `ψ` lifts through `q`.

Local surjectivity of `q` produces a covering of `W` on which the section of `G` corresponding
to `ψ` under Stacks 0G1V lifts; condition (1) refines that covering by distinguished objects and
condition (2) with Stacks 0G1W extracts a finite subfamily. -/
theorem exists_finite_lift_extensionByZeroUnit (hEnough : S.HasEnoughObjects)
    (hqc : S.ObjectsAreQuasiCompact) {A G : SheafOfModules.{max u₁ v₁ w t} R} (q : A ⟶ G)
    [Epi q] {W : C} (hW : W ∈ S.objects)
    (ψ : extensionByZeroUnit.{u₁, v₁, w, t} R W ⟶ G) :
    ∃ (ι : Type (max u₁ v₁)) (_ : Finite ι) (Z : ι → C) (g : ∀ c, Z c ⟶ W),
      (∀ c, Z c ∈ S.objects) ∧
        Epi (Sigma.desc fun c ↦ extensionByZeroUnitMap.{u₁, v₁, w, t} R (g c)) ∧
          ∃ d : ∀ c, extensionByZeroUnit.{u₁, v₁, w, t} R (Z c) ⟶ A,
            ∀ c, d c ≫ q = extensionByZeroUnitMap.{u₁, v₁, w, t} R (g c) ≫ ψ := by
  obtain ⟨T, hT, hlift⟩ := EpiMono.exists_covering_of_epi q
    (extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R W G ψ)
  obtain ⟨𝒲, h𝒲mem, h𝒲obj, h𝒲sub⟩ := exists_hypercover_subordinate S hEnough hT
  obtain ⟨Tfin, hTfin, hTepi⟩ :=
    exists_finite_epi_sigmaDesc_extensionByZeroUnitMap.{u₁, v₁, w, t} R (hqc W hW) 𝒲 h𝒲mem
  have _ : Finite Tfin := hTfin.to_subtype
  refine ⟨Tfin, inferInstance, fun c ↦ 𝒲.X c.1, fun c ↦ 𝒲.f c.1, fun c ↦ h𝒲obj _, hTepi, ?_⟩
  choose s hs using fun c : Tfin ↦ hlift (𝒲.f c.1) (h𝒲sub c.1)
  have hd : ∀ c : Tfin,
      (extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R (𝒲.X c.1) A).symm (s c) ≫ q =
        extensionByZeroUnitMap.{u₁, v₁, w, t} R (𝒲.f c.1) ≫ ψ := by
    intro c
    refine (extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R (𝒲.X c.1) G).injective ?_
    rw [extensionByZeroUnitHomEquiv_naturality, extensionByZeroUnitHomEquiv_map]
    exact (congrArg (fun x ↦ (SheafOfModules.evaluation R (op (𝒲.X c.1))).map q x)
      (Equiv.apply_symm_apply _ (s c))).trans (hs c)
  exact ⟨_, hd⟩

/-! ### Stacks 093E -/

/-- The direct sum over a family of index sets of the epimorphisms supplied by
`exists_finite_lift_extensionByZeroUnit` is an epimorphism onto the direct sum of the
`j_{W_k!} O_{W_k}`. -/
theorem epi_sigmaDesc_sigmaIota {n : ℕ} (W : Fin n → C) (ι : Fin n → Type (max u₁ v₁))
    (Z : ∀ k, ι k → C) (g : ∀ k c, Z k c ⟶ W k)
    (hepi : ∀ k, Epi (Sigma.desc fun c ↦ extensionByZeroUnitMap.{u₁, v₁, w, t} R (g k c))) :
    Epi (Sigma.desc fun x : Σ k, ι k ↦
      extensionByZeroUnitMap.{u₁, v₁, w, t} R (g x.1 x.2) ≫
        Sigma.ι (fun k ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (W k)) x.1) := by
  refine ⟨fun {P} h₁ h₂ hh => Sigma.hom_ext _ _ fun k => ?_⟩
  have _ := hepi k
  refine (cancel_epi (Sigma.desc fun c ↦
    extensionByZeroUnitMap.{u₁, v₁, w, t} R (g k c))).1 (Sigma.hom_ext _ _ fun c => ?_)
  have h := Sigma.ι (fun x : Σ k, ι k ↦
    extensionByZeroUnit.{u₁, v₁, w, t} R (Z x.1 x.2)) (⟨k, c⟩ : Σ k, ι k) ≫= hh
  rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc, Category.assoc, Category.assoc] at h
  simp only [Sigma.ι_desc_assoc]
  exact h

/-- The objects indexing the relations of the presentation that the proof of Stacks 093E
produces: the distinguished objects over which the generators of the source lift, together with
the objects indexing the relations of the target. -/
def relationObjects {n' m : ℕ} (ι : Fin n' → Type (max u₁ v₁)) (Z : ∀ k, ι k → C)
    (V : Fin m → C) : ((k : Fin n') × ι k) ⊕ Fin m → C :=
  Sum.elim (fun x ↦ Z x.1 x.2) V

/-- The relations of the presentation that the proof of Stacks 093E produces: the lifts of the
generators of the source, together with the relations of the target. -/
noncomputable def relationsMap {n m n' : ℕ} (U : Fin n → C) (V : Fin m → C)
    (ι : Fin n' → Type (max u₁ v₁)) (Z : ∀ k, ι k → C)
    (b : (∐ fun j ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (V j)) ⟶
      ∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i))
    (d : ∀ k c, extensionByZeroUnit.{u₁, v₁, w, t} R (Z k c) ⟶
      ∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i)) :
    (∐ fun sx ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (relationObjects ι Z V sx)) ⟶
      ∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i) :=
  Sigma.desc (Sum.rec (fun x ↦ d x.1 x.2)
    (fun j ↦ Sigma.ι (fun j' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (V j')) j ≫ b))

/-- On the summand indexed by `Sum.inl x`, `relationsMap` restricts to `d x.1 x.2`. -/
@[reassoc]
lemma ι_inl_comp_relationsMap {n m n' : ℕ} (U : Fin n → C) (V : Fin m → C)
    (ι : Fin n' → Type (max u₁ v₁)) (Z : ∀ k, ι k → C)
    (b : (∐ fun j ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (V j)) ⟶
      ∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i))
    (d : ∀ k c, extensionByZeroUnit.{u₁, v₁, w, t} R (Z k c) ⟶
      ∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i)) (x : Σ k, ι k) :
    Sigma.ι (fun sx ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (relationObjects ι Z V sx))
        (Sum.inl x) ≫ relationsMap S R U V ι Z b d = d x.1 x.2 :=
  Sigma.ι_desc _ _

/-- On the summand indexed by `Sum.inr j`, `relationsMap` restricts to the composite of the
coprojection at `j` with `b`. -/
@[reassoc]
lemma ι_inr_comp_relationsMap {n m n' : ℕ} (U : Fin n → C) (V : Fin m → C)
    (ι : Fin n' → Type (max u₁ v₁)) (Z : ∀ k, ι k → C)
    (b : (∐ fun j ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (V j)) ⟶
      ∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i))
    (d : ∀ k c, extensionByZeroUnit.{u₁, v₁, w, t} R (Z k c) ⟶
      ∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i)) (j : Fin m) :
    Sigma.ι (fun sx ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (relationObjects ι Z V sx))
        (Sum.inr j) ≫ relationsMap S R U V ι Z b d =
      Sigma.ι (fun j' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (V j')) j ≫ b :=
  Sigma.ι_desc _ _

/-- **The assembly step of Stacks 093E.** If every generator `j_{W_k!} O_{W_k}` of the source of
`ψ` is, after restriction along a finite family `{Z_{k,c} → W_k}` whose extensions by zero map
onto it, in the image of the quotient map `q : A ⟶ Coker(b)`, then `Coker(ψ)` is the cokernel of
the map into `A` whose summands are those lifts together with `b`. -/
noncomputable def cokernelIsoOfLifts {n m n' : ℕ} (U : Fin n → C) (V : Fin m → C)
    (W : Fin n' → C) (ι : Fin n' → Type (max u₁ v₁)) (Z : ∀ k, ι k → C)
    (g : ∀ k c, Z k c ⟶ W k)
    (b : (∐ fun j ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (V j)) ⟶
      ∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i))
    (ψ : (∐ fun k ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (W k)) ⟶ cokernel b)
    (d : ∀ k c, extensionByZeroUnit.{u₁, v₁, w, t} R (Z k c) ⟶
      ∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i))
    (hd : ∀ k c, d k c ≫ cokernel.π b =
      extensionByZeroUnitMap.{u₁, v₁, w, t} R (g k c) ≫
        Sigma.ι (fun k' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (W k')) k ≫ ψ)
    (hepi : ∀ k, Epi (Sigma.desc fun c ↦ extensionByZeroUnitMap.{u₁, v₁, w, t} R (g k c))) :
    cokernel (relationsMap S R U V ι Z b d) ≅ cokernel ψ := by
  have hε := epi_sigmaDesc_sigmaIota S R W ι Z g hepi
  refine cokernelIsoCokernelOfFactorizations b ψ (relationsMap S R U V ι Z b d)
    (Sigma.desc fun j ↦ Sigma.ι (fun sx ↦
      extensionByZeroUnit.{u₁, v₁, w, t} R (relationObjects ι Z V sx)) (Sum.inr j))
    (Sigma.desc (Sum.rec (fun x ↦ extensionByZeroUnitMap.{u₁, v₁, w, t} R (g x.1 x.2) ≫
        Sigma.ι (fun k ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (W k)) x.1) (fun _ ↦ 0)))
    (Sigma.desc fun x : Σ k, ι k ↦ extensionByZeroUnitMap.{u₁, v₁, w, t} R (g x.1 x.2) ≫
      Sigma.ι (fun k ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (W k)) x.1)
    (Sigma.desc fun x : Σ k, ι k ↦ Sigma.ι (fun sx ↦
      extensionByZeroUnit.{u₁, v₁, w, t} R (relationObjects ι Z V sx)) (Sum.inl x)) ?_ ?_ ?_
  · refine Sigma.hom_ext _ _ fun j => ?_
    exact (Sigma.ι_desc_assoc _ j (relationsMap S R U V ι Z b d)).trans
      (ι_inr_comp_relationsMap S R U V ι Z b d j)
  · refine Sigma.hom_ext _ _ fun sx => ?_
    cases sx with
    | inl x =>
      refine (Sigma.ι_desc_assoc _ (Sum.inl x) ψ).trans ((Category.assoc _ _ _).trans ?_)
      exact (hd x.1 x.2).symm.trans
        (ι_inl_comp_relationsMap_assoc S R U V ι Z b d x (cokernel.π b)).symm
    | inr j =>
      refine (Sigma.ι_desc_assoc _ (Sum.inr j) ψ).trans (zero_comp.trans ?_)
      refine ((ι_inr_comp_relationsMap_assoc S R U V ι Z b d j (cokernel.π b)).trans
        ((Category.assoc _ _ _).trans ?_)).symm
      rw [cokernel.condition]
      exact comp_zero
  · refine Sigma.hom_ext _ _ fun x => ?_
    refine ((Sigma.ι_desc_assoc _ x (relationsMap S R U V ι Z b d ≫ cokernel.π b)).trans
      ?_).trans (Eq.symm ((Sigma.ι_desc_assoc _ x ψ).trans (Category.assoc _ _ _)))
    exact (ι_inl_comp_relationsMap_assoc S R U V ι Z b d x (cokernel.π b)).trans (hd x.1 x.2)

/-- **Stacks Project, Tag 093E.** On a site with a distinguished collection of objects which
covers every object and consists of quasi-compact objects, the cokernel of a morphism between
two sheaves of modules with finite presentations by extensions by zero again has a finite
presentation by extensions by zero. -/
@[stacks 093E]
theorem hasFiniteExtensionByZeroPresentation_cokernel (hEnough : S.HasEnoughObjects)
    (hqc : S.ObjectsAreQuasiCompact) {F G : SheafOfModules.{max u₁ v₁ w t} R} (f : F ⟶ G)
    (hF : HasFiniteExtensionByZeroPresentation.{u₁, v₁, w, t} S R F)
    (hG : HasFiniteExtensionByZeroPresentation.{u₁, v₁, w, t} S R G) :
    HasFiniteExtensionByZeroPresentation.{u₁, v₁, w, t} S R (cokernel f) := by
  obtain ⟨n', m', W, V', hW, hV', b', ⟨eF⟩⟩ := hF
  obtain ⟨n, m, U, V, hU, hV, b, ⟨eG⟩⟩ := hG
  have hp : Epi (cokernel.π b' ≫ eF.hom) := epi_comp _ _
  choose ι hι Z g hZ hεepi d hd using fun k : Fin n' =>
    exists_finite_lift_extensionByZeroUnit S R hEnough hqc (cokernel.π b) (hW k)
      (Sigma.ι (fun k' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (W k')) k ≫
        ((cokernel.π b' ≫ eF.hom) ≫ f) ≫ eG.inv)
  have _ : ∀ k, Finite (ι k) := hι
  refine hasFiniteExtensionByZeroPresentation_of_finite S R U (relationObjects ι Z V) hU
    (fun sx ↦ by cases sx with | inl x => exact hZ x.1 x.2 | inr j => exact hV j)
    (relationsMap S R U V ι Z b d) ?_
  exact cokernelIsoOfLifts S R U V W ι Z g b _ d hd hεepi ≪≫
    cokernelCompIsIso ((cokernel.π b' ≫ eF.hom) ≫ f) eG.inv ≪≫
    cokernelEpiComp (cokernel.π b' ≫ eF.hom) f

end Presentation

end Stacks.SheafOfModules

end
