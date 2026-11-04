module

public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.DevissageBounded.Basic

/-!
# Calculus of bounded dévissage filtrations

`Stacks.AlgebraicGeometry.DevissageBounded.HasDevissageWith` is the predicate "`F` carries a
finite filtration by coherent submodules, starting at a zero module, whose successive quotients
lie in the class `Q`" that the proof of [Stacks, Tag 01YF] produces. The predicate is stated
over a cut-off `n` with an `ℕ`-indexed family, and nothing in this repository manipulated such a
filtration: the only two producers were the empty one on a zero module and a transport of the
unbounded variant. This file supplies the two operations the proof of 01YF needs — transport
along an isomorphism, and appending one monomorphism on top — together with the two facts about
isomorphism-invariance they rest on.

The implementation notes of
`StacksFrontier/AlgebraicGeometry/DevissageNoetherian/Basic.lean` name the missing operation
precisely: against the filtration form, the source's phrase "splicing them yields one for `F`"
is a genuine obligation. Appending is the easy half of it and is here; the splicing itself is in
`StacksFrontier/AlgebraicGeometry/IrreducibleDevissage/Splicing.lean`, which is built on top of
this file.

## Main results

* `Stacks.AlgebraicGeometry.IrreducibleDevissage.supp_subset_of_iso`: one inclusion of the
  isomorphism invariance of the support, read off the stalk isomorphism obtained by composing
  `PresheafOfModules.toPresheaf` with `TopCat.Presheaf.stalkFunctor`. The invariance itself is
  `SheafOfModules.supp_eq_of_iso`.
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_of_iso'`: coherence transports along
  an isomorphism, with the coherence of the target as an **explicit** argument rather than an
  instance.
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.cokernelIsoOfCompIso`: composing with
  isomorphisms on either side leaves the cokernel unchanged.
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.hasDevissageWith_of_iso`: a bounded dévissage
  filtration of `F` is one of anything isomorphic to `F`.
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.hasDevissageWith_snoc`: **one monomorphism
  appended on top of a filtration.**

## Implementation notes

**Why `isCoherent_of_iso'` exists.** `Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso`
takes the coherence of its target as an instance argument. At an object as compound as
`cokernel f` that instance is *not* found from a hypothesis in the local context, because the
`HasCokernel` argument carried by the hypothesis's spelling of `cokernel f` and by the goal's
need not agree syntactically, and instance search is keyed on the head term. With the hypothesis
explicit the problem does not arise, since nothing is synthesized. Every use of coherence-transport
below goes through the primed form; the unprimed one silently fails.

**Why `hasDevissageWith_snoc` needs the class to be isomorphism-invariant.** The appended family
is `fun i => if i ≤ n then K i else F`, and in the branch `i + 1 ≤ n` the morphism is the old
`f i` conjugated by the two `eqToIso`s witnessing `H i = K i` and `H (i + 1) = K (i + 1)`. The
cokernel of a conjugate is only *isomorphic* to the cokernel of `f i`, never equal, so `Q` has
to be transported across that isomorphism. There is no way to avoid the conjugation: `if` does
not reduce inside a branch unless the `Decidable` instance is syntactically `isTrue`, and the
family is required to be total on `ℕ`.

**The three branches.** `i + 1 ≤ n` carries the old filtration; `i = n` is the appended step
`K n ≅ G ⟶ F`; `n < i` is a transport of the identity of `F`, on which nothing is required,
since the predicate constrains only indices `≤ n + 1`. The branch equations are applied to the
goal through `cokernelIsoOfEq` rather than by rewriting, because rewriting under `cokernel`
produces an ill-typed motive — the `HasCokernel` instance depends on the morphism being
rewritten.

## References

* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SheafOfModules TopologicalSpace
open Stacks.AlgebraicGeometry.CoherentDevissage
open Stacks.AlgebraicGeometry.DevissageBounded

universe u

namespace Stacks.AlgebraicGeometry.IrreducibleDevissage

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### The support is an isomorphism invariant -/

/-- **The stalks of two isomorphic sheaves of modules are isomorphic as abelian groups.** The
stalk of a sheaf of modules is the stalk of its underlying presheaf of abelian groups, so this is
the composite of `SheafOfModules.forget`, `PresheafOfModules.toPresheaf` and
`TopCat.Presheaf.stalkFunctor` applied to the isomorphism. -/
def stalkIsoOfIso {M N : X.Modules} (e : M ≅ N) (x : X) :
    (show TopCat.Presheaf Ab.{u} X from M.val.presheaf).stalk x ≅
      (show TopCat.Presheaf Ab.{u} X from N.val.presheaf).stalk x :=
  (TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso
    ((PresheafOfModules.toPresheaf _).mapIso
      ((SheafOfModules.forget _).mapIso e))

/-- One inclusion of `SheafOfModules.supp_eq_of_iso`: the stalk isomorphism carries a nonzero
element of a stalk of `M` to a nonzero element of the corresponding stalk of `N`. -/
theorem supp_subset_of_iso {M N : X.Modules} (e : M ≅ N) :
    SheafOfModules.supp M ⊆ SheafOfModules.supp N := by
  intro x hx
  obtain ⟨a, ha⟩ := hx
  refine ⟨(stalkIsoOfIso e x).hom a, fun h0 => ha ?_⟩
  have h1 : (stalkIsoOfIso e x).inv ((stalkIsoOfIso e x).hom a) = a :=
    CategoryTheory.Iso.hom_inv_id_apply (stalkIsoOfIso e x) a
  rw [← h1, h0, map_zero]

/-! ### Cokernels are unchanged by isomorphisms on either side -/

/-- Composing a morphism with isomorphisms on both sides does not change its cokernel. -/
def cokernelIsoOfCompIso {A B A' B' : X.Modules} (u : A' ≅ A) (g : A ⟶ B) (v : B ≅ B') :
    cokernel (u.hom ≫ g ≫ v.hom) ≅ cokernel g :=
  (cokernelEpiComp u.hom (g ≫ v.hom)).trans (cokernelCompIsIso g v.hom)

/-- Coherence transports along an isomorphism. This is
`Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso` with the coherence of the target as
  an
explicit argument: at an object as compound as `cokernel f` the instance is not found from a
hypothesis in the context, because the `HasCokernel` argument the two spellings carry need not
agree syntactically. -/
theorem isCoherent_of_iso' {M N : X.Modules} (e : M ≅ N) (h : N.IsCoherent) : M.IsCoherent :=
  have := h
  isCoherent_of_iso e

/-! ### Transporting and extending a filtration -/

/-- A property invariant under isomorphism holds for the cokernel of a morphism equal to a
conjugate `u.hom ≫ g ≫ v.hom` as soon as it holds for the cokernel of `g`. -/
private theorem cokernel_prop_of_eq_comp_iso {P : X.Modules → Prop}
    (hP : ∀ {M N : X.Modules}, (M ≅ N) → P M → P N) {A B A' B' : X.Modules} (u : A' ≅ A)
    (g : A ⟶ B) (v : B ≅ B') {g' : A' ⟶ B'} (h : g' = u.hom ≫ g ≫ v.hom)
    (hg : P (cokernel g)) : P (cokernel g') := by
  subst h
  exact hP (cokernelIsoOfCompIso u g v).symm hg

/-- A bounded dévissage filtration of `F` is one of anything isomorphic to `F`. -/
theorem hasDevissageWith_of_iso {Q : X.Modules → Prop} {F F' : X.Modules} (e : F ≅ F')
    (h : HasDevissageWith Q F) : HasDevissageWith Q F' := by
  obtain ⟨n, K, f, hmono, hzero, hcoh, hcoker, ⟨e'⟩, hq⟩ := h
  exact ⟨n, K, f, hmono, hzero, hcoh, hcoker, ⟨e'.trans e⟩, hq⟩

/-- **One mono appended on top of a filtration.** If `G` carries a bounded dévissage filtration
with quotients in `Q` and `ι : G ⟶ F` is a monomorphism whose cokernel is coherent and lies in
`Q`, then `F` carries one. -/
theorem hasDevissageWith_snoc {Q : X.Modules → Prop}
    (hQ : ∀ {M N : X.Modules}, (M ≅ N) → Q M → Q N)
    {G F : X.Modules} (ι : G ⟶ F) [Mono ι] (hFc : F.IsCoherent)
    (hck : (cokernel ι).IsCoherent) (hq : Q (cokernel ι))
    (hG : HasDevissageWith Q G) : HasDevissageWith Q F := by
  obtain ⟨n, K, f, hmono, hzero, hcoh, hcoker, ⟨e⟩, hq'⟩ := hG
  have hle : ∀ i : ℕ, i ≤ n → (if i ≤ n then K i else F) = K i := fun i hi => ite_eq_left hi
  have hgt : ∀ i : ℕ, n < i → (if i ≤ n then K i else F) = F := fun i hi => ite_eq_right (by omega)
  refine ⟨n + 1, fun i => if i ≤ n then K i else F, fun i =>
    if h1 : i + 1 ≤ n then
      (eqToIso (hle i (by omega))).hom ≫ f i ≫ (eqToIso (hle (i + 1) h1)).inv
    else if h2 : i ≤ n then
      ((eqToIso (hle i h2) ≪≫ eqToIso (congrArg K (show i = n by omega))) ≪≫ e).hom ≫ ι ≫
        (eqToIso (hgt (i + 1) (by omega))).inv
    else
      eqToHom ((hgt i (by omega)).trans (hgt (i + 1) (by omega)).symm),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- monomorphisms
    intro i hi
    dsimp only
    by_cases h1 : i + 1 ≤ n
    · rw [dite_eq_left h1]
      have := hmono i (by omega)
      infer_instance
    · rw [dite_eq_right h1, dite_eq_left (show i ≤ n by omega)]
      infer_instance
  · -- the bottom is zero
    dsimp only
    rw [hle 0 (Nat.zero_le n)]
    exact hzero
  · -- coherence of the terms
    intro i hi
    dsimp only
    by_cases h2 : i ≤ n
    · rw [hle i h2]; exact hcoh i h2
    · rw [hgt i (by omega)]; exact hFc
  · -- coherence of the quotients
    intro i hi
    dsimp only
    by_cases h1 : i + 1 ≤ n
    · exact cokernel_prop_of_eq_comp_iso (fun e h => isCoherent_of_iso' e.symm h) _ (f i)
        (eqToIso (hle (i + 1) h1)).symm (dite_eq_left h1) (hcoker i (by omega))
    · exact cokernel_prop_of_eq_comp_iso (fun e h => isCoherent_of_iso' e.symm h) _ ι
        (eqToIso (hgt (i + 1) (by omega))).symm
        ((dite_eq_right h1).trans (dite_eq_left (show i ≤ n by omega))) hck
  · -- the top is `F`
    exact ⟨eqToIso (hgt (n + 1) (by omega))⟩
  · -- the quotients lie in `Q`
    intro i hi
    dsimp only
    by_cases h1 : i + 1 ≤ n
    · exact cokernel_prop_of_eq_comp_iso hQ _ (f i) (eqToIso (hle (i + 1) h1)).symm
        (dite_eq_left h1) (hq' i (by omega))
    · exact cokernel_prop_of_eq_comp_iso hQ _ ι (eqToIso (hgt (i + 1) (by omega))).symm
        ((dite_eq_right h1).trans (dite_eq_left (show i ≤ n by omega))) hq

end Stacks.AlgebraicGeometry.IrreducibleDevissage


end
