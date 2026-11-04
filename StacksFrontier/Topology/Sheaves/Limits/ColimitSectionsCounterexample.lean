module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Limits.FilteredColimitSections

/-!
# A filtered system of sheaves whose sections miss the sections of the colimit (Stacks 009G)

Part (4) of Stacks 009F says that the canonical map
`Ψ : colimᵢ ℱᵢ(U) → (colimᵢ ℱᵢ)(U)` is bijective as soon as `U` has a cofinal system of finite
open coverings with quasi-compact pairwise intersections.  This file shows the hypothesis
cannot be dropped: there is a space `X`, a system `ℱ : ℕ ⥤ TopCat.Sheaf (Type) X` and an open
(namely `U = X`) for which `Ψ` is *not* bijective.

Take `X = ℕ` with the discrete topology, `Uₙ = {m : n ≤ m}` and `ℱₙ = jₙ,*𝐙` the pushforward
of the constant sheaf along `jₙ : Uₙ → X`.  Concretely `ℱₙ(V)` is the set of `𝐙`-valued
functions on `V ∩ Uₙ`, and that is how `sheafSystem` below builds it: as the sheaf of sections
of the fibre family `fiber n x = PLift (n ≤ x) → 𝐙`, a copy of `𝐙` at the points `x ≥ n` and a
singleton at the others.  (This presentation is available because `Uₙ` is discrete, so the
constant sheaf on it is the sheaf of all `𝐙`-valued functions.)  Every transition map
`ℱₙ → ℱₙ₊₁` forgets the coordinate at `n`.

The colimit kills every stalk: `ℱₙ,ₓ = 0` for `n > x`, because `{x}` is an open subset of `X`
missing `Uₙ`, so `(colimₙ ℱₙ)ₓ = 0` for every `x`.  Global sections of the system, on the other
hand, survive: `colimₙ ℱₙ(X) = colimₙ ∏_{m ≥ n} 𝐙` is the set of eventually-equal sequences,
which has more than one element.  Since a section of the sheafification is determined by its
germs, `Ψ` collapses all of `colimₙ ℱₙ(X)` to a single element, so it is not injective.

This is the example of the source with its two closed points `s₁, s₂` removed.  Those points
are what makes `Γ(X, colim ℱₙ) = M ⊕ M` while `colimₙ Γ(X, ℱₙ) = M` there, i.e. they turn the
failure into a failure of *surjectivity*; the whole space of the source is quasi-compact, so by
009F (2) injectivity cannot fail for it.  Deleting them makes `X` non-quasi-compact and leaves
the colimit sheaf with only trivial stalks, and the same mechanism — all stalks die, global
sections do not — now breaks injectivity, which is the cheaper half to exhibit.  Either way
the conclusion of 009F (4) fails, which is what the example is for.

Main results:

* `exists_system_canonicalMap_not_bijective` (`@[stacks 009G]`): a space, a system indexed by
  `ℕ` and an open on which the canonical map of 009F is not bijective.
* `SectionsCounterexample.not_hasFiniteCompactCofinalCovers_top`: for this space the hypothesis
  of 009F (4) indeed fails, so the counterexample is consistent with the lemma.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite

namespace DirectedColimitOfSheaves

namespace SectionsCounterexample

/-- The space of the example: the natural numbers with their (discrete) topology.  Every
subset is open, and the space is not quasi-compact. -/
abbrev space : TopCat.{0} := TopCat.of ℕ

/-- The open subset `{x}` of `space`; a singleton is open because the topology is discrete. -/
def pt (x : ℕ) : Opens space := ⟨{x}, isOpen_discrete _⟩

/-- The point `x` lies in the open set `pt x`. -/
lemma mem_pt (x : ℕ) : x ∈ pt x := rfl

/-- The only point of `pt x` is `x`. -/
lemma eq_of_mem_pt {x y : ℕ} (hy : y ∈ pt x) : y = x := hy

/-- The fibre of the `n`-th sheaf of the system at the point `x`: a copy of `𝐙` when
`n ≤ x`, and a singleton otherwise.  Writing it as a function type out of `PLift (n ≤ x)`
avoids a case distinction: the domain is a singleton when `n ≤ x` and empty otherwise. -/
def fiber (n x : ℕ) : Type := PLift (n ≤ x) → ℤ

/-- The transition map on fibres: for `n ≤ m` it is the identity of `𝐙` at the points
`x ≥ m` and the unique map to a singleton at the points `x < m`. -/
def fiberMap {n m : ℕ} (h : n ≤ m) (x : ℕ) (f : fiber n x) : fiber m x :=
  fun p => f ⟨h.trans p.down⟩

/-- The system `ℱ : ℕ ⥤ TopCat.Sheaf (Type) X` of the example.  `ℱₙ` is the sheaf of sections
of the fibre family `fiber n`, i.e. the pushforward `jₙ,*𝐙` of the constant sheaf along the
inclusion `jₙ : {m : n ≤ m} → ℕ`: its sections over `V` are the `𝐙`-valued functions on
`V ∩ {m : n ≤ m}`.  The transition map `ℱₙ → ℱₘ` for `n ≤ m` restricts a function to the
smaller set. -/
noncomputable def sheafSystem : ℕ ⥤ TopCat.Sheaf (Type) space where
  obj n := TopCat.sheafToTypes space (fiber n)
  map h := { hom := { app := fun _ => ↾fun σ x => fiberMap (leOfHom h) x (σ x) } }

/-- Sections of `ℱₙ` over an open all of whose points are `< n` form a subsingleton: the
fibres of `fiber n` at those points are singletons. -/
lemma sections_eq_of_lt (x n : ℕ) (hn : x < n)
    (σ τ : ((presheafSystem sheafSystem).obj n).obj (op (pt x))) : σ = τ := by
  refine funext fun y => funext fun p => ?_
  have hy : (y : ℕ) = x := eq_of_mem_pt y.2
  exact absurd (le_of_le_of_eq p.down hy) (by omega)

/-- The constant section of value `c` of `ℱ₀` over the whole space. -/
def constSec (c : ℤ) : ((presheafSystem sheafSystem).obj 0).obj (op ⊤) := fun _ _ => c

/-- The image of `constSec c` in `ℱ'(X) = colimₙ ℱₙ(X)`. -/
noncomputable def constSecColim (c : ℤ) : (colimitPresheaf sheafSystem).obj (op ⊤) :=
  (colimit.ι (presheafSystem sheafSystem) 0).app (op ⊤) (constSec c)

/-- Distinct constants give distinct global sections of `ℱ' = colimₙ ℱₙ`: a transition map
sends the constant sequence `c` to the constant sequence `c`, and no transition map out of `0`
identifies two different constants, because the space has points above every index. -/
lemma constSecColim_injective {c c' : ℤ} (h : constSecColim c = constSecColim c') : c = c' := by
  obtain ⟨m, g, hg⟩ :=
    (colimit_eq_iff_eventual sheafSystem ⊤ 0 (constSec c) (constSec c')).mp h
  exact congrFun (congrFun hg ⟨m, trivial⟩) ⟨le_rfl⟩

/-- All germs of the sections `constSecColim c` coincide: at a point `x` the section
restricts to a section over `{x}`, and there it becomes the unique section of `ℱₓ₊₁` over
`{x}`, since the fibre of `fiber (x + 1)` at `x` is a singleton. -/
lemma germ_constSecColim_eq (c c' : ℤ) (x : ℕ) (hx : x ∈ (⊤ : Opens space)) :
    (colimitPresheaf sheafSystem).germ ⊤ x hx (constSecColim c) =
      (colimitPresheaf sheafSystem).germ ⊤ x hx (constSecColim c') := by
  have key : ∀ d : ℤ, (colimitPresheaf sheafSystem).germ ⊤ x hx (constSecColim d) =
      (colimitPresheaf sheafSystem).germ (pt x) x (mem_pt x)
        ((colimit.ι (presheafSystem sheafSystem) 0).app (op (pt x))
          (((presheafSystem sheafSystem).obj 0).map (homOfLE (le_top (a := pt x))).op
            (constSec d))) := fun d => by
    rw [← (colimitPresheaf sheafSystem).germ_res_apply (homOfLE (le_top (a := pt x))) x
      (mem_pt x)]
    exact congrArg _ (ConcreteCategory.congr_hom
      ((colimit.ι (presheafSystem sheafSystem) 0).naturality
        (homOfLE (le_top (a := pt x))).op) (constSec d)).symm
  rw [key c, key c']
  exact congrArg _ ((colimit_eq_iff_eventual sheafSystem (pt x) 0 _ _).mpr
    ⟨x + 1, homOfLE (Nat.zero_le _), sections_eq_of_lt x (x + 1) (Nat.lt_succ_self x) _ _⟩)

/-- The canonical map of 009F identifies the global sections `constSecColim c` for all `c`:
they have the same germ at every point, and the sheafification is separated. -/
lemma canonicalMap_constSecColim_eq (c c' : ℤ) :
    canonicalMap sheafSystem ⊤ (constSecColim c) = canonicalMap sheafSystem ⊤ (constSecColim c') :=
  (canonicalMap_eq_iff sheafSystem ⊤ _ _).mpr fun x hx => germ_constSecColim_eq c c' x hx

/-- The hypothesis of 009F (4) fails for the whole space: the covering by singletons has no
finite refinement, since `ℕ` is infinite. -/
lemma not_hasFiniteCompactCofinalCovers_top :
    ¬ HasFiniteCompactCofinalCovers (X := space) ⊤ := by
  intro h
  obtain ⟨K, hK, W, -, hWcover, hWref, -⟩ :=
    h (fun j : ℕ => pt j) (fun _ => le_top) fun x _ => Opens.mem_iSup.mpr ⟨x, mem_pt x⟩
  have : Finite K := hK
  choose j hj using hWref
  have hsurj : Function.Surjective j := by
    intro x
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (hWcover (Opens.mem_top x))
    exact ⟨k, (eq_of_mem_pt (hj k hk)).symm⟩
  have : Finite ℕ := Finite.of_surjective j hsurj
  exact not_finite ℕ

end SectionsCounterexample

/-- **Stacks 009G.**  Some hypothesis is necessary in part (4) of 009F: there are a space `X`
and a system of sheaves of sets `ℱ : ℕ ⥤ TopCat.Sheaf (Type) X` indexed by the directed set
`ℕ` for which the canonical map `Ψ : colimₙ ℱₙ(X) → (colimₙ ℱₙ)(X)` is not bijective.

The witness is `SectionsCounterexample.sheafSystem`, the pushforwards `jₙ,*𝐙` of the constant
sheaf along the inclusions of the cofinal subsets `{m : n ≤ m}` of the discrete space `ℕ`.  All
its stalks die in the colimit while its global sections do not, so `Ψ` is not injective; and
`SectionsCounterexample.not_hasFiniteCompactCofinalCovers_top` checks that the hypothesis of
009F (4) really fails here. -/
@[stacks 009G]
theorem exists_system_canonicalMap_not_bijective :
    ∃ (X : TopCat) (F : ℕ ⥤ TopCat.Sheaf (Type) X),
      ¬ Function.Bijective (canonicalMap F ⊤) := by
  refine ⟨SectionsCounterexample.space, SectionsCounterexample.sheafSystem, fun hbij => ?_⟩
  have h01 : (0 : ℤ) = 1 :=
    SectionsCounterexample.constSecColim_injective
      (hbij.injective (SectionsCounterexample.canonicalMap_constSecColim_eq 0 1))
  exact zero_ne_one h01

end DirectedColimitOfSheaves
