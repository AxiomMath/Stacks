module

public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Functoriality

/-!
# Filtered homotopies restrict to the filtration steps

A filtered homotopy between two morphisms `φ, ψ : M ⟶ N` of filtered complexes
(`CochainComplex.FilteredHomotopic`) is a homotopy `h` between the underlying morphisms together
with, for each pair of degrees `i j` and each `p`, a lift `h^{i,j}_p : F^pM^i ⟶ F^pN^j` of
`h^{i,j}` along the inclusions of the filtration steps. Since those inclusions are degreewise
monomorphisms, the lifts are unique, and they assemble into an honest homotopy between the induced
morphisms `F^pM ⟶ F^pN` of the `p`-th filtration steps: the homotopy relation on the step follows
from the one upstairs by cancelling the mono `F^pN^i ⟶ N^i`. No compatibility of the lifts with
the differentials has to be assumed — post-composing the whole relation with that mono turns every
summand into the corresponding ambient one.

## Main results

* `CochainComplex.FilteredHomotopic.homotopy_natTrans_app`: a filtered homotopy between `φ` and
  `ψ` yields a homotopy between `φ.natTrans.app (op p)` and `ψ.natTrans.app (op p)`.
* `HomologicalComplex.quasiIso_of_homotopy_comp` and
  `CochainComplex.quasiIso_of_homotopy_comp`: if `f` and `h` are quasi-isomorphisms and `f ≫ g` is
  homotopic to `h`, then `g` is a quasi-isomorphism.
* `CochainComplex.quasiIso_natTrans_app_of_filteredHomotopic`: the filtration-step version of the
  previous result for a filtered homotopy.

## Implementation notes

`CochainComplex.FilteredHomotopic` is an existential statement, so the homotopy it produces on a
filtration step can only be extracted through `Classical.choice`; the conclusion of
`CochainComplex.FilteredHomotopic.homotopy_natTrans_app` is therefore phrased as
`Nonempty (Homotopy _ _)` rather than as a `Homotopy` carrying data.

`CategoryTheory.FilteredObject.Filtration.ι` has the *constant* functor as its codomain, so the
morphism `M.filtration.ι.app p` carries `((Functor.const ℤᵒᵖ).obj M.X).obj p` in an implicit
argument where every lemma about `M.X` spells it `M.X`; the two are definitionally but not
reducibly equal, so `rw` cannot bridge them. `CochainComplex.filtrationStepι` is the same morphism
with the reduced spelling, and all the lemmas below are stated through it so that the seam is
crossed exactly once, by the type ascription in its definition.
`CochainComplex.filtration_ι_app_comm` restates the chain-map condition at the unreduced spelling,
for consumers that present it that way.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace HomologicalComplex

variable {V : Type*} [Category* V] [Preadditive V] {ι : Type*} {c : ComplexShape ι}

/-- `dNext` is compatible with a commuting square: if a family `u` of maps between two complexes
lifts a family `v` along chain maps `a` and `b`, then `dNext i u` lifts `dNext i v`. -/
lemma dNext_comp_of_comm {K K' L L' : HomologicalComplex V c} (a : K ⟶ K') (b : L ⟶ L')
    (u : ∀ i j, K.X i ⟶ L.X j) (v : ∀ i j, K'.X i ⟶ L'.X j)
    (huv : ∀ i j, u i j ≫ b.f j = a.f i ≫ v i j) (i : ι) :
    dNext i u ≫ b.f i = a.f i ≫ dNext i v := by
  show (K.d i (c.next i) ≫ u (c.next i) i) ≫ b.f i
      = a.f i ≫ (K'.d i (c.next i) ≫ v (c.next i) i)
  rw [Category.assoc, huv, ← Category.assoc, ← a.comm, Category.assoc]

/-- `prevD` is compatible with a commuting square: if a family `u` of maps between two complexes
lifts a family `v` along chain maps `a` and `b`, then `prevD i u` lifts `prevD i v`. -/
lemma prevD_comp_of_comm {K K' L L' : HomologicalComplex V c} (a : K ⟶ K') (b : L ⟶ L')
    (u : ∀ i j, K.X i ⟶ L.X j) (v : ∀ i j, K'.X i ⟶ L'.X j)
    (huv : ∀ i j, u i j ≫ b.f j = a.f i ≫ v i j) (i : ι) :
    prevD i u ≫ b.f i = a.f i ≫ prevD i v := by
  show (u i (c.prev i) ≫ L.d (c.prev i) i) ≫ b.f i
      = a.f i ≫ (v i (c.prev i) ≫ L'.d (c.prev i) i)
  rw [Category.assoc, ← b.comm, ← Category.assoc, huv, Category.assoc]

/-- If `f` and `h` are quasi-isomorphisms and `f ≫ g` is homotopic to `h`, then `g` is a
quasi-isomorphism. -/
lemma quasiIso_of_homotopy_comp [CategoryWithHomology V] {K L M : HomologicalComplex V c}
    (f : K ⟶ L) (g : L ⟶ M) (h : K ⟶ M) (hf : QuasiIso f) (hh : QuasiIso h)
    (e : Homotopy (f ≫ g) h) : QuasiIso g := by
  refine ⟨fun i => (quasiIsoAt_iff_isIso_homologyMap g i).2 ?_⟩
  have hfg : homologyMap f i ≫ homologyMap g i = homologyMap h i := by
    rw [← homologyMap_comp, e.homologyMap_eq i]
  have : IsIso (homologyMap f i) := (quasiIsoAt_iff_isIso_homologyMap f i).1 (hf.quasiIsoAt i)
  have : IsIso (homologyMap h i) := (quasiIsoAt_iff_isIso_homologyMap h i).1 (hh.quasiIsoAt i)
  have : IsIso (homologyMap f i ≫ homologyMap g i) := by rw [hfg]; infer_instance
  exact IsIso.of_isIso_comp_left (homologyMap f i) (homologyMap g i)

end HomologicalComplex

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- If `f` and `h` are quasi-isomorphisms of cochain complexes and `f ≫ g` is homotopic to `h`,
then `g` is a quasi-isomorphism. -/
lemma quasiIso_of_homotopy_comp {C : Type*} [Category* C] [Abelian C]
    {L M N : CochainComplex C ℤ} {f : L ⟶ M} {g : M ⟶ N} {h : L ⟶ N}
    (hf : QuasiIso f) (hh : QuasiIso h) (e : Homotopy (f ≫ g) h) : QuasiIso g :=
  HomologicalComplex.quasiIso_of_homotopy_comp f g h hf hh e

section FilteredSteps

variable (M : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)

/-- The inclusion `F^pM ⟶ M` of a filtration step of a filtered complex, spelled with codomain
`M.X` rather than `((Functor.const ℤᵒᵖ).obj M.X).obj p`. The two are definitionally equal, but
only the former is the spelling in which the lemmas about `M.X` apply. -/
abbrev filtrationStepι (p : ℤᵒᵖ) : M.filtration.obj p ⟶ M.X :=
  M.filtration.ι.app p

/-- The inclusion of a filtration step commutes with the differentials. -/
@[reassoc]
lemma filtrationStepι_comm (p : ℤᵒᵖ) (i j : ℤ) :
    (M.filtration.obj p).d i j ≫ (filtrationStepι M p).f j
      = (filtrationStepι M p).f i ≫ M.X.d i j :=
  ((filtrationStepι M p).comm i j).symm

/-- `filtrationStepι_comm` at the spelling that `CategoryTheory.FilteredObject.Filtration.ι`
produces on its own, namely with the constant functor as the codomain of the inclusion; this is
the form in which `rw` meets it in goals that were not stated through `filtrationStepι`. -/
@[reassoc]
lemma filtration_ι_app_comm (p : ℤᵒᵖ) (i j : ℤ) :
    (M.filtration.obj p).d i j ≫ (M.filtration.ι.app p).f j
      = (M.filtration.ι.app p).f i ≫ M.X.d i j :=
  filtrationStepι_comm M p i j

variable {M}

/-- The map induced by a morphism of filtered complexes on the `p`-th filtration step is
compatible with the inclusions of the steps. -/
@[reassoc]
lemma natTrans_app_f_comp_filtrationStepι_f {N : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ}
    (φ : M ⟶ N) (p : ℤᵒᵖ) (i : ℤ) :
    (φ.natTrans.app p).f i ≫ (filtrationStepι N p).f i
      = (filtrationStepι M p).f i ≫ φ.hom.f i :=
  HomologicalComplex.congr_hom (φ.comm p) i

/-- A filtered homotopy between morphisms of filtered complexes restricts to a homotopy between
the induced morphisms of the `p`-th filtration steps. The conclusion is `Nonempty` because
`CochainComplex.FilteredHomotopic` only asserts the *existence* of the lifted homotopy
components. -/
lemma FilteredHomotopic.homotopy_natTrans_app {N : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ}
    {φ ψ : M ⟶ N} (h : FilteredHomotopic φ ψ) (p : ℤ) :
    Nonempty (Homotopy (φ.natTrans.app (op p)) (ψ.natTrans.app (op p))) := by
  obtain ⟨H, hH⟩ := h
  have hspec : ∀ i j : ℤ, (hH i j p).choose ≫ (filtrationStepι N (op p)).f j
      = (filtrationStepι M (op p)).f i ≫ H.hom i j := fun i j => (hH i j p).choose_spec
  refine ⟨{ hom := fun i j => (hH i j p).choose, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    rw [← cancel_mono ((filtrationStepι N (op p)).f j), hspec i j, H.zero i j hij, comp_zero,
      zero_comp]
  · intro i
    rw [← cancel_mono ((filtrationStepι N (op p)).f i),
      natTrans_app_f_comp_filtrationStepι_f, Preadditive.add_comp, Preadditive.add_comp,
      natTrans_app_f_comp_filtrationStepι_f,
      HomologicalComplex.dNext_comp_of_comm (filtrationStepι M (op p))
        (filtrationStepι N (op p)) _ H.hom hspec,
      HomologicalComplex.prevD_comp_of_comm (filtrationStepι M (op p))
        (filtrationStepι N (op p)) _ H.hom hspec,
      ← Preadditive.comp_add, ← Preadditive.comp_add, ← H.comm i]

/-- If `α` is a quasi-isomorphism on the `p`-th filtration step, and `α ≫ β` is filtered homotopic
to a `γ` which is also a quasi-isomorphism on the `p`-th step, then `β` is a quasi-isomorphism on
the `p`-th step. -/
lemma quasiIso_natTrans_app_of_filteredHomotopic
    {N P : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ} {α : M ⟶ N} {β : N ⟶ P} {γ : M ⟶ P}
    (h : FilteredHomotopic (α ≫ β) γ) (p : ℤ)
    (hα : QuasiIso (α.natTrans.app (op p))) (hγ : QuasiIso (γ.natTrans.app (op p))) :
    QuasiIso (β.natTrans.app (op p)) := by
  obtain ⟨e⟩ := h.homotopy_natTrans_app p
  exact quasiIso_of_homotopy_comp hα hγ e

end FilteredSteps

end CochainComplex
