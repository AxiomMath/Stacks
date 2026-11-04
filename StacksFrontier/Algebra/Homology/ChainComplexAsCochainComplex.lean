module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Data.Set.Finite.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A chain complex read as a cochain complex

A `ℤ`-indexed chain complex and a `ℤ`-indexed cochain complex carry the same information: the
two complex shapes `ComplexShape.down ℤ` and `ComplexShape.up ℤ` are exchanged by `n ↦ -n`.
Mathlib records this as the equivalence of categories
`ChainComplex.cochainComplexEquivalence`, built from the embedding of complex shapes
`ComplexShape.embeddingUpIntDownInt`.

This file gives the one object of that equivalence a name of its own, `asCochain`, and provides
what a consumer of a chain complex needs in order to feed it to a cohomological construction:
the degreewise and differentialwise descriptions, the identification of homology in degree `n`
with homology of the original complex in degree `-n`, the fact that quasi-isomorphisms are
reflected and preserved, and the reindexing of a complex concentrated in degree zero.

## Main definitions

* `Stacks.ChainComplex.asCochain`: the cochain complex `n ↦ K_{-n}` attached to a chain
  complex `K`.
* `Stacks.ChainComplex.asCochainMap`: the morphism of cochain complexes attached to a morphism
  of chain complexes.
* `Stacks.ChainComplex.asCochainHomologyIso`: `Hⁿ(asCochain K) ≅ H_{-n}(K)`.
* `Stacks.ChainComplex.asCochainSingleZeroIso`: a chain complex concentrated in degree zero,
  read as a cochain complex, is the cochain complex concentrated in degree zero on the same
  object.

## Main results

* `Stacks.ChainComplex.quasiIsoAt_asCochainMap_iff`: a morphism of chain complexes is a
  quasi-isomorphism in degree `-n` if and only if the associated morphism of cochain complexes
  is one in degree `n`.
* `Stacks.ChainComplex.quasiIso_asCochainMap`: **a quasi-isomorphism of chain complexes becomes
  a quasi-isomorphism of cochain complexes.**
* `Stacks.ChainComplex.isZero_asCochain_X_iff`: the degrees in which the cochain complex
  vanishes are the negatives of those in which the chain complex vanishes, so a chain complex
  with finitely many nonvanishing terms has a cochain complex with finitely many nonvanishing
  terms.

## Implementation notes

`asCochain` is the restriction along `ComplexShape.embeddingUpIntDownInt`, so its term in degree
`n` is *definitionally* `K.X (-n)` and its differential from `m` to `n` is definitionally
`K.d (-m) (-n)`; the descriptions below are `rfl`, and that is what makes the identification of
the short complexes computing homology available from `HomologicalComplex.restriction.sc'Iso`
with no transport.

The reindexing of a complex concentrated in degree zero cannot be an equality of complexes,
because the degree-`n` term of `HomologicalComplex.single` is `if n = 0 then A else 0` and the
two conditions `-n = 0` and `n = 0`, while equivalent, are not the same proposition. The
isomorphism is therefore assembled degreewise out of `if_congr`; both complexes have vanishing
differentials, so there is nothing to check for the compatibility.
-/

@[expose] public section

open CategoryTheory Category Limits HomologicalComplex

universe v u

namespace Stacks.ChainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- **A `ℤ`-indexed chain complex read as a `ℤ`-indexed cochain complex**: the complex whose
term in degree `n` is `K_{-n}`, obtained by restricting along the embedding of complex shapes
`n ↦ -n`. -/
@[ega "0 11.2.1"]
noncomputable abbrev asCochain (K : _root_.ChainComplex C ℤ) : CochainComplex C ℤ :=
  K.restriction ComplexShape.embeddingUpIntDownInt

/-- The term of `asCochain K` in degree `n` is the term of `K` in degree `-n`. -/
@[ega "0 11.2.1" "partial"]
theorem asCochain_X (K : _root_.ChainComplex C ℤ) (n : ℤ) :
    (asCochain K).X n = K.X (-n) :=
  rfl

/-- The differential of `asCochain K` from degree `m` to degree `n` is the differential of `K`
from degree `-m` to degree `-n`. -/
@[ega "0 11.2.1" "partial"]
theorem asCochain_d (K : _root_.ChainComplex C ℤ) (m n : ℤ) :
    (asCochain K).d m n = K.d (-m) (-n) :=
  rfl

/-- **A morphism of chain complexes read as a morphism of cochain complexes.** -/
noncomputable abbrev asCochainMap {K L : _root_.ChainComplex C ℤ} (f : K ⟶ L) :
    asCochain K ⟶ asCochain L :=
  restrictionMap f ComplexShape.embeddingUpIntDownInt

/-- The component of `asCochainMap f` in degree `n` is the component of `f` in degree `-n`. -/
theorem asCochainMap_f {K L : _root_.ChainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    (asCochainMap f).f n = f.f (-n) :=
  rfl

/-- `asCochainMap` sends the identity of `K` to the identity of `asCochain K`. -/
@[simp]
theorem asCochainMap_id (K : _root_.ChainComplex C ℤ) : asCochainMap (𝟙 K) = 𝟙 _ := rfl

/-- `asCochainMap` sends a composite of morphisms of chain complexes to the composite of the
associated morphisms of cochain complexes. -/
@[simp, reassoc]
theorem asCochainMap_comp {K L M : _root_.ChainComplex C ℤ} (f : K ⟶ L) (g : L ⟶ M) :
    asCochainMap (f ≫ g) = asCochainMap f ≫ asCochainMap g := rfl

/-- `asCochain K` vanishes in degree `n` exactly when `K` vanishes in degree `-n`. -/
theorem isZero_asCochain_X_iff (K : _root_.ChainComplex C ℤ) (n : ℤ) :
    IsZero ((asCochain K).X n) ↔ IsZero (K.X (-n)) :=
  Iff.rfl

/-- **The set of degrees in which `asCochain K` does not vanish is finite as soon as the set of
degrees in which `K` does not vanish is**, being its image under `n ↦ -n`. -/
theorem finite_not_isZero_asCochain_X (K : _root_.ChainComplex C ℤ)
    (h : {i : ℤ | ¬ IsZero (K.X i)}.Finite) :
    {i : ℤ | ¬ IsZero ((asCochain K).X i)}.Finite := by
  refine (Set.Finite.image (fun i => -i) h).subset fun i hi => ?_
  exact ⟨-i, (isZero_asCochain_X_iff K i).not.1 hi, neg_neg i⟩

/-- The comparison isomorphisms of a restriction of complexes are natural in the complex. -/
theorem restrictionXIso_hom_naturality {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} {K L : HomologicalComplex C c'} (φ : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff] {i : ι} {i' : ι'} (h : e.f i = i') :
    (K.restrictionXIso e h).hom ≫ φ.f i' =
      (restrictionMap φ e).f i ≫ (L.restrictionXIso e h).hom := by
  subst h
  exact (id_comp _).trans (comp_id _).symm

section Homology

variable [CategoryWithHomology C]

/-- **The cohomology of `asCochain K` in degree `n` is the homology of `K` in degree `-n`.** -/
noncomputable def asCochainHomologyIso (K : _root_.ChainComplex C ℤ) (n : ℤ) :
    (asCochain K).homology n ≅ K.homology (-n) :=
  K.restrictionHomologyIso ComplexShape.embeddingUpIntDownInt (n - 1) n (n + 1)
    (by simp) (by simp) (i' := -n + 1) (j' := -n) (k' := -n - 1)
    (by simp; omega) (by simp) (by simp; omega)
    ((ComplexShape.down ℤ).prev_eq' (show -n + 1 = -n + 1 from rfl))
    ((ComplexShape.down ℤ).next_eq' (show -n - 1 + 1 = -n by omega))

/-- A morphism of complexes is a quasi-isomorphism in a degree in the image of an embedding of
complex shapes if and only if its restriction along that embedding is one in the corresponding
degree, provided the neighbouring degrees correspond as well. -/
theorem quasiIsoAt_restrictionMap_iff {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} {K L : HomologicalComplex C c'} (φ : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff]
    (i j k : ι) {i' j' k' : ι'} (hi : c.prev j = i) (hk : c.next j = k)
    (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
    (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k') :
    QuasiIsoAt (restrictionMap φ e) j ↔ QuasiIsoAt φ j' := by
  rw [quasiIsoAt_iff' _ i j k hi hk, quasiIsoAt_iff' φ i' j' k' hi'' hk'']
  exact ShortComplex.quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (restriction.sc'Iso K e i j k hi' hj' hk' hi'' hk'')
      (restriction.sc'Iso L e i j k hi' hj' hk' hi'' hk'')
      (by ext <;> exact restrictionXIso_hom_naturality φ e ‹_›))

/-- **A morphism of chain complexes is a quasi-isomorphism in degree `-n` if and only if the
associated morphism of cochain complexes is one in degree `n`.** -/
theorem quasiIsoAt_asCochainMap_iff {K L : _root_.ChainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    QuasiIsoAt (asCochainMap f) n ↔ QuasiIsoAt f (-n) :=
  quasiIsoAt_restrictionMap_iff f ComplexShape.embeddingUpIntDownInt (n - 1) n (n + 1)
    (i' := -n + 1) (j' := -n) (k' := -n - 1)
    (by simp) (by simp) (by simp; omega) (by simp) (by simp; omega)
    ((ComplexShape.down ℤ).prev_eq' (show -n + 1 = -n + 1 from rfl))
    ((ComplexShape.down ℤ).next_eq' (show -n - 1 + 1 = -n by omega))

/-- **A quasi-isomorphism of chain complexes becomes a quasi-isomorphism of cochain
complexes.** -/
instance quasiIso_asCochainMap {K L : _root_.ChainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (asCochainMap f) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_asCochainMap_iff]
  infer_instance

end Homology

section Single

variable [HasZeroObject C]

/-- **A chain complex concentrated in degree zero, read as a cochain complex, is the cochain
complex concentrated in degree zero on the same object.** -/
noncomputable def asCochainSingleZeroIso (A : C) :
    asCochain ((single C (ComplexShape.down ℤ) 0).obj A) ≅
      (single C (ComplexShape.up ℤ) 0).obj A :=
  Hom.isoOfComponents (fun _ => eqToIso (if_congr neg_eq_zero rfl rfl))
    (fun _ _ _ => comp_zero.trans zero_comp.symm)

end Single

end Stacks.ChainComplex

end
