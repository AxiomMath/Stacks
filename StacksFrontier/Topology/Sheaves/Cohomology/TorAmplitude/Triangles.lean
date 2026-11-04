module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

This is Stacks project Tag 08CJ (Lemma 20.48.6), in the section on Tor dimension
(Tag 08CF) of the chapter Cohomology of Sheaves.

Let $(X, \mathcal{O}_X)$ be a ringed space and let $D(\mathcal{O}_X)$ denote the derived
category of the category of $\mathcal{O}_X$-modules.

## Main Definition (Tor-amplitude, Stacks Tag 08CG)

Let $E$ be an object of $D(\mathcal{O}_X)$ and let $a, b \in \mathbf{Z}$ with $a \le b$.
We say that $E$ *has tor-amplitude in $[a, b]$* if for every $\mathcal{O}_X$-module
$\mathcal{F}$ and every integer $i \notin [a, b]$ (i.e. $i < a$ or $b < i$) we have
$$ H^i\bigl(E \otimes_{\mathcal{O}_X}^{\mathbf{L}} \mathcal{F}\bigr) = 0, $$
where $\otimes_{\mathcal{O}_X}^{\mathbf{L}}$ denotes the derived tensor product in
$D(\mathcal{O}_X)$, the module $\mathcal{F}$ is regarded as the object $\mathcal{F}[0]$,
and $H^i(-)$ denotes the $i$-th cohomology sheaf.

## Main Statements

Let $(K, L, M, f, g, h)$ be a distinguished triangle
$K \xrightarrow{f} L \xrightarrow{g} M \xrightarrow{h} K[1]$ in $D(\mathcal{O}_X)$,
and let $a, b \in \mathbf{Z}$ with $a \le b$. Then:

1. If $K$ has tor-amplitude in $[a+1, b+1]$ and $L$ has tor-amplitude in $[a, b]$,
   then $M$ has tor-amplitude in $[a, b]$.
2. If $K$ and $M$ both have tor-amplitude in $[a, b]$, then $L$ has tor-amplitude in $[a, b]$.
3. If $L$ has tor-amplitude in $[a+1, b+1]$ and $M$ has tor-amplitude in $[a, b]$,
   then $K$ has tor-amplitude in $[a+1, b+1]$.

## Modeling notes

* The category of $\mathcal{O}_X$-modules over a ringed space, its derived category and the
  derived tensor product $- \otimes^{\mathbf L} \mathcal F$ are not all available as usable
  structures in current Mathlib.  We model the situation faithfully as follows.

  - `M` is the abelian category of $\mathcal{O}_X$-modules.  We use Mathlib's
    `DerivedCategory M` as $D(\mathcal{O}_X)$, which is pretriangulated and triangulated and
    comes equipped with cohomology (homology) sheaf functors
    `DerivedCategory.homologyFunctor M i : DerivedCategory M ⥤ M`, playing the role of $H^i$.

  - For each $\mathcal{O}_X$-module `F : M`, the derived tensor product
    $- \otimes^{\mathbf L} \mathcal F$ is an exact (triangulated) endofunctor of
    $D(\mathcal{O}_X)$.  We model the whole family by a function
    `derTensor : M → (DerivedCategory M ⥤ DerivedCategory M)` together with the assumption
    that each `derTensor F` is a triangulated functor (`CommShift ℤ` and `IsTriangulated`).
    These are precisely the properties of $- \otimes^{\mathbf L} \mathcal F$ used in the
    Stacks proof: it is an exact functor of triangulated categories, hence sends a
    distinguished triangle to a distinguished triangle, which then gives the long exact
    sequence of cohomology sheaves.

* Indexing: `ℤ` is used for the cohomological degree.  The set $[a,b]$ is encoded by its
  complement: $i \notin [a,b]$ is `i < a ∨ b < i`.  The hypothesis $a \le b$ guarantees the
  ranges $[a,b]$ and $[a+1,b+1]$ are nonempty, exactly as in the Stacks statement.
-/

open CategoryTheory Limits Pretriangulated

namespace TorAmplitude

variable {M : Type*} [Category M] [Abelian M] [HasDerivedCategory M]
  (derTensor : M → (DerivedCategory M ⥤ DerivedCategory M))
  [∀ F, (derTensor F).CommShift ℤ] [∀ F, (derTensor F).IsTriangulated]

-- Main Definition (Tor-amplitude, Stacks Tag 08CG)

/-- An object `E` of `D(O_X)` *has tor-amplitude in `[a, b]`* if for every `O_X`-module `F`
and every integer `i` with `i < a` or `b < i` (i.e. `i ∉ [a, b]`), the `i`-th cohomology
sheaf `H^i (E ⊗^L F)` of the derived tensor product is zero.  Here the derived tensor
product `- ⊗^L F` is modeled by the triangulated endofunctor `derTensor F`. -/
def HasTorAmplitude (E : DerivedCategory M) (a b : ℤ) : Prop :=
  ∀ (F : M) (i : ℤ), (i < a ∨ b < i) →
    IsZero ((DerivedCategory.homologyFunctor M i).obj ((derTensor F).obj E))

-- Main Statement(s)

/-- Stacks Tag 08CJ (1): in a distinguished triangle `K → L → M → K[1]`, if `K` has
tor-amplitude in `[a+1, b+1]` and `L` has tor-amplitude in `[a, b]`, then `M` has
tor-amplitude in `[a, b]`. -/
@[stacks 08CJ "(1)", sga "6 I 5.3" "partial", sga "6 III 3.2" "Triangulatedness clause"]
theorem hasTorAmplitude_obj₃ (T : Triangle (DerivedCategory M))
    (hT : T ∈ distinguishedTriangles) (a b : ℤ)
    (hK : HasTorAmplitude derTensor T.obj₁ (a + 1) (b + 1))
    (hL : HasTorAmplitude derTensor T.obj₂ a b) :
    HasTorAmplitude derTensor T.obj₃ a b := by
  intro F i hi
  set G := derTensor F
  have hT' : G.mapTriangle.obj T ∈ distinguishedTriangles :=
    Functor.IsTriangulated.map_distinguished T hT
  have hexact := (DerivedCategory.homologyFunctor M 0).homologySequence_exact₃
    (G.mapTriangle.obj T) hT' i (i + 1) rfl
  refine hexact.isZero_X₂ ?_ ?_
  · have hz : IsZero ((DerivedCategory.homologyFunctor M i).obj (G.obj T.obj₂)) :=
      hL F i hi
    exact hz.eq_of_src _ _
  · have hi' : i + 1 < a + 1 ∨ b + 1 < i + 1 := by omega
    have hz : IsZero ((DerivedCategory.homologyFunctor M (i+1)).obj (G.obj T.obj₁)) :=
      hK F (i+1) hi'
    exact hz.eq_of_tgt _ _

/-- Stacks Tag 08CJ (2): in a distinguished triangle `K → L → M → K[1]`, if `K` and `M`
both have tor-amplitude in `[a, b]`, then `L` has tor-amplitude in `[a, b]`. -/
@[stacks 08CJ "(2)", sga "6 I 5.3" "partial", sga "6 III 3.2" "Triangulatedness clause"]
theorem hasTorAmplitude_obj₂ (T : Triangle (DerivedCategory M))
    (hT : T ∈ distinguishedTriangles) (a b : ℤ)
    (hK : HasTorAmplitude derTensor T.obj₁ a b)
    (hM : HasTorAmplitude derTensor T.obj₃ a b) :
    HasTorAmplitude derTensor T.obj₂ a b := by
  intro F i hi
  set G := derTensor F
  have hT' : G.mapTriangle.obj T ∈ distinguishedTriangles :=
    Functor.IsTriangulated.map_distinguished T hT
  have hexact := (DerivedCategory.homologyFunctor M 0).homologySequence_exact₂
    (G.mapTriangle.obj T) hT' i
  refine hexact.isZero_X₂ ?_ ?_
  · have hz : IsZero ((DerivedCategory.homologyFunctor M i).obj (G.obj T.obj₁)) :=
      hK F i hi
    exact hz.eq_of_src _ _
  · have hz : IsZero ((DerivedCategory.homologyFunctor M i).obj (G.obj T.obj₃)) :=
      hM F i hi
    exact hz.eq_of_tgt _ _

/-- Stacks Tag 08CJ (3): in a distinguished triangle `K → L → M → K[1]`, if `L` has
tor-amplitude in `[a+1, b+1]` and `M` has tor-amplitude in `[a, b]`, then `K` has
tor-amplitude in `[a+1, b+1]`. -/
@[stacks 08CJ "(3)", sga "6 I 5.3" "partial", sga "6 III 3.2" "Triangulatedness clause"]
theorem hasTorAmplitude_obj₁ (T : Triangle (DerivedCategory M))
    (hT : T ∈ distinguishedTriangles) (a b : ℤ)
    (hL : HasTorAmplitude derTensor T.obj₂ (a + 1) (b + 1))
    (hM : HasTorAmplitude derTensor T.obj₃ a b) :
    HasTorAmplitude derTensor T.obj₁ (a + 1) (b + 1) := by
  intro F i hi
  set G := derTensor F
  have hT' : G.mapTriangle.obj T ∈ distinguishedTriangles :=
    Functor.IsTriangulated.map_distinguished T hT
  have hexact := (DerivedCategory.homologyFunctor M 0).homologySequence_exact₁
    (G.mapTriangle.obj T) hT' (i - 1) i (by omega)
  refine hexact.isZero_X₂ ?_ ?_
  · have hi' : i - 1 < a ∨ b < i - 1 := by omega
    have hz : IsZero ((DerivedCategory.homologyFunctor M (i-1)).obj (G.obj T.obj₃)) :=
      hM F (i-1) hi'
    exact hz.eq_of_src _ _
  · have hz : IsZero ((DerivedCategory.homologyFunctor M i).obj (G.obj T.obj₂)) :=
      hL F i hi
    exact hz.eq_of_tgt _ _

end TorAmplitude
