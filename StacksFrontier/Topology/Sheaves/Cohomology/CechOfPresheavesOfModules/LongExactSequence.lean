module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import StacksFrontier.CategoryTheory.Sites.CechComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The long exact sequence of Čech cohomology

Let `U : ι → C` be a family of objects of a category with finite products, let `A` be an
abelian category with `ι`-indexed products, and let `0 ⟶ P₁ ⟶ P₂ ⟶ P₃ ⟶ 0` be a short
complex of presheaves `Cᵒᵖ ⥤ A`. If the sequence of sections is short exact over every
object `inter U x` occurring in the Čech complex of `U`, then the Čech complexes form a
short exact sequence of cochain complexes, and therefore fit into a long exact sequence of
Čech cohomology objects. This is the content of [Stacks, Tag 01EK]: the functors
`P ↦ Ȟ^n(𝒰, P)` form a `δ`-functor on the presheaf category.

All names are in the namespace `Stacks.CategoryTheory.CechComplex`.

## Main results

* `shortExact_pi_map` says that a product of short exact sequences is short exact, for an
  abelian category whose products of the relevant size are exact (Grothendieck's axiom
  AB4*).
* `shortExact_map_cechComplexFunctor` is the Čech half of [Stacks, Tag 01EJ]: a short
  complex of presheaves whose sections are short exact over every `inter U x` is sent by
  the Čech complex functor to a short exact sequence of cochain complexes.
* `cechδ` is the connecting map `Ȟ^n(𝒰, P₃) ⟶ Ȟ^(n+1)(𝒰, P₁)`, and `cech_exact₁`,
  `cech_exact₂`, `cech_exact₃` are the three exactness statements that assemble into the
  long exact sequence of [Stacks, Tag 01EK].
* `isZero_cechHomology_X₃`, a step of [Stacks, Tag 01EW]: if `P₁` and `P₂` have vanishing
  higher Čech cohomology then so does `P₃`.

## Implementation notes

The index type `ι` is left in its own universe `w`, independent of the universes of `C` and
of `A`. Mathlib's `CategoryTheory.cechComplexFunctor` already asks only for
`HasProducts.{w} A`, and the one extra hypothesis the long exact sequence needs is that
`w`-indexed products in `A` are exact, i.e. `CategoryTheory.AB4StarOfSize.{w} A`. Both are
instances for `A = AddCommGrpCat.{u}` and `A = ModuleCat.{u} R` when `w` is `0` or `u`, so a
covering indexed by `Fin n` is usable directly, with no `ULift` reindexing of the index type.

## References

* [Stacks Project, Tag 01EJ](https://stacks.math.columbia.edu/tag/01EJ)
* [Stacks Project, Tag 01EK](https://stacks.math.columbia.edu/tag/01EK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v v' u u'

namespace Stacks.CategoryTheory.CechComplex

noncomputable section

/-! ### Products of short exact sequences -/

section Products

variable {A : Type u'} [Category.{v'} A] [Abelian A]

/-- `CategoryTheory.Limits.Pi.map` is additive in the family of morphisms. -/
theorem pi_map_add {J : Type w} {X Y : J → A} [HasProduct X] [HasProduct Y]
    (p q : ∀ j, X j ⟶ Y j) :
    Limits.Pi.map (fun j ↦ p j + q j) = Limits.Pi.map p + Limits.Pi.map q :=
  Limits.Pi.hom_ext _ _ fun j ↦ by
    rw [Limits.Pi.map_π, Preadditive.add_comp, Limits.Pi.map_π, Limits.Pi.map_π,
      Preadditive.comp_add]

variable {J : Type w} [HasProducts.{w} A] {X Y Z : J → A}
  (f : ∀ j, X j ⟶ Y j) (g : ∀ j, Y j ⟶ Z j) (hz : ∀ j, f j ≫ g j = 0)

/-- The short complex of discrete diagrams determined by a family of short complexes. Its image
under `CategoryTheory.Limits.lim` is the product of the family. -/
def piDiscrete : ShortComplex (Discrete J ⥤ A) where
  X₁ := Discrete.functor X
  X₂ := Discrete.functor Y
  X₃ := Discrete.functor Z
  f := Discrete.natTrans fun j ↦ f j.as
  g := Discrete.natTrans fun j ↦ g j.as
  zero := NatTrans.ext (funext fun j ↦ hz j.as)

/-- Evaluating `piDiscrete` at an index recovers the corresponding member of the family of short
complexes. -/
def piDiscreteMapEvaluationIso (j : Discrete J) :
    (piDiscrete f g hz).map ((evaluation (Discrete J) A).obj j) ≅
      ShortComplex.mk (f j.as) (g j.as) (hz j.as) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [piDiscrete])
    (by simp [piDiscrete])

omit [HasProducts.{w} A] in
/-- A family of short exact sequences gives a short exact sequence of discrete diagrams. -/
theorem shortExact_piDiscrete
    (h : ∀ j, (ShortComplex.mk (f j) (g j) (hz j)).ShortExact) :
    (piDiscrete f g hz).ShortExact := by
  have hmono : Mono (piDiscrete f g hz).f :=
    (NatTrans.mono_iff_mono_app (piDiscrete f g hz).f).2 fun j ↦
      ((h j.as).mono_f : Mono (f j.as))
  have hepi : Epi (piDiscrete f g hz).g :=
    (NatTrans.epi_iff_epi_app (piDiscrete f g hz).g).2 fun j ↦
      ((h j.as).epi_g : Epi (g j.as))
  have hexact : (piDiscrete f g hz).Exact := by
    rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    refine NatTrans.ext (funext fun j ↦ ?_)
    have hj : ((piDiscrete f g hz).map ((evaluation (Discrete J) A).obj j)).Exact :=
      ShortComplex.exact_of_iso (piDiscreteMapEvaluationIso f g hz j).symm (h j.as).exact
    rw [ShortComplex.exact_iff_isZero_homology] at hj
    exact (IsZero.of_iso hj
      ((piDiscrete f g hz).mapHomologyIso ((evaluation (Discrete J) A).obj j)).symm).eq_of_src _ _
  exact { exact := hexact, mono_f := hmono, epi_g := hepi }

variable [AB4StarOfSize.{w} A]

/-- A product of short exact sequences is short exact, when `w`-indexed products in `A` are exact
(Grothendieck's axiom AB4*). -/
theorem shortExact_pi_map (h : ∀ j, (ShortComplex.mk (f j) (g j) (hz j)).ShortExact)
    (zero : Limits.Pi.map f ≫ Limits.Pi.map g = 0) :
    (ShortComplex.mk (Limits.Pi.map f) (Limits.Pi.map g) zero).ShortExact :=
  (shortExact_piDiscrete f g hz h).map_of_exact (lim (J := Discrete J) (C := A))

end Products

/-! ### Short exactness of the Čech complexes -/

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]
  {ι : Type w} (U : ι → C)

/-- The Čech complex functor is additive. -/
instance cechComplexFunctor_additive : (cechComplexFunctor U (A := A)).Additive where
  map_add {_ _} φ ψ := HomologicalComplex.hom_ext _ _ fun n ↦ pi_map_add
    (fun x : Fin (n + 1) → ι ↦ φ.app (op (inter U x)))
    (fun x : Fin (n + 1) → ι ↦ ψ.app (op (inter U x)))

variable (S : ShortComplex (Cᵒᵖ ⥤ A)) [AB4StarOfSize.{w} A]

/-- **The Čech half of [Stacks, Tag 01EJ].** If the sections of a short complex of presheaves are
short exact over every object `inter U x` appearing in the Čech complex of the family `U`, then the
Čech complexes form a short exact sequence of cochain complexes. Short exactness in the presheaf
category, the hypothesis of [Stacks, Tag 01EJ], is the case in which this holds over every object.
-/
@[stacks 01EJ "exactness of the Čech complex functor into complexes, for Mathlib's \
  cechComplexFunctor, and assuming short exactness of sections only over the intersections \
  that occur in the Čech complex", ega "III 1.2.5" "partial"]
theorem shortExact_map_cechComplexFunctor
    (hS : ∀ (n : ℕ) (x : Fin (n + 1) → ι),
      (S.map ((evaluation Cᵒᵖ A).obj (op (inter U x)))).ShortExact) :
    (S.map (cechComplexFunctor U)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    shortExact_pi_map (fun x : Fin (n + 1) → ι ↦ S.f.app (op (inter U x)))
      (fun x : Fin (n + 1) → ι ↦ S.g.app (op (inter U x)))
      (fun x ↦ (NatTrans.comp_app S.f S.g (op (inter U x))).symm.trans
        (congrArg (fun α : S.X₁ ⟶ S.X₃ ↦ α.app (op (inter U x))) S.zero))
      (fun x ↦ hS n x)
      (((S.map (cechComplexFunctor U)).map
        (HomologicalComplex.eval A (ComplexShape.up ℕ) n)).zero)

/-! ### The long exact sequence

The Čech cohomology objects `Ȟ^n(𝒰, P)` are the homology objects of the Čech complex. The
connecting maps and exactness statements below form the long exact sequence
`⋯ ⟶ Ȟ^n(𝒰, P₁) ⟶ Ȟ^n(𝒰, P₂) ⟶ Ȟ^n(𝒰, P₃) ⟶ Ȟ^(n+1)(𝒰, P₁) ⟶ ⋯` of
[Stacks, Tag 01EK]. -/

variable (hS : ∀ (n : ℕ) (x : Fin (n + 1) → ι),
  (S.map ((evaluation Cᵒᵖ A).obj (op (inter U x)))).ShortExact)

/-- **The connecting map of Čech cohomology.** For a short complex of presheaves whose sections are
short exact over the objects of the Čech complex of `U`, this is the map
`Ȟ^n(𝒰, P₃) ⟶ Ȟ^(n+1)(𝒰, P₁)`. -/
@[stacks 01EK "the connecting maps and the long exact sequence of Čech cohomology"]
def cechδ (n : ℕ) :
    ((cechComplexFunctor U).obj S.X₃).homology n ⟶
      ((cechComplexFunctor U).obj S.X₁).homology (n + 1) :=
  (shortExact_map_cechComplexFunctor U S hS).δ n (n + 1) rfl

/-- The composite `Ȟ^n(𝒰, P₂) ⟶ Ȟ^n(𝒰, P₃) ⟶ Ȟ^(n+1)(𝒰, P₁)` vanishes. -/
@[reassoc (attr := simp)]
theorem cech_comp_δ (n : ℕ) :
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map S.g) n ≫ cechδ U S hS n = 0 :=
  (shortExact_map_cechComplexFunctor U S hS).comp_δ n (n + 1) rfl

/-- The composite `Ȟ^n(𝒰, P₃) ⟶ Ȟ^(n+1)(𝒰, P₁) ⟶ Ȟ^(n+1)(𝒰, P₂)` vanishes. -/
@[reassoc (attr := simp)]
theorem cech_δ_comp (n : ℕ) :
    cechδ U S hS n ≫
        HomologicalComplex.homologyMap ((cechComplexFunctor U).map S.f) (n + 1) = 0 :=
  (shortExact_map_cechComplexFunctor U S hS).δ_comp n (n + 1) rfl

/-- **Exactness of `Ȟ^n(𝒰, P₃) ⟶ Ȟ^(n+1)(𝒰, P₁) ⟶ Ȟ^(n+1)(𝒰, P₂)`**, one of the three exactness
statements making up the long exact sequence of [Stacks, Tag 01EK]. -/
@[stacks 01EK "the connecting maps and the long exact sequence of Čech cohomology"]
theorem cech_exact₁ (n : ℕ) :
    (ShortComplex.mk _ _ (cech_δ_comp U S hS n)).Exact :=
  (shortExact_map_cechComplexFunctor U S hS).homology_exact₁ n (n + 1) rfl

include hS in
/-- **Exactness of `Ȟ^n(𝒰, P₁) ⟶ Ȟ^n(𝒰, P₂) ⟶ Ȟ^n(𝒰, P₃)`**, one of the three exactness statements
making up the long exact sequence of [Stacks, Tag 01EK]. -/
@[stacks 01EK "the connecting maps and the long exact sequence of Čech cohomology"]
theorem cech_exact₂ (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap ((cechComplexFunctor U).map S.f) n)
      (HomologicalComplex.homologyMap ((cechComplexFunctor U).map S.g) n)
      (by rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp, S.zero,
        Functor.map_zero, HomologicalComplex.homologyMap_zero])).Exact :=
  (shortExact_map_cechComplexFunctor U S hS).homology_exact₂ n

/-- **Exactness of `Ȟ^n(𝒰, P₂) ⟶ Ȟ^n(𝒰, P₃) ⟶ Ȟ^(n+1)(𝒰, P₁)`**, one of the three exactness
statements making up the long exact sequence of [Stacks, Tag 01EK]. -/
@[stacks 01EK "the connecting maps and the long exact sequence of Čech cohomology"]
theorem cech_exact₃ (n : ℕ) :
    (ShortComplex.mk _ _ (cech_comp_δ U S hS n)).Exact :=
  (shortExact_map_cechComplexFunctor U S hS).homology_exact₃ n (n + 1) rfl

include hS in
/-- **Vanishing of higher Čech cohomology passes to a quotient.** If the Čech cohomology of `P₁`
and of `P₂` vanishes in every positive degree, then so does that of `P₃`; this is a step of
[Stacks, Tag 01EW]. -/
theorem isZero_cechHomology_X₃
    (h₁ : ∀ n : ℕ, 0 < n → IsZero (((cechComplexFunctor U).obj S.X₁).homology n))
    (h₂ : ∀ n : ℕ, 0 < n → IsZero (((cechComplexFunctor U).obj S.X₂).homology n))
    (n : ℕ) (hn : 0 < n) :
    IsZero (((cechComplexFunctor U).obj S.X₃).homology n) :=
  (cech_exact₃ U S hS n).isZero_of_both_isZero (h₂ n hn) (h₁ (n + 1) n.succ_pos)

end

end Stacks.CategoryTheory.CechComplex

end
