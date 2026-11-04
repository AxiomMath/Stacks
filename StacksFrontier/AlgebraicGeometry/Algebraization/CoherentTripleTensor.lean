module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleHilbertPolynomial
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic

/-!
# Twisting a coherent triple by an invertible coherent triple

Let `A` be a local ring and `f ∈ A`, and let `(F, F₀, α)` and `(L, L₀, λ)` be coherent triples
for `(A, f)` with `(L, L₀, λ)` invertible. Tensoring the two members of the first triple with the
corresponding members of the second produces again a coherent triple

`(F ⊗ L, F₀ ⊗ L₀, α ⊗ λ)`,

the identification over the punctured closed fibre being `α ⊗ λ` read through the comparison of
the inverse image of a tensor product with the tensor product of the inverse images. Iterating
the construction twists `(F, F₀, α)` by the nonnegative tensor powers of `(L, L₀, λ)`; that
family of triples is the one whose Euler characteristics [Stacks, Tag 0F27] asserts to be given
by a polynomial.

## Main definitions

* `Stacks.Algebraization.CoherentTriple.tensorInvertible`: the tensor product of a coherent
  triple with an invertible coherent triple.
* `Stacks.Algebraization.CoherentTriple.twistPow`: the twists of a coherent triple by the
  nonnegative tensor powers of an invertible coherent triple.

## Main results

* `Stacks.Algebraization.isSMulRegular_sections_tensorModules`: a global function acting
  injectively on all sections of a module on a scheme acts injectively on all sections of its
  tensor product with an invertible module.
* `Stacks.Algebraization.isFTorsionFree_tensorModules`: the same statement for the
  `f`-torsion-freeness condition of a coherent triple.
* `Stacks.Algebraization.isInvertibleTriple_tensorInvertible` and
  `Stacks.Algebraization.isInvertibleTriple_twistPow`: the tensor product of two invertible
  coherent triples is invertible, and so is every twist of an invertible triple.

## Implementation notes

The three conditions a coherent triple imposes on its punctured-spectrum member are coherence,
`f`-torsion-freeness and nothing else, and the first is [Stacks, Tag 01CE] in the form
`AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible`. The second has to be
proved here, and is the only part of the construction that is not a composition of existing
comparisons.

`Stacks.Algebraization.IsFTorsionFree` asks that the image of `f` act injectively on the sections
over *every* open, which is not a condition instance search or a tensor-functor argument can see.
It is proved locally instead: an invertible module is trivial near every point
(`Stacks.InvertibleRankOneScheme.exists_mem_isoUnit_over`), and over an open on which the second
factor is the structure sheaf the tensor product is the first factor
(`Stacks.SheafOfModules.TensorOver.tensorOverIsoOfTrivial`). An isomorphism of sheaves of modules
on the slice site at that open is in particular a bijection on the sections over each smaller
open, linear over the functions there, so injectivity of multiplication transfers to those opens;
and a section of a sheaf is determined by its restrictions to a covering. The restriction of the
image of `f` to a smaller open is again the image of `f` there, which is
`Stacks.Algebraization.restrict_restrict_global`.

The tensor product is written `Stacks.RelativeVeryAmple.tensorModules`, an abbreviation for
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` on a scheme, which is the spelling the
functoriality `Stacks.RelativeVeryAmple.tensorModulesMapIso` and the inverse-image comparison
`Stacks.RelativeVeryAmple.pullbackTensorModulesIso` of [Stacks, Tag 01CD] are stated in. No
monoidal instance is used, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/TensorPower.lean`: the monoidal structure on
sheaves of modules is not visible to instance search at the presentation
`AlgebraicGeometry.Scheme.Modules`.

Invertibility of the second triple is the hypothesis `Stacks.Algebraization.IsInvertibleTriple`,
which asks for invertibility of its two members and nothing about its identification; the
identification enters only as the middle factor of the composite defining the new one.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RelativeVeryAmple

universe u

namespace Stacks.Algebraization

/-! ### Restricting a global function -/

/-- Restricting a global function of a scheme to an open and then to a smaller one restricts it
to the smaller one. -/
public theorem restrict_restrict_global {X : Scheme.{u}} {V W : X.Opens} (h : W ≤ V)
    (r : Γ(X, ⊤)) :
    X.presheaf.map (homOfLE h).op (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r)
      = X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op r := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting the product of a global function with a section of a module is multiplying the
restricted section by the restriction of that function. -/
public theorem map_smul_restrict_global {X : Scheme.{u}} (M : X.Modules) (r : Γ(X, ⊤))
    {V W : X.Opens} (h : W ≤ V) (a : Γ(M, V)) :
    M.presheaf.map (homOfLE h).op (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r • a) =
      X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op r • M.presheaf.map (homOfLE h).op a := by
  have h1 : M.presheaf.map (homOfLE h).op
        (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r • a)
      = X.presheaf.map (homOfLE h).op (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r) •
        M.presheaf.map (homOfLE h).op a :=
    PresheafOfModules.map_smul M.val (homOfLE h).op _ a
  rw [h1, restrict_restrict_global h r]

/-! ### A regular global function on a tensor product with an invertible module -/

/-- **A global function acting injectively on all sections of a module on a scheme acts
injectively on all sections of its tensor product with an invertible module.**

An invertible module is the structure sheaf near every point, and over an open on which the
second factor is the structure sheaf the tensor product is the first factor; an isomorphism of
sheaves of modules on the slice site at that open is a bijection on the sections over every
smaller open which is linear over the functions there, so it carries the injectivity hypothesis
to the tensor product over those opens. A section of a sheaf is determined by its restrictions to
a covering. -/
public theorem isSMulRegular_sections_tensorModules {X : Scheme.{u}} (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (r : Γ(X, ⊤))
    (hF : ∀ V : X.Opens, IsSMulRegular Γ(F, V)
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r))
    (V : X.Opens) :
    IsSMulRegular Γ(tensorModules X F L, V)
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r) := by
  set M := tensorModules X F L
  intro x y hxy
  have key : ∀ z ∈ V, ∃ (W : X.Opens) (hW : W ≤ V), z ∈ W ∧
      M.presheaf.map (homOfLE hW).op x = M.presheaf.map (homOfLE hW).op y := by
    intro z hz
    obtain ⟨U, hzU, ⟨θ⟩⟩ := Stacks.InvertibleRankOneScheme.exists_mem_isoUnit_over X L z
    refine ⟨V ⊓ U, inf_le_left, ⟨hz, hzU⟩, ?_⟩
    have ε : M.over U ≅ F.over U :=
      Stacks.SheafOfModules.TensorOver.tensorOverIsoOfTrivial (X := X.toRingedSpace) U F L θ
    let j : Over U := Over.mk (Y := V ⊓ U) (homOfLE inf_le_right)
    let φ : Γ(M, V ⊓ U) → Γ(F, V ⊓ U) := ε.hom.val.app (op j)
    have hinv : ∀ a : Γ(M, V ⊓ U), ε.inv.val.app (op j) (φ a) = a := fun a =>
      (ConcreteCategory.congr_hom
        (congrArg (fun t : M.over U ⟶ M.over U => t.val.app (op j)) ε.hom_inv_id) a).trans
        (CategoryTheory.id_apply a)
    have hlin : ∀ (c : Γ(X, V ⊓ U)) (a : Γ(M, V ⊓ U)), φ (c • a) = c • φ a := fun c a =>
      (ε.hom.val.app (op j)).hom.map_smul c a
    have h : M.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op
          (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r • x) =
        M.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op
          (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r • y) :=
      congrArg _ hxy
    rw [map_smul_restrict_global M r inf_le_left x,
      map_smul_restrict_global M r inf_le_left y] at h
    exact Function.LeftInverse.injective hinv
      (hF (V ⊓ U) ((hlin _ _).symm.trans ((congrArg φ h).trans (hlin _ _))))
  exact TopCat.Sheaf.eq_of_locally_eq'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X.carrier)
    (fun z : {z : X.carrier // z ∈ V} => (key z.1 z.2).choose) V
    (fun z => homOfLE (key z.1 z.2).choose_spec.choose)
    (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, (key z hz).choose_spec.choose_spec.1⟩) x y
    (fun z => (key z.1 z.2).choose_spec.choose_spec.2)

/-- **`f`-torsion-freeness passes to a tensor product with an invertible module.** The image of
`f` in the functions on an open of the punctured spectrum is the restriction of its image in the
global functions, so this is
`Stacks.Algebraization.isSMulRegular_sections_tensorModules` at that global function. -/
public theorem isFTorsionFree_tensorModules (A : Type u) [CommRing A] [IsLocalRing A] (f : A)
    (F L : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    [Stacks.Ample.IsInvertibleModule (Stacks.Divisors.puncturedSpectrum A).toScheme L]
    (hF : IsFTorsionFree A f F) :
    IsFTorsionFree A f (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme F L) :=
  isSMulRegular_sections_tensorModules F L
    ((Stacks.Divisors.puncturedSpectrum A).ι.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)) hF

/-! ### Tensoring two invertible modules -/

/-- **Stacks Project, Tag 01CT (1).** The tensor product of two invertible modules on a scheme is
invertible. -/
public theorem isInvertibleModule_tensorModules (X : Scheme.{u}) (M N : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] [Stacks.Ample.IsInvertibleModule X N] :
    Stacks.Ample.IsInvertibleModule X (tensorModules X M N) := by
  have inv (P : X.Modules) [Stacks.Ample.IsInvertibleModule X P] :
      Stacks.SheafOfModules.IsInvertible X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) P :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ P).2 ‹_›
  exact (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
    (Stacks.SheafOfModules.isInvertible_tensorSheaf X.presheaf _ M N)

/-! ### The tensor product of a coherent triple with an invertible coherent triple -/

/-- **The tensor product of a coherent triple with an invertible coherent triple.** Its members
are the tensor products of the corresponding members, and its identification over the punctured
closed fibre is the tensor product of the two identifications, read through the comparison of the
inverse image of a tensor product with the tensor product of the inverse images. -/
public noncomputable def CoherentTriple.tensorInvertible {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} (T L : CoherentTriple A f) (hL : IsInvertibleTriple L) : CoherentTriple A f where
  F := tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme T.F L.F
  F₀ := tensorModules (closedFibre A f) T.F₀ L.F₀
  coherent_F :=
    have : _root_.SheafOfModules.IsCoherent T.F := T.coherent_F
    have : Stacks.Ample.IsInvertibleModule
      (Stacks.Divisors.puncturedSpectrum A).toScheme L.F := hL.invertible_F
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible _ T.F L.F
  coherent_F₀ :=
    have : _root_.SheafOfModules.IsCoherent T.F₀ := T.coherent_F₀
    have : Stacks.Ample.IsInvertibleModule (closedFibre A f) L.F₀ := hL.invertible_F₀
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible _ T.F₀ L.F₀
  torsionFree :=
    have : Stacks.Ample.IsInvertibleModule
      (Stacks.Divisors.puncturedSpectrum A).toScheme L.F := hL.invertible_F
    isFTorsionFree_tensorModules A f T.F L.F T.torsionFree
  alpha :=
    pullbackTensorModulesIso
        (morphismRestrict (closedImmersion A f) (Stacks.Divisors.puncturedSpectrum A)) T.F L.F ≪≫
      tensorModulesMapIso (puncturedClosedFibre A f).toScheme T.alpha L.alpha ≪≫
      (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀ L.F₀).symm

/-- **The tensor product of two invertible coherent triples is invertible.** -/
public theorem isInvertibleTriple_tensorInvertible {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {T L : CoherentTriple A f} (hT : IsInvertibleTriple T) (hL : IsInvertibleTriple L) :
    IsInvertibleTriple (T.tensorInvertible L hL) where
  invertible_F :=
    have := hT.invertible_F
    have := hL.invertible_F
    isInvertibleModule_tensorModules _ T.F L.F
  invertible_F₀ :=
    have := hT.invertible_F₀
    have := hL.invertible_F₀
    isInvertibleModule_tensorModules _ T.F₀ L.F₀

/-! ### Twisting by the nonnegative powers -/

/-- **The twists of a coherent triple by the nonnegative tensor powers of an invertible coherent
triple.** The zeroth twist is the triple itself and each further one is the tensor product of the
previous one with the invertible triple, so the `n`-th is `(F ⊗ L^{⊗ n}, F₀ ⊗ L₀^{⊗ n}, α ⊗ λ^{⊗
n})` up to the associativity of the tensor product. This is the family whose Euler
characteristics [Stacks, Tag 0F27] asserts to be given by a polynomial. -/
@[stacks 0F27 "the twist of a coherent triple by the nonnegative powers of an invertible triple"]
public noncomputable def CoherentTriple.twistPow {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} (T L : CoherentTriple A f) (hL : IsInvertibleTriple L) : ℕ → CoherentTriple A f
  | 0 => T
  | n + 1 => (T.twistPow L hL n).tensorInvertible L hL

/-- The zeroth twist is the triple itself. -/
public theorem CoherentTriple.twistPow_zero {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    (T L : CoherentTriple A f) (hL : IsInvertibleTriple L) : T.twistPow L hL 0 = T :=
  rfl

/-- Each twist is the tensor product of the previous one with the invertible triple. -/
public theorem CoherentTriple.twistPow_succ {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    (T L : CoherentTriple A f) (hL : IsInvertibleTriple L) (n : ℕ) :
    T.twistPow L hL (n + 1) = (T.twistPow L hL n).tensorInvertible L hL :=
  rfl

/-- **Every twist of an invertible coherent triple by an invertible coherent triple is
invertible.** -/
public theorem isInvertibleTriple_twistPow {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    {T L : CoherentTriple A f} (hT : IsInvertibleTriple T) (hL : IsInvertibleTriple L) :
    ∀ n : ℕ, IsInvertibleTriple (T.twistPow L hL n)
  | 0 => hT
  | n + 1 => isInvertibleTriple_tensorInvertible (isInvertibleTriple_twistPow hT hL n) hL

end Stacks.Algebraization

end
