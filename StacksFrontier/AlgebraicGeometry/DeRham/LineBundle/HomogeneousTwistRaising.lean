module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwist

/-!
# Multiplication by a homogeneous function raises the degree of the pushed-forward forms

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module and `L^⋆ ⟶ X` the
complement of the zero section of the associated line bundle. Multiplication by the homogeneous
function of a local section of `L^{⊗ n}` carries the degree-`m` part `Ω^p_{L^⋆/S, m}` of the
pushed-forward relative forms into the degree-`(n + m)` part — for *every* section over *every*
open of `X`, not only for a homogeneous form over an affine one, which is
`Stacks.LineBundle.Situation.smul_mem_gradedLaurentForms`. This file proves that.

## Main results

* `Stacks.LineBundle.Situation.mem_gradedLaurentForms_of_locally`: **membership in a graded piece
  is local on the open.**
* `Stacks.LineBundle.Situation.mem_gradedLaurentForms_of_eq`: membership transported along an
  equation of sections.
* `Stacks.LineBundle.Situation.laurentSmul_zero`: multiplying the zero form by a function gives
  the zero form.
* `Stacks.LineBundle.Situation.laurentSmul_mem_gradedLaurentForms_affine` and
  `Situation.laurentSmul_map_mem_gradedLaurentForms`: the degree bookkeeping on a homogeneous
  generator, over its own affine open and over an arbitrary smaller open.
* `Stacks.LineBundle.Situation.laurentSmul_mem_gradedLaurentForms`: **multiplication by the
  homogeneous function of a section of `L^{⊗ n}` carries `Ω^p_{L^⋆/S, m}` into
  `Ω^p_{L^⋆/S, n + m}`**, over an arbitrary open and for an arbitrary section.

## Implementation notes

Locality of membership is the `isSheaf` field of Mathlib's `SheafOfModules.Submodule` — the field
that makes a submodule of a sheaf of modules a subsheaf rather than only a sub-presheaf — read
through the covering-sieve criterion `TopologicalSpace.Opens.mem_grothendieckTopology` for the
topology of a space, so that a consumer supplies one neighbourhood per point instead of a sieve.

The degree bookkeeping is the induction principle `Situation.gradedLaurentForms_le_iff` applied to
the sub-`𝒪_X`-module sheaf of sections whose products with the homogeneous functions land in the
degree-`(n + m)` part. The condition is stated over *all smaller opens*, as the annihilator
subsheaf of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EtaSheafCohomology.lean` is and for the
same reason: so stated it is stable under restriction and local, and its `isSheaf` field reduces
to the locality above with no sieve built by hand. Restriction along the identity is likewise not
among the conditions, and the two places where the condition has to be read on the open the
section itself lives over go through a neighbourhood from the basis of affine opens rather than
through the identification of a restriction along `𝟙` with the section.

Each of `0`, `+` and `•` in the three closure fields of that subsheaf has to be moved between the
pushforward's indexing of the forms and the one carrying the action of a function on `L^⋆`:
`smul_zero` and `smul_add` do not apply at the pushforward spelling, the `SMulZeroClass` and
`DistribSMul` instances living at the `D.laurentFormsAlgebra.piece p` indexing. The move is
`id (α := ·)`, as in `Situation.laurentSmul` itself, and it is made once per operation —
`Situation.laurentSmul_zero` here, `Situation.laurentSmul_add` and `Situation.laurentSmul_smul`
in `StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwist` — so that the fields
themselves rewrite with lemmas already stated at the pushforward spelling.

The goals of this file are memberships in `Situation.gradedLaurentForms`, whose statement mentions
`𝒪_X` at two indexings that are equal by `rfl` and not interchangeable at reducible transparency.
A rewrite in such a goal fails, its motive being elaborated at that transparency; a term
application crosses the seam, so the naturality chains are transported by
`Situation.mem_gradedLaurentForms_of_eq` rather than by `rw`.

## References

* [Stacks Project, Tag 0FUH](https://stacks.math.columbia.edu/tag/0FUH), clause (1)
* [Stacks Project, Tag 0FU9](https://stacks.math.columbia.edu/tag/0FU9), the graded pieces
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **Membership in a graded piece of the pushed-forward forms is local on the open**: a section
each of whose restrictions to a neighbourhood of every point lies in the degree-`k` part lies in
it. This is the sheaf condition carried by `SheafOfModules.Submodule`, read through the
covering-sieve criterion for the topology of a space. -/
theorem Situation.mem_gradedLaurentForms_of_locally (p : ℕ) (k : ℤ) {W : D.X.Opens}
    (ω : (D.laurentFormsPushforward (p : ℤ)).val.obj (op W))
    (h : ∀ z ∈ W, ∃ (W' : D.X.Opens) (hW' : W' ≤ W), z ∈ W' ∧
      (D.laurentFormsPushforward (p : ℤ)).val.map (homOfLE hW').op ω ∈
        (D.gradedLaurentForms p k).obj (op W')) :
    ω ∈ (D.gradedLaurentForms p k).obj (op W) := by
  refine (D.gradedLaurentForms p k).isSheaf ω ?_
  rw [Opens.mem_grothendieckTopology]
  intro z hz
  obtain ⟨W', hW', hzW', hmem⟩ := h z hz
  exact ⟨W', homOfLE hW', hmem, hzW'⟩

/-- Membership in a graded piece transported along an equation of sections. The equations below
are chains of naturality statements and `Situation.laurentSmul` moves a term between two
indexings of the forms, so the goals they act on are not rewritable: the motive of a rewrite is
elaborated at reducible transparency, at which the two indexings of `𝒪_X` are not interchangeable.
Transporting along an explicit `congrArg` is a term application and crosses that seam. -/
theorem Situation.mem_gradedLaurentForms_of_eq (p : ℕ) (k : ℤ) {V : (Opens D.X)ᵒᵖ}
    {ω η : (D.laurentFormsPushforward (p : ℤ)).val.obj V} (h : ω = η)
    (hη : η ∈ (D.gradedLaurentForms p k).obj V) :
    ω ∈ (D.gradedLaurentForms p k).obj V :=
  Eq.mpr (congrArg (· ∈ (D.gradedLaurentForms p k).obj V) h) hη

/-- **Multiplying the zero form by a function gives the zero form.** The `SMulZeroClass`
instance lives at the `D.laurentFormsAlgebra.piece p` indexing of the forms, so `smul_zero` does
not apply to the pushforward spelling and the zero is moved by `id (α := ·)`, as in
`Situation.laurentSmul` itself. -/
theorem Situation.laurentSmul_zero (p : ℤ) (U : D.X.Opens)
    (f : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) :
    D.laurentSmul p U f 0 = 0 :=
  smul_zero (A := (D.laurentFormsAlgebra.piece p).val.obj
    (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) f

/-- If a section restricts to `η` on a smaller open, the restriction of its product with a
homogeneous function is the product of `η` with the restricted function. -/
private theorem Situation.map_laurentSmul_mem_gradedLaurentForms (p : ℕ) (k n : ℤ)
    {V W : D.X.Opens} (hWV : W ≤ V) (x : (D.laurentAlgebra.piece n).val.obj (op V))
    (ω : (D.laurentFormsPushforward (p : ℤ)).val.obj (op V))
    {η : (D.laurentFormsPushforward (p : ℤ)).val.obj (op W)}
    (h : (D.laurentFormsPushforward (p : ℤ)).val.map (homOfLE hWV).op ω = η)
    (hη : D.laurentSmul (p : ℤ) W (D.laurentFunctionOfOpen n W
        ((D.laurentAlgebra.piece n).val.map (homOfLE hWV).op x)) η ∈
      (D.gradedLaurentForms p k).obj (op W)) :
    (D.laurentFormsPushforward (p : ℤ)).val.map (homOfLE hWV).op
        (D.laurentSmul (p : ℤ) V (D.laurentFunctionOfOpen n V x) ω) ∈
      (D.gradedLaurentForms p k).obj (op W) :=
  D.mem_gradedLaurentForms_of_eq p k
    ((D.laurentSmul_map (p : ℤ) hWV (D.laurentFunctionOfOpen n V x) ω).trans
      (congrArg₂ (fun f η => D.laurentSmul (p : ℤ) W f η)
        (D.laurentFunctionOfOpen_map n hWV x) h)) hη

/-- Membership of a product with a function, transported along equations of the form and of the
product. -/
private theorem Situation.laurentSmul_mem_gradedLaurentForms_of_eq (p : ℕ) (k : ℤ)
    {V : D.X.Opens} (f : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ V)))
    {ω η ζ : (D.laurentFormsPushforward (p : ℤ)).val.obj (op V)} (h : ω = η)
    (h' : D.laurentSmul (p : ℤ) V f η = ζ) (hζ : ζ ∈ (D.gradedLaurentForms p k).obj (op V)) :
    D.laurentSmul (p : ℤ) V f ω ∈ (D.gradedLaurentForms p k).obj (op V) :=
  D.mem_gradedLaurentForms_of_eq p k ((congrArg (D.laurentSmul (p : ℤ) V f) h).trans h') hζ

/-! ### The degree-raising inclusion -/

/-- **A homogeneous form of degree `m` over an affine open, multiplied by the homogeneous
function of a section of `L^{⊗ n}` over that same open, is a section of `Ω^p_{L^⋆/S, n + m}`.**
This is `Situation.smul_mem_gradedLaurentForms` with the multiplication written through
`Situation.laurentSmul` and the function through `Situation.laurentFunctionOfOpen`, the two
descriptions agreeing over an affine open. -/
theorem Situation.laurentSmul_mem_gradedLaurentForms_affine {p : ℕ} {m : ℤ} (n : ℤ)
    (U : D.X.affineOpens) (x : (D.laurentAlgebra.piece n).val.obj (op U.1))
    {ω : (D.laurentFormsAlgebra.piece (p : ℤ)).val.obj
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U.1))}
    (hω : D.IsHomogeneousLaurentForm U p m ω) :
    D.laurentSmul (p : ℤ) U.1 (D.laurentFunctionOfOpen n U.1 x) ω ∈
      (D.gradedLaurentForms p (n + m)).obj (op U.1) := by
  rw [D.laurentFunctionOfOpen_affine n U x]
  exact D.smul_mem_gradedLaurentForms U n x hω

/-- **The restriction of a homogeneous form of degree `m` to an arbitrary smaller open,
multiplied there by the homogeneous function of any section of `L^{⊗ n}`, is a section of
`Ω^p_{L^⋆/S, n + m}`.** The smaller open carries no affineness hypothesis: membership is local by
`Situation.mem_gradedLaurentForms_of_locally`, and on an affine neighbourhood inside it
`Situation.isHomogeneousLaurentForm_map` makes the restricted form a homogeneous generator
again. -/
theorem Situation.laurentSmul_map_mem_gradedLaurentForms {p : ℕ} {m : ℤ} (n : ℤ)
    (U : D.X.affineOpens) {V : D.X.Opens} (hV : V ≤ U.1)
    {ω : (D.laurentFormsAlgebra.piece (p : ℤ)).val.obj
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U.1))}
    (hω : D.IsHomogeneousLaurentForm U p m ω)
    (x : (D.laurentAlgebra.piece n).val.obj (op V)) :
    D.laurentSmul (p : ℤ) V (D.laurentFunctionOfOpen n V x)
        ((D.laurentFormsPushforward (p : ℤ)).val.map (homOfLE hV).op ω) ∈
      (D.gradedLaurentForms p (n + m)).obj (op V) := by
  refine D.mem_gradedLaurentForms_of_locally p (n + m) _ ?_
  intro z hz
  obtain ⟨W, hWaff, hzW, hWV⟩ := Opens.isBasis_iff_nbhd.mp D.X.isBasis_affineOpens hz
  refine ⟨W, hWV, hzW, ?_⟩
  have hmap : (D.laurentFormsPushforward (p : ℤ)).val.map (homOfLE hWV).op
        ((D.laurentFormsPushforward (p : ℤ)).val.map (homOfLE hV).op ω) =
      (D.laurentFormsPushforward (p : ℤ)).val.map (homOfLE (hWV.trans hV)).op ω :=
    ((D.laurentFormsPushforward (p : ℤ)).val.map_comp_apply
        (homOfLE hV).op (homOfLE hWV).op ω).symm.trans
      ((D.laurentFormsPushforward (p : ℤ)).val.congr_map_apply
        (show (homOfLE hV).op ≫ (homOfLE hWV).op = (homOfLE (hWV.trans hV)).op from
          Subsingleton.elim _ _) ω)
  refine D.map_laurentSmul_mem_gradedLaurentForms p (n + m) n hWV x _ hmap ?_
  exact D.laurentSmul_mem_gradedLaurentForms_affine n ⟨W, hWaff⟩ _
    (D.isHomogeneousLaurentForm_map (U' := ⟨W, hWaff⟩) (hWV.trans hV) p m ω hω)

/-- The condition cutting out the sections whose products with the homogeneous functions of the
local sections of `L^{⊗ n}` land in the degree-`(n + m)` part. The condition is imposed over
*every smaller open*, not only over the open the section lives on, which is what makes it local:
the restriction of a section satisfying it satisfies it, and a section satisfying it near every
point satisfies it. The annihilator subsheaf of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EtaSheafCohomology.lean` is stated the same way, for
the same reason, and restriction along the identity is likewise not among the conditions. -/
private def Situation.RaisesDegree (p : ℕ) (n m : ℤ) {U : (Opens D.X)ᵒᵖ}
    (ω : (D.laurentFormsPushforward (p : ℤ)).val.obj U) : Prop :=
  ∀ (V : (Opens D.X)ᵒᵖ) (g : U ⟶ V) (x : (D.laurentAlgebra.piece n).val.obj V),
    D.laurentSmul (p : ℤ) V.unop (D.laurentFunctionOfOpen n V.unop x)
        ((D.laurentFormsPushforward (p : ℤ)).val.map g ω) ∈
      (D.gradedLaurentForms p (n + m)).obj V

/-- The condition is stable under restriction, each of its instances for the restricted section
being one of its instances for the section. -/
private theorem Situation.raisesDegree_map (p : ℕ) (n m : ℤ) {U V : (Opens D.X)ᵒᵖ} (g : U ⟶ V)
    {ω : (D.laurentFormsPushforward (p : ℤ)).val.obj U} (hω : D.RaisesDegree p n m ω) :
    D.RaisesDegree p n m ((D.laurentFormsPushforward (p : ℤ)).val.map g ω) := fun V' g' x =>
  D.laurentSmul_mem_gradedLaurentForms_of_eq p (n + m)
    (D.laurentFunctionOfOpen n V'.unop x)
    ((D.laurentFormsPushforward (p : ℤ)).val.map_comp_apply g g' ω).symm rfl (hω V' (g ≫ g') x)

/-- **The condition is local on the open**: a section satisfying it on a neighbourhood of every
point satisfies it. Each of its instances is a membership in a graded piece, and those are local
by `Situation.mem_gradedLaurentForms_of_locally`; the neighbourhood is cut down by the open the
instance is asked over, so that the two restrictions of the section being compared agree. -/
private theorem Situation.raisesDegree_of_locally (p : ℕ) (n m : ℤ) {U : (Opens D.X)ᵒᵖ}
    (s : (D.laurentFormsPushforward (p : ℤ)).val.obj U)
    (hs : ∀ z ∈ U.unop, ∃ (W : D.X.Opens) (hW : W ≤ U.unop), z ∈ W ∧
      D.RaisesDegree p n m
        ((D.laurentFormsPushforward (p : ℤ)).val.map (homOfLE hW).op s)) :
    D.RaisesDegree p n m s := by
  intro V g x
  refine D.mem_gradedLaurentForms_of_locally p (n + m) _ ?_
  intro z hz
  obtain ⟨W, hWU, hzW, hW⟩ := hs z (leOfHom g.unop hz)
  refine ⟨W ⊓ V.unop, inf_le_right, ⟨hzW, hz⟩, ?_⟩
  have hboth : (D.laurentFormsPushforward (p : ℤ)).val.map
          (homOfLE (inf_le_right : W ⊓ V.unop ≤ V.unop)).op
        ((D.laurentFormsPushforward (p : ℤ)).val.map g s) =
      (D.laurentFormsPushforward (p : ℤ)).val.map
          (homOfLE (inf_le_left : W ⊓ V.unop ≤ W)).op
        ((D.laurentFormsPushforward (p : ℤ)).val.map (homOfLE hWU).op s) :=
    (((D.laurentFormsPushforward (p : ℤ)).val.map_comp_apply g
          (homOfLE (inf_le_right : W ⊓ V.unop ≤ V.unop)).op s).symm.trans
        ((D.laurentFormsPushforward (p : ℤ)).val.congr_map_apply
          (show g ≫ (homOfLE (inf_le_right : W ⊓ V.unop ≤ V.unop)).op =
              (homOfLE hWU).op ≫ (homOfLE (inf_le_left : W ⊓ V.unop ≤ W)).op from
            Subsingleton.elim _ _) s)).trans
      ((D.laurentFormsPushforward (p : ℤ)).val.map_comp_apply (homOfLE hWU).op
        (homOfLE (inf_le_left : W ⊓ V.unop ≤ W)).op s)
  refine D.map_laurentSmul_mem_gradedLaurentForms p (n + m) n inf_le_right x _ hboth ?_
  exact hW (op (W ⊓ V.unop)) (homOfLE (inf_le_left : W ⊓ V.unop ≤ W)).op _

/-- The sections satisfying the condition, as a sub-`𝒪_X`-module of the pushed-forward forms.
Each of `0`, `+` and `•` has to be moved between the pushforward's indexing of the forms and the
one carrying the action of a function on `L^⋆`; that is what
`Situation.laurentSmul_zero`, `Situation.laurentSmul_add` and `Situation.laurentSmul_smul` do,
so none of `smul_zero`, `smul_add` or `smul_comm` is reached for here. -/
private def Situation.raisesDegreeSubmodule (p : ℕ) (n m : ℤ) :
    (D.laurentFormsPushforward (p : ℤ)).val.Submodule where
  obj _V :=
    { carrier := {ω | D.RaisesDegree p n m ω}
      zero_mem' := fun V' g _ => D.laurentSmul_mem_gradedLaurentForms_of_eq p (n + m) _
        (map_zero ((D.laurentFormsPushforward (p : ℤ)).val.map g).hom)
        (D.laurentSmul_zero (p : ℤ) V'.unop _) (Submodule.zero_mem _)
      add_mem' := fun ha hb V' g x => D.laurentSmul_mem_gradedLaurentForms_of_eq p (n + m) _
        (map_add ((D.laurentFormsPushforward (p : ℤ)).val.map g).hom _ _)
        (D.laurentSmul_add (p : ℤ) V'.unop _ _ _)
        (Submodule.add_mem _ (ha V' g x) (hb V' g x))
      smul_mem' := fun r _ ha V' g x => D.laurentSmul_mem_gradedLaurentForms_of_eq p (n + m) _
        ((D.laurentFormsPushforward (p : ℤ)).val.map_smul g r _)
        (D.laurentSmul_smul (p : ℤ) V'.unop _ _ _) (Submodule.smul_mem _ _ (ha V' g x)) }
  map g _ hω := D.raisesDegree_map p n m g hω

/-- **The sections satisfying the condition form a sub-`𝒪_X`-module *sheaf***: the `isSheaf`
field is `Situation.raisesDegree_of_locally`, the covering sieve being read through
`TopologicalSpace.Opens.mem_grothendieckTopology`. -/
private def Situation.raisesDegreeSubsheaf (p : ℕ) (n m : ℤ) :
    (D.laurentFormsPushforward (p : ℤ)).Submodule where
  toSubmodule := D.raisesDegreeSubmodule p n m
  isSheaf {U} s hs := D.raisesDegree_of_locally p n m s fun z hz => by
    obtain ⟨W, f, hWmem, hzW⟩ := hs z hz
    exact ⟨W, leOfHom f, hzW, hWmem⟩

/-- **Every section of the degree-`m` part satisfies the condition**: by the induction principle
`Situation.gradedLaurentForms_le_iff` it is enough to check it on the homogeneous forms of degree
`m` over an affine open, which is `Situation.laurentSmul_map_mem_gradedLaurentForms`. -/
private theorem Situation.gradedLaurentForms_le_raisesDegreeSubsheaf (p : ℕ) (n m : ℤ) :
    D.gradedLaurentForms p m ≤ D.raisesDegreeSubsheaf p n m := by
  refine (D.gradedLaurentForms_le_iff _).mpr ?_
  intro U ω hω V g x
  exact D.laurentSmul_map_mem_gradedLaurentForms n U (leOfHom g.unop) hω x

/-- **Multiplying a section of `Ω^p_{L^⋆/S, m}` by the homogeneous function of a section of
`L^{⊗ n}` gives a section of `Ω^p_{L^⋆/S, n + m}`**, over an arbitrary open of `X` and for an
arbitrary section — not only for a homogeneous form over an affine open, which is
`Situation.smul_mem_gradedLaurentForms`. This is what corestricts the multiplication map
`Situation.twistHom` of clause (1) of Tag 0FUH to the two graded pieces, so it is needed before
the comparison of that clause can be written down. -/
theorem Situation.laurentSmul_mem_gradedLaurentForms {p : ℕ} {m : ℤ} (n : ℤ) {U : D.X.Opens}
    (x : (D.laurentAlgebra.piece n).val.obj (op U))
    {ω : (D.laurentFormsPushforward (p : ℤ)).val.obj (op U)}
    (hω : ω ∈ (D.gradedLaurentForms p m).obj (op U)) :
    D.laurentSmul (p : ℤ) U (D.laurentFunctionOfOpen n U x) ω ∈
      (D.gradedLaurentForms p (n + m)).obj (op U) := by
  have hraise : D.RaisesDegree p n m ω :=
    D.gradedLaurentForms_le_raisesDegreeSubsheaf p n m (op U) hω
  refine D.mem_gradedLaurentForms_of_locally p (n + m) _ ?_
  intro z hz
  obtain ⟨W, -, hzW, hWU⟩ := Opens.isBasis_iff_nbhd.mp D.X.isBasis_affineOpens hz
  refine ⟨W, hWU, hzW, ?_⟩
  refine D.map_laurentSmul_mem_gradedLaurentForms p (n + m) n hWU x ω rfl ?_
  exact hraise (op W) (homOfLE hWU).op _

end Stacks.LineBundle

end
