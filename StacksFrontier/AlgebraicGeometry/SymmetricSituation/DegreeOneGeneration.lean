module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.DegreeOneGeneration
public import StacksFrontier.AlgebraicGeometry.SymmetricFree.Presentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraGrading
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise

/-!
# The symmetric algebra of a quasi-coherent module is generated in degree one

The projective bundle of a quasi-coherent module `F` on a scheme `X` is the relative `Proj` of
`Sym(F)`, and the representability of its degree-one functor (Tag 01O4) has one hypothesis: that
on every affine open `U` of `X` the graded ring of sections

`⨁_{n ≥ 0} Symⁿ(F)(U)`

is generated in degree one over its degree-zero part. This file proves that hypothesis.

`Symⁿ(F)` is the *sheafification* of the sectionwise symmetric power `U ↦ Symⁿ_{𝒪(U)}(F(U))`
(Tag 01CG), so a section of it is the image of a sectionwise symmetric power only locally, on
the members of some cover of arbitrary opens. Three steps join up:

* **sectionwise** — `Symⁿ_{R}(M)` is spanned by the ordered products of `n` elements of `M`,
  which is Mathlib's `SymmetricAlgebra.symmetricPower_eq_span_prod_ι` transported to the
  subtype;
* **sheafification** — the unit of the sheafification is locally surjective, and it carries a
  sectionwise ordered product to the ordered product of the images, because the sheafified
  multiplication is pinned down on unit-images;
* **local-to-global** — `Stacks.RelativeProj.Situation.adjoin_sectionRingGrading_one_eq_top`,
  which takes exactly the local statement these two produce and needs the open to be affine.

## Main definitions

* `PresheafOfModules.symmetricAlgebraProd`: the ordered product of `n` local sections of `F`,
  as a local section of the sectionwise degree-`n` symmetric power.
* `Stacks.RelativeProj.symmetricSituationUnit`: the sheafification unit, from the sectionwise
  symmetric power to the homogeneous piece of the symmetric relative `Proj` situation.

## Main results

* `Submodule.mem_span_preimage_subtype`: membership in the span of a set transfers to the
  subtype of a submodule containing that set. Pure algebra, and the step that turns the
  symmetric-power span into a statement about sections of the sectionwise symmetric power.
* `PresheafOfModules.mem_span_range_symmetricAlgebraProd`: **the sectionwise span.**
* `Stacks.RelativeProj.symmetricSituationUnit_symmetricAlgebraProd`: **the unit carries a
  sectionwise ordered product to the ordered product of the images.**
* `Stacks.RelativeProj.isLocallyDegreeOneGenerated_symmetricSituation`: **the symmetric
  situation is locally generated in degree one over every open.**
* `Stacks.RelativeProj.adjoin_sectionRingGrading_one_eq_top_symmetricSituation` and
  `Stacks.RelativeProj.adjoin_sectionRingGrading_one_eq_top_symmetricSituationOfQuasicoherent`:
  **the graded ring of sections of `Sym(F)` over an affine open is generated in degree one over
  its degree-zero part**, for the situation with its quasi-coherence hypothesis open and for the
  projective-bundle situation of a quasi-coherent module.

## Implementation notes

**The local statement is proved over an arbitrary open and affineness is used only at the
end.** `isLocallyDegreeOneGenerated_symmetricSituation` has no affineness hypothesis at all: the
cover it produces comes from local surjectivity of the sheafification unit, which is
unconditional. Affineness enters only inside
`Stacks.RelativeProj.Situation.adjoin_sectionRingGrading_one_eq_top`, where it shrinks that
cover to basic opens and clears the denominators at the degree-one piece.

**The two sides of the sheafification are two scalar spellings of one ring, and only one of them
carries each instance.** A section of the sectionwise piece is a module over
`X.ringCatSheaf.obj.obj (op V)`; a section of the situation's piece is a module over
`Γ(X, V)`. The types are definitionally equal and the instances are not interchangeable:
`Module Γ(X, V) ((symPowInt n F.val).obj (op V))` is `synthInstanceFailed`.
So the sectionwise span is stated over the first ring and the span it is pushed into over the
second, and the induction that crosses the seam is
`symmetricSituationUnit_mem_span_homogeneousPow`.

**Every identity crossing the sheafification is proved as a term.** `rw` on
`PresheafOfModules.symmetricAlgebraProd` fails *"not type-correct under the `implicit`
transparency level"*, because the degree of the product appears in the type of the section and
`((n + 1 : ℕ) : ℤ)` and `(n : ℤ) + 1` are definitionally but not syntactically equal.

**The tag attribute is withheld.** Degree-one generation is the hypothesis `hgen` of Tag 01O4's
representability statement, not the content of a tag; Tag 01CG is the sheafification description
of `Symⁿ`, which holds here by construction rather than being proved.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open PresheafOfModules (symPowInt symPowIntGradedAlgebra symPowIntGen
  symPowIntOne sheafifyUnit sheafifyRestrict symPowIntVal
  symPowIntVal_injective)

universe v u w

/-- **Membership in the span of a set transfers to the subtype of a submodule containing it.**
If `S ⊆ p` and `p ⊆ span R S`, then every element of `p`, read in the subtype, lies in the span
of the preimage of `S`. -/
theorem Submodule.mem_span_preimage_subtype {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (p : Submodule R M) (S : Set M) (hS : S ⊆ (p : Set M))
    (hp : (p : Set M) ⊆ Submodule.span R S) (m : p) :
    m ∈ Submodule.span R (p.subtype ⁻¹' S) := by
  have himg : p.subtype '' (p.subtype ⁻¹' S) = S :=
    Set.image_preimage_eq_of_subset (by simpa using hS)
  have hmap : (Submodule.span R (p.subtype ⁻¹' S)).map p.subtype = Submodule.span R S := by
    rw [Submodule.map_span, himg]
  have hmem : (m : M) ∈ (Submodule.span R (p.subtype ⁻¹' S)).map p.subtype := by
    rw [hmap]; exact hp m.2
  obtain ⟨y, hy, hym⟩ := hmem
  exact (Subtype.ext hym : y = m) ▸ hy

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat))

/-- The ordered product of `n` local sections of `F`, as a local section of the sectionwise
degree-`n` symmetric power. -/
noncomputable def symmetricAlgebraProd (n : ℕ) (Y : Cᵒᵖ) (t : Fin n → F.obj Y) :
    (symPowInt (n : ℤ) F).obj Y :=
  ⟨∏ i : Fin n, SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y) (t i),
    SymmetricAlgebra.prod_ι_mem _ t⟩

/-- The underlying element of `symmetricAlgebraProd n Y t` in the symmetric algebra of
`F.obj Y` is the product of the generators `ι (t i)`. -/
theorem symPowIntVal_prod (n : ℕ) (Y : Cᵒᵖ) (t : Fin n → F.obj Y) :
    symPowIntVal (F.symmetricAlgebraProd n Y t) =
      ∏ i : Fin n, SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y) (t i) := rfl

/-- The empty ordered product is the unit of the sectionwise symmetric algebra. -/
theorem symmetricAlgebraProd_zero (Y : Cᵒᵖ) (t : Fin 0 → F.obj Y) :
    F.symmetricAlgebraProd 0 Y t = (symPowIntOne F).eval Y :=
  symPowIntVal_injective (0 : ℤ) F (by
    rw [symPowIntVal_prod, PresheafOfModules.symPowIntVal_one]
    exact Fin.prod_univ_zero _)

/-- The ordered product of `n + 1` sections is the product of the first `n` with the last. -/
theorem symmetricAlgebraProd_succ (n : ℕ) (Y : Cᵒᵖ) (t : Fin (n + 1) → F.obj Y) :
    F.symmetricAlgebraProd (n + 1) Y t =
      ((symPowIntGradedAlgebra F).mul (n : ℤ) 1).app Y
        (F.symmetricAlgebraProd n Y fun i => t i.castSucc)
        (PresheafOfModules.Hom.app (symPowIntGen F) Y (t (Fin.last n))) :=
  symPowIntVal_injective ((n + 1 : ℕ) : ℤ) F (by
    simp only [symmetricAlgebraProd]
    exact Fin.prod_univ_castSucc _)

/-- **The sectionwise degree-`n` symmetric power is spanned by the ordered products of `n`
degree-one sections.** This is `SymmetricAlgebra.symmetricPower_eq_span_prod_ι` read inside the
submodule it describes. -/
theorem mem_span_range_symmetricAlgebraProd (n : ℕ) (Y : Cᵒᵖ)
    (x : (symPowInt (n : ℤ) F).obj Y) :
    x ∈ Submodule.span ((O ⋙ forget₂ _ RingCat).obj Y)
      (Set.range fun t : Fin n → F.obj Y => F.symmetricAlgebraProd n Y t) := by
  have hpre : (SymPow.symmetricPowerInt (n : ℤ) ((O ⋙ forget₂ CommRingCat RingCat).obj Y)
          (F.obj Y)).subtype ⁻¹'
        (Set.range fun t : Fin n → F.obj Y =>
          ∏ i : Fin n,
            SymmetricAlgebra.ι ((O ⋙ forget₂ CommRingCat RingCat).obj Y) (F.obj Y) (t i)) =
      Set.range fun t : Fin n → F.obj Y => F.symmetricAlgebraProd n Y t := by
    ext y
    exact ⟨fun ⟨t, ht⟩ => ⟨t, Subtype.ext ht⟩, fun ⟨t, h⟩ => ⟨t, congrArg Subtype.val h⟩⟩
  refine hpre ▸ Submodule.mem_span_preimage_subtype _ _ ?_ ?_ x
  · rintro - ⟨t, rfl⟩
    exact SymmetricAlgebra.prod_ι_mem _ t
  · intro y hy
    have h2 : y ∈ SymPow.symmetricPower n ((O ⋙ forget₂ CommRingCat RingCat).obj Y)
        (F.obj Y) := hy
    rw [SymmetricAlgebra.symmetricPower_eq_span_prod_ι] at h2
    exact h2

end PresheafOfModules

namespace Stacks.RelativeProj

variable (X : Scheme.{u}) (F : X.Modules)
  (hqc : ∀ n : ℕ, ((SheafOfModules.sheafifiedSymmetricAlgebra
    (Opens.grothendieckTopology ↥X) F).piece (n : ℤ)).IsQuasicoherent)

/-- The sheafification unit, from a section of the sectionwise degree-`d` symmetric power to a
section of the degree-`d` homogeneous piece of the symmetric relative `Proj` situation. -/
noncomputable abbrev symmetricSituationUnit (d : ℤ) (V : X.Opens)
    (m : (symPowInt d F.val).obj (op V)) :
    Γ((symmetricSituation X F hqc).pieceModules d, V) :=
  PresheafOfModules.Hom.app
    (sheafifyUnit (𝟙 X.ringCatSheaf.obj) (symPowInt d F.val)) (op V) m

/-- **The unit carries a sectionwise ordered product to the ordered product of the images.**
The sheafified multiplication is pinned down on unit-images
(`Stacks.GradedAlgebra.sheafify_mul_unit`), so this is an induction on the length of the
product with the sectionwise recursion of `PresheafOfModules.symmetricAlgebraProd` at each
step. -/
theorem symmetricSituationUnit_symmetricAlgebraProd (V : X.Opens) :
    ∀ (n : ℕ) (t : Fin n → F.val.obj (op V)),
      symmetricSituationUnit X F hqc (n : ℤ) V (F.val.symmetricAlgebraProd n (op V) t) =
        (symmetricSituation X F hqc).homogeneousPow V n fun i =>
          symmetricSituationUnit X F hqc 1 V
            (PresheafOfModules.Hom.app (symPowIntGen F.val) (op V) (t i)) := by
  intro n
  induction n with
  | zero =>
      intro t
      exact (congrArg (symmetricSituationUnit X F hqc ((0 : ℕ) : ℤ) V)
          (F.val.symmetricAlgebraProd_zero (op V) t)).trans
        ((symPowIntGradedAlgebra F.val).sheafify_one_eval
          (𝟙 X.ringCatSheaf.obj) (op V)).symm
  | succ n ih =>
      intro t
      exact (congrArg (symmetricSituationUnit X F hqc ((n + 1 : ℕ) : ℤ) V)
          (F.val.symmetricAlgebraProd_succ n (op V) t)).trans
        (((symPowIntGradedAlgebra F.val).sheafify_mul_unit
            (𝟙 X.ringCatSheaf.obj) (n : ℤ) 1 (op V) _ _).symm.trans
          (congrArg
            (fun w => (symmetricSituation X F hqc).pieceMul (n : ℤ) 1 V w
              (symmetricSituationUnit X F hqc 1 V
                (PresheafOfModules.Hom.app (symPowIntGen F.val) (op V)
                  (t (Fin.last n)))))
            (ih fun i => t i.castSucc)))

end Stacks.RelativeProj

/-- **A span-valued membership criterion for a morphism of presheaves of modules.** If the
image of every element of a spanning set lies in a submodule of the sections of the target,
then so does the image of every element of the span.

It is stated at a variable sheaf of rings on purpose: there is exactly one spelling of the ring
of sections in sight, so no instance search has to cross the three spellings this file would
otherwise meet. -/
theorem PresheafOfModules.mem_of_mem_span_of_forall {C : Type u} [Category.{v} C]
    {R₀ : Cᵒᵖ ⥤ RingCat.{w}} {M N : PresheafOfModules.{w} R₀} (φ : M ⟶ N) (Y : Cᵒᵖ)
    (p : Submodule (R₀.obj Y) (N.obj Y)) (S : Set (M.obj Y))
    (hS : ∀ y ∈ S, PresheafOfModules.Hom.app φ Y y ∈ p) {m : M.obj Y}
    (hm : m ∈ Submodule.span (R₀.obj Y) S) : PresheafOfModules.Hom.app φ Y m ∈ p := by
  exact (Submodule.span_le (p := p.comap (PresheafOfModules.Hom.app φ Y).hom)).2
    (fun y hy => hS y hy) hm

namespace Stacks.RelativeProj

variable (X : Scheme.{u}) (F : X.Modules)
  (hqc : ∀ n : ℕ, ((SheafOfModules.sheafifiedSymmetricAlgebra
    (Opens.grothendieckTopology ↥X) F).piece (n : ℤ)).IsQuasicoherent)

/-- **Every section of a homogeneous piece in the image of the sheafification unit is a
combination of ordered products of degree-one sections.** The three ring spellings in play —
`Γ(X, V)`, `X.ringCatSheaf.obj.obj (op V)` and the one the sectionwise symmetric power is a
module over — are definitionally equal and pairwise invisible to instance search; they are
crossed here, once each, at an argument position of
`PresheafOfModules.mem_of_mem_span_of_forall`, where the check is definitional unfolding and
not a search. -/
theorem symmetricSituationUnit_mem_of_forall
    (V : (symmetricSituation X F hqc).base.Opens) (n : ℕ)
    (p : Submodule Γ((symmetricSituation X F hqc).base, V)
      Γ((symmetricSituation X F hqc).pieceModules (n : ℤ), V))
    (hp : ∀ t : Fin n → F.val.obj (op V),
      symmetricSituationUnit X F hqc (n : ℤ) V (F.val.symmetricAlgebraProd n (op V) t) ∈ p)
    (m : (symPowInt (n : ℤ) F.val).obj (op V)) :
    symmetricSituationUnit X F hqc (n : ℤ) V m ∈ p :=
  PresheafOfModules.mem_of_mem_span_of_forall
    (sheafifyUnit (𝟙 X.ringCatSheaf.obj) (symPowInt (n : ℤ) F.val)) (op V) p _
    (fun _ hy => by
      obtain ⟨t, rfl⟩ := hy
      exact hp t)
    (F.val.mem_span_range_symmetricAlgebraProd n (op V) m)

/-- **Every section of a homogeneous piece is a combination of ordered products of degree-one
sections**, locally, where it is in the image of the sheafification unit. -/
theorem symmetricSituationUnit_mem_span_homogeneousPow
    (V : (symmetricSituation X F hqc).base.Opens) (n : ℕ)
    (m : (symPowInt (n : ℤ) F.val).obj (op V)) :
    symmetricSituationUnit X F hqc (n : ℤ) V m ∈
      Submodule.span Γ((symmetricSituation X F hqc).base, V)
        (Set.range fun z : Fin n → Γ((symmetricSituation X F hqc).pieceModules (1 : ℤ), V) =>
          (symmetricSituation X F hqc).homogeneousPow V n z) :=
  symmetricSituationUnit_mem_of_forall X F hqc V n
    (Submodule.span Γ((symmetricSituation X F hqc).base, V)
      (Set.range fun z : Fin n → Γ((symmetricSituation X F hqc).pieceModules (1 : ℤ), V) =>
        (symmetricSituation X F hqc).homogeneousPow V n z))
    (fun t => Submodule.subset_span
      ⟨_, (symmetricSituationUnit_symmetricAlgebraProd X F hqc V n t).symm⟩) m

/-- **The symmetric algebra of a sheaf of modules is locally generated in degree one over every
open.** No affineness is involved: the cover comes from local surjectivity of the sheafification
unit, which is unconditional. -/
theorem isLocallyDegreeOneGenerated_symmetricSituation
    (U : (symmetricSituation X F hqc).base.Opens) :
    (symmetricSituation X F hqc).IsLocallyDegreeOneGenerated U := by
  intro n a x hx
  obtain ⟨V, f, hf, hxV⟩ := Stacks.liftSieve_mem (𝟙 X.ringCatSheaf.obj)
    (symPowInt (n : ℤ) F.val) (X := op U) a x hx
  obtain ⟨m, hm⟩ := Stacks.exists_lift_of_liftSieve (𝟙 X.ringCatSheaf.obj)
    (symPowInt (n : ℤ) F.val) a f hf
  refine ⟨V, f.le, hxV, ?_⟩
  have hm' : (symmetricSituation X F hqc).pieceRestrict (n : ℤ) f.le a =
      symmetricSituationUnit X F hqc (n : ℤ) V m := hm.symm
  exact hm' ▸ symmetricSituationUnit_mem_span_homogeneousPow X F hqc V n m

/-- **The graded ring of sections of `Sym(F)` over an affine open is generated in degree one
over its degree-zero part.** This is the hypothesis `hgen` of Tag 01O4's representability
statement for the projective bundle of `F`. -/
theorem adjoin_sectionRingGrading_one_eq_top_symmetricSituation
    (U : (symmetricSituation X F hqc).base.Opens) (hU : IsAffineOpen U) :
    Algebra.adjoin ↥((symmetricSituation X F hqc).sectionRingGrading U 0)
      ((symmetricSituation X F hqc).sectionRingGrading U 1 :
        Set ((symmetricSituation X F hqc).sectionRing U)) = ⊤ :=
  (symmetricSituation X F hqc).adjoin_sectionRingGrading_one_eq_top U hU
    (isLocallyDegreeOneGenerated_symmetricSituation X F hqc U)

/-- **The projective-bundle situation of a quasi-coherent module is generated in degree one.**
Tag 01OB's relative `Proj` situation, with the quasi-coherence of the symmetric powers
discharged by `Stacks.SliceAlgebra.isQuasicoherent_sheafifiedSymmetricPiece`. -/
theorem adjoin_sectionRingGrading_one_eq_top_symmetricSituationOfQuasicoherent
    (E : X.Modules) [E.IsQuasicoherent]
    (U : (symmetricSituationOfQuasicoherent X E).base.Opens) (hU : IsAffineOpen U) :
    Algebra.adjoin ↥((symmetricSituationOfQuasicoherent X E).sectionRingGrading U 0)
      ((symmetricSituationOfQuasicoherent X E).sectionRingGrading U 1 :
        Set ((symmetricSituationOfQuasicoherent X E).sectionRing U)) = ⊤ :=
  adjoin_sectionRingGrading_one_eq_top_symmetricSituation X E _ U hU

end Stacks.RelativeProj

end
