module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The structure sheaf of a ringed site is quasi-coherent and of finite type

On any site and over any sheaf of rings, the free module of rank one — the structure sheaf
itself — has a global presentation, is therefore quasi-coherent in the sense of Stacks 03DL(6),
and is of finite type in the sense of Stacks 03DL(5).  Both statements are formal: the
presentation is the identity of the structure sheaf viewed as a one-element coproduct and a
cokernel of the zero map, and the single section `1` generates on every object.  Neither needs
a sheafification instance, a covering argument, or any cohomological input.

Specialized to the small étale ringed site of an algebraic space, the two results are the
quasi-coherence clause and the finite-type clause of coherence of the structure sheaf, which is
the structure-sheaf assertion of Stacks 07UB.

## Main results

* `SheafOfModules.hasGlobalPresentation_unit`: the structure sheaf of a ringed site has a global
  presentation.
* `SheafOfModules.isQuasicoherentOnSite_unit`: the structure sheaf of a ringed site is
  quasi-coherent, as an instance.
* `PresheafOfModules.isFiniteType_unit`: the structure sheaf of a ringed site is of finite type.
* `AlgebraicGeometry.Space.isCoherent_structureSheaf_of_relations`: the structure sheaf of an
  algebraic space is coherent as soon as the relations among every finite family of its sections
  are of finite type.

## Implementation notes

`SheafOfModules.HasGlobalPresentation` asks for a cokernel of a map between coproducts of copies
of the structure sheaf, with the coproducts and the cokernel given by their universal
properties.  For the structure sheaf itself both coproducts are taken over a one-element index
type with the identity as the single inclusion, which is a colimit because a cofan with a single
identity leg is, and the presenting map is the zero map, whose cokernel is the identity.  The
universe bookkeeping is the one point that is not free: the module universe of
`SheafOfModules.unit R` is the coefficient universe `r`, and at `m = r` the two universe-lifted
copies of the structure sheaf appearing in `HasGlobalPresentation` — the one indexing the
coproducts and the one receiving the cokernel — become the same object, so the presenting
cokernel map may be the identity.

Finite type is `PresheafOfModules.IsFiniteType`, the sectionwise form of Stacks 03DL(5) used by
`SheafOfModules.IsCoherentOnSite`, rather than `SheafOfModules.IsFiniteTypeOnSite`.  The
covering family of objects witnessing it is all of the site, which covers the final object by
`CategoryTheory.GrothendieckTopology.coversTop_self`, and the generating family over an object
is the single section `1`; no shrinking is needed, so the covering sieve produced for each
section is the maximal one.

The structure-sheaf assertion of Stacks 07UB is *not* discharged here and no tag is carried.
`AlgebraicGeometry.Space.IsCoherent` is quasi-coherence together with
`SheafOfModules.IsCoherentOnSite`, and the latter is finite type together with finite type of the
sheaf of relations of every finite family of sections on every slice site.  The two clauses
proved here are the first and the second; the third is the one carrying the locally Noetherian
hypothesis, and `AlgebraicGeometry.Space.isCoherent_structureSheaf_of_relations` carries it as an
explicit hypothesis.  Discharging it means covering a slice of the small étale site by affine
schemes with Noetherian coordinate rings, where the relations among `n` sections of the structure
sheaf form the kernel of a map `A ^ n ⟶ A` and are finitely generated, and propagating that
along the étale — hence flat — morphisms of the slice, where the kernel commutes with the base
change.  That argument needs no comparison with the Zariski site and so does not pass through
Stacks 03DX, unlike the corresponding clause for a general quasi-coherent module.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **The structure sheaf of a ringed site has a global presentation.**  Both coproducts are
indexed by a one-element type with the identity as their single inclusion, and the presenting
map is zero, whose cokernel is the identity. -/
theorem hasGlobalPresentation_unit (R : Sheaf J RingCat.{r}) :
    (unit R).HasGlobalPresentation.{u, v, r, r} := by
  refine ⟨PUnit.{max u v r + 1}, PUnit.{max u v r + 1},
    uliftForPresentation.{u, v, r, r, max u v r} (unit R),
    uliftForPresentation.{u, v, r, r, max u v r} (unit R),
    fun _ => 𝟙 _, fun _ => 𝟙 _, ⟨?_⟩, ⟨?_⟩, 0, 𝟙 _, by rw [zero_comp], ⟨?_⟩⟩
  iterate 2
    exact Cofan.IsColimit.mk _ (fun s => s.inj PUnit.unit)
      (fun _ j => by cases j; exact Category.id_comp _)
      (fun _ _ hk => by simpa using hk PUnit.unit)
  · exact Cofork.IsColimit.mk _ (fun s => s.π) (fun _ => Category.id_comp _)
      (fun _ _ hk => by simpa using hk)

/-- **Stacks Project, Tag 03DL(6) for the structure sheaf.**  The structure sheaf of a ringed
site is quasi-coherent: it already has a global presentation, so the covering witnessing
quasi-coherence may be taken to be the identity, and the restriction of the structure sheaf to a
slice site is the structure sheaf of that slice. -/
@[ega "0 5.1.3" "more general"]
instance isQuasicoherentOnSite_unit (R : Sheaf J RingCat.{r}) :
    (unit R).IsQuasicoherentOnSite.{u, v, r, r} where
  locally_hasGlobalPresentation U := by
    refine ⟨ULift.{max u v} PUnit, fun _ => U, fun _ => 𝟙 U, ?_,
      fun _ => hasGlobalPresentation_unit (R.over U)⟩
    have htop : Sieve.ofArrows (fun _ : ULift.{max u v} PUnit => U) (fun _ => 𝟙 U) = ⊤ := by
      refine le_antisymm le_top fun Z g _ => ?_
      rw [Sieve.mem_ofArrows_iff]
      exact ⟨ULift.up PUnit.unit, g, by simp⟩
    rw [htop]
    exact J.top_mem U

end SheafOfModules

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Acting by a section of the structure sheaf on the section `1` gives that section back: the
module structure of the structure sheaf on itself is its ring multiplication. -/
private theorem unit_smul_one (R : Sheaf J RingCat.{r}) (X : Cᵒᵖ) (a : R.obj.obj X) :
    a • ((1 : R.obj.obj X) : (SheafOfModules.unit R).val.obj X)
      = (a : (SheafOfModules.unit R).val.obj X) := mul_one a

/-- **Stacks Project, Tag 03DL(5) for the structure sheaf.**  The structure sheaf of a ringed
site is of finite type: every object of the site carries the single generating section `1`, and
the site covers its final object. -/
theorem isFiniteType_unit (R : Sheaf J RingCat.{r}) :
    IsFiniteType J (SheafOfModules.unit R).val := by
  refine ⟨C, id, J.coversTop_self, fun U => ⟨1, fun _ => (1 : R.obj.obj (op U)), ?_⟩⟩
  intro V f t
  refine ⟨⊤, J.top_mem V, fun W g _ => ⟨fun _ => R.obj.map g.op t, ?_⟩⟩
  rw [Fin.sum_univ_one,
    show ((SheafOfModules.unit R).val.restrictₛₗ (g ≫ f).op) (1 : R.obj.obj (op U))
      = ((1 : R.obj.obj (op W)) : (SheafOfModules.unit R).val.obj (op W)) from
      unit_map_one R.obj (g ≫ f).op]
  exact unit_smul_one R (op W) (R.obj.map g.op t)

end PresheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The structure-sheaf assertion of Stacks 07UB, reduced to its relations clause.**  The
structure sheaf of an algebraic space is coherent as soon as the relations among every finite
family of its sections over every object of the small étale site are of finite type on the slice
site over that object.

Quasi-coherence and finite type, the other two clauses of
`AlgebraicGeometry.Space.IsCoherent` for the structure sheaf, are
`SheafOfModules.isQuasicoherentOnSite_unit` and `PresheafOfModules.isFiniteType_unit` and are not
hypotheses.  The hypothesis carried here is the one that needs the locally Noetherian assumption
on the space, and so this statement is weaker than Stacks 07UB and does not carry its tag. -/
theorem isCoherent_structureSheaf_of_relations
    (h : ∀ (U : (smallEtaleRingedSite B S hS F hF).C) (n : ℕ)
      (s : Fin n → (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O))).val.obj (op U)),
      PresheafOfModules.IsFiniteType ((smallEtaleRingedSite B S hS F hF).J.over U)
        (PresheafOfModules.relations (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).val s)) :
    IsCoherent B S hS F hF
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))) :=
  { __ := SheafOfModules.isQuasicoherentOnSite_unit _
    __ := ({ isFiniteType := PresheafOfModules.isFiniteType_unit _
             kernel_isFiniteType := h } :
      SheafOfModules.IsCoherentOnSite
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)))) }

end AlgebraicGeometry.Space

end
