module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective

/-!
# Finitely many jointly surjective maps assemble into an epimorphism out of their biproduct

Let `R` be a sheaf of rings on a site `C` and let `φ i : E i ⟶ G` be finitely many morphisms of
sheaves of `R`-modules.  If every object of `C` has a covering family on whose members every
section of `G` is a sum of sections coming from the `E i`, then the single morphism
`⨁ E i ⟶ G` assembled out of the `φ i` is an epimorphism.

This is the site analogue of `AlgebraicGeometry.epi_of_forall_open_generators`, which on a
scheme reduces being an epimorphism to generation near each point; on a site there are no
stalks, and what replaces them is local surjectivity.

## Main results

* `Stacks.SheafOfModules.EpiMono.biproductDesc_app_sum`: the assembled morphism sends the sum of
  the images of finitely many sections under the biproduct inclusions to the sum of their images
  under the `φ i`.
* `Stacks.SheafOfModules.EpiMono.epi_biproductDesc_of_jointlySurjective`: **finitely many
  jointly locally surjective morphisms assemble into an epimorphism out of their biproduct.**
* `Stacks.SheafOfModules.EpiMono.epi_biproductDesc_of_surjective_on_presieve`: the same with the
  joint surjectivity tested on the members of a generating presieve of each object, which is the
  form a covering family is given in.

## Implementation notes

Only the easy direction of `Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective` is used,
so no sheafification hypothesis is needed: `epi_of_isLocallySurjective` is stated with the
sheafification instances of its file omitted.

The sections of the biproduct are never computed.  A joint lift of a section of `G` is assembled
as the sum of the images of its components under the biproduct inclusions `biproduct.ι E i`, and
`CategoryTheory.Limits.biproduct.ι_desc` identifies the image of that sum under the assembled
morphism with the sum of the images under the `φ i`; additivity of the component maps is all
that is used of the biproduct.

The presieve form asks for a *presieve*, not a sieve, whose generated sieve covers.  That is what
makes it applicable to a covering family: a family of arrows `V i ⟶ U` is a presieve, and
`CategoryTheory.Sieve.ofArrows` is the sieve it generates.  Joint surjectivity is required only
over the members of the family and not over the arrows factoring through them, because the sieve of
arrows along which a section lifts is already a sieve: `CategoryTheory.Sieve.generate_le_iff` turns
containment of the generated sieve into containment of the presieve, so no section has to be
restricted along the factoring arrow.

Nothing here is a Stacks tag: the criterion is a mechanism, and the source uses the
corresponding statement about schemes without delimiting it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v t

namespace Stacks.SheafOfModules.EpiMono

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- The morphism assembled out of finitely many `φ i : E i ⟶ G` sends the sum of the images of
sections `x i` under the biproduct inclusions to the sum of the images of the `x i` under the
`φ i`. -/
theorem biproductDesc_app_sum {ι : Type*} [Fintype ι] {E : ι → _root_.SheafOfModules.{t} R}
    {G : _root_.SheafOfModules.{t} R} [HasBiproduct E] (φ : ∀ i, E i ⟶ G) (W : C)
    (x : ∀ i, (E i).val.obj (op W)) :
    (biproduct.desc φ).val.app (op W) (∑ i, (biproduct.ι E i).val.app (op W) (x i)) =
      ∑ i, (φ i).val.app (op W) (x i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => congr_arg (·.val.app (op W) (x i)) (biproduct.ι_desc φ i)

/-- A section that is a sum of images under the `φ i` is an image under the assembled morphism. -/
private theorem exists_preimage_biproductDesc {ι : Type*} [Fintype ι]
    {E : ι → _root_.SheafOfModules.{t} R} {G : _root_.SheafOfModules.{t} R} [HasBiproduct E]
    (φ : ∀ i, E i ⟶ G) {W : C} {y}
    (h : ∃ x : ∀ i, (E i).val.obj (op W), ∑ i, (φ i).val.app (op W) (x i) = y) :
    ∃ z, (biproduct.desc φ).val.app (op W) z = y :=
  let ⟨x, hx⟩ := h
  ⟨_, (biproductDesc_app_sum φ W x).trans hx⟩

/-- **Finitely many jointly locally surjective morphisms of sheaves of modules assemble into an
epimorphism out of their biproduct.**  The hypothesis is that every section of `G` over an object
`V` has a covering sieve of `V` along each arrow of which it restricts to a sum of sections
coming from the `E i`. -/
theorem epi_biproductDesc_of_jointlySurjective {ι : Type*} [Fintype ι]
    {E : ι → _root_.SheafOfModules.{t} R} {G : _root_.SheafOfModules.{t} R} [HasBiproduct E]
    (φ : ∀ i, E i ⟶ G)
    (h : ∀ (V : C) (y : G.val.obj (op V)), ∃ S : Sieve V, S ∈ J V ∧
      ∀ ⦃W : C⦄ (g : W ⟶ V), S g → ∃ x : ∀ i, (E i).val.obj (op W),
        ∑ i, (φ i).val.app (op W) (x i) = G.val.map g.op y) :
    Epi (biproduct.desc φ) := by
  refine epi_of_isLocallySurjective _ ⟨fun {V} y => ?_⟩
  obtain ⟨S, hS, hlift⟩ := h V y
  refine J.superset_covering (fun W g hg => ?_) hS
  exact exists_preimage_biproductDesc φ (hlift g hg)

/-- **Finitely many morphisms of sheaves of modules which are jointly surjective on the sections
over the members of a generating presieve assemble into an epimorphism out of their
biproduct.**  The presieve need not be a sieve, which is what makes this applicable to a covering
family of each object. -/
theorem epi_biproductDesc_of_surjective_on_presieve {ι : Type*} [Fintype ι]
    {E : ι → _root_.SheafOfModules.{t} R} {G : _root_.SheafOfModules.{t} R} [HasBiproduct E]
    (φ : ∀ i, E i ⟶ G) (P : ∀ V : C, Presieve V) (hP : ∀ V : C, Sieve.generate (P V) ∈ J V)
    (hsurj : ∀ (V : C) ⦃W : C⦄ (g : W ⟶ V), P V g → ∀ y : G.val.obj (op W),
      ∃ x : ∀ i, (E i).val.obj (op W), ∑ i, (φ i).val.app (op W) (x i) = y) :
    Epi (biproduct.desc φ) := by
  refine epi_of_isLocallySurjective _ ⟨fun {V} y => ?_⟩
  refine J.superset_covering ((Sieve.generate_le_iff _ _).2 fun W b hb => ?_) (hP V)
  exact exists_preimage_biproductDesc φ (hsurj V b hb (G.val.map b.op y))

end Stacks.SheafOfModules.EpiMono

end
