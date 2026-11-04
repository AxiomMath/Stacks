module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.RestrictFiberComparison

/-!
# The image of a descent datum under the inclusion of a full subcategory

A descent datum for the restriction of `p` to the full subcategory cut out by `P` is carried to one
for `p`: its objects are transported by `CategoryTheory.Functor.fiberιFunctor` and its gluing
isomorphisms are conjugated by `CategoryTheory.Functor.pullbackFiberιFiberIso`.

## Main definitions

* `CategoryTheory.Functor.SieveDescentDatum.mapι`, the image of the datum.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- The image under `P.ι` of a descent datum for the restriction of `p` to a full subcategory: its
objects are transported by `CategoryTheory.Functor.fiberιFunctor`, and its gluing isomorphisms are
conjugated by `CategoryTheory.Functor.pullbackFiberιFiberIso`. -/
noncomputable def SieveDescentDatum.mapι (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) [p.IsFibered]
    (h1 : ClosedUnderStronglyCartesian p P) {U : 𝒮} {R : Sieve U}
    (D : haveI := isFibered_restrict_of_closed p P h1; SieveDescentDatum (restrict p P) R) :
    SieveDescentDatum p R :=
  haveI := isFibered_restrict_of_closed p P h1
  { obj := fun {V} f hf => fiberι p P (D.obj f hf)
    iso := fun {V W Z} {f} hf {g} hg ε ε' heq =>
      (pullbackFiberιFiberIso h1 (D.obj f hf) ε).symm ≪≫
        (fiberιFunctor p P Z).mapIso (D.iso hf hg ε ε' heq) ≪≫
        pullbackFiberιFiberIso h1 (D.obj g hg) ε'
    cocycle := fun {V W X Z} {f} hf {g} hg {h} hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃ => by
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
        Iso.hom_inv_id_assoc]
      rw [← Functor.map_comp_assoc, D.cocycle hf hg hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃]
    iso_pullback := fun {V W Z Z'} {f} hf {g} hg ε ε' heq γ => by
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
        pullbackFiberIso_hom, pullbackFiberHom_comp]
      rw [← D.iso_pullback hf hg ε ε' heq γ]
      simp only [pullbackFiberIso_hom, Functor.map_comp, Category.assoc,
        ← pullbackFiberιFiberIso_comp_inv_assoc h1 (D.obj f hf) ε γ]
      rw [← pullbackFiberιFiberIso_naturality_assoc h1 (D.iso hf hg ε ε' heq).hom γ,
        ← pullbackFiberιFiberIso_comp h1 (D.obj g hg) ε' γ] }

/-- The objects of a transported descent datum are the images under `P.ι` of the original ones. -/
@[simp]
lemma SieveDescentDatum.mapι_obj (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) [p.IsFibered]
    (h1 : ClosedUnderStronglyCartesian p P) {U : 𝒮} {R : Sieve U}
    (D : haveI := isFibered_restrict_of_closed p P h1; SieveDescentDatum (restrict p P) R)
    ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R f) :
    haveI := isFibered_restrict_of_closed p P h1
    (SieveDescentDatum.mapι p P h1 D).obj f hf = fiberι p P (D.obj f hf) := rfl

/-- The gluing isomorphisms of a transported descent datum are the original ones conjugated by
`pullbackFiberιFiberIso`. -/
@[simp]
lemma SieveDescentDatum.mapι_iso (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) [p.IsFibered]
    (h1 : ClosedUnderStronglyCartesian p P) {U : 𝒮} {R : Sieve U}
    (D : haveI := isFibered_restrict_of_closed p P h1; SieveDescentDatum (restrict p P) R)
    ⦃V W Z : 𝒮⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    haveI := isFibered_restrict_of_closed p P h1
    (SieveDescentDatum.mapι p P h1 D).iso hf hg ε ε' heq =
      (pullbackFiberιFiberIso h1 (D.obj f hf) ε).symm ≪≫
        (fiberιFunctor p P Z).mapIso (D.iso hf hg ε ε' heq) ≪≫
        pullbackFiberιFiberIso h1 (D.obj g hg) ε' := rfl

end Functor

end CategoryTheory
