module

public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Replacing the summands of a cofan by isomorphic objects

A cofan is colimiting as soon as the cofan obtained by precomposing each of its injections
with an isomorphism of the corresponding summand is, and conversely. The apex is untouched:
only the family of summands is replaced, summand by summand.

Mathlib has the two neighbouring statements, but not this one. `CategoryTheory.Limits.Cofan.ext`
replaces the apex and keeps the summands; `CategoryTheory.Limits.Sigma.whiskerEquiv` does
replace the summands up to isomorphism, but it produces an isomorphism of the coproducts `∐ f`
and `∐ g` and so presupposes that both coproducts exist, whereas the statement here is about an
arbitrary cofan with no `HasCoproduct` hypothesis.

## Main definitions

* `CategoryTheory.Limits.Cofan.isColimitCompIso`: the colimit property transported along a
  family of isomorphisms of the summands.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

/-- The summands of a colimiting cofan may be replaced by isomorphic objects: if the cofan with
injections `f i : F i ⟶ P` is colimiting and `e i : G i ≅ F i`, then the cofan with injections
`(e i).hom ≫ f i : G i ⟶ P` is colimiting too. -/
def Cofan.isColimitCompIso {D : Type*} [Category* D] {ι : Type*}
    {F G : ι → D} {P : D} (f : ∀ i, F i ⟶ P) (hf : IsColimit (Cofan.mk P f))
    (e : ∀ i, G i ≅ F i) : IsColimit (Cofan.mk P fun i => (e i).hom ≫ f i) := by
  refine Cofan.IsColimit.mk _ (fun s => Cofan.IsColimit.desc hf fun i => (e i).inv ≫ s.inj i)
    (fun s i => (Category.assoc _ _ _).trans
      (((e i).hom ≫= Cofan.IsColimit.fac hf _ i).trans ((e i).hom_inv_id_assoc _)))
    (fun s m hm => Cofan.IsColimit.hom_ext hf _ _ fun i => ?_)
  exact (show f i ≫ m = (e i).inv ≫ s.inj i by simpa using (e i).inv ≫= hm i).trans
    (Cofan.IsColimit.fac hf (fun i => (e i).inv ≫ s.inj i) i).symm

end CategoryTheory.Limits

end
