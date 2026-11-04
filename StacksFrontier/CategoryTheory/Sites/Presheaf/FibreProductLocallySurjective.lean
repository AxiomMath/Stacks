module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.CategoryTheory.Sites.Presheaf.FibreProduct

/-!
# The fibre product of locally surjective maps of presheaves

For maps `mF : F ⟶ H` and `mG : G ⟶ H` of presheaves of sets and a Grothendieck topology on the
site, the map `F ×_H G ⟶ H` out of the explicit fibre product
`CategoryTheory.Presheaf.fibreProduct` is locally surjective as soon as both `mF` and `mG` are.

## Main results

* `CategoryTheory.Presheaf.isLocallySurjective_fibreProductFst_comp`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Presheaf

universe v u a

variable {C : Type u} [Category.{v} C] {F G H : Cᵒᵖ ⥤ Type a} (mF : F ⟶ H) (mG : G ⟶ H)

/-- **The fibre product of two locally surjective maps maps locally surjectively onto the
base.** A section `s` of `H` over `U` is locally `mF a` and locally `mG b`; on the intersection
of the two covering sieves the pair `(a, b)` is a section of `F ×_H G` lying over `s`. -/
instance isLocallySurjective_fibreProductFst_comp (J : GrothendieckTopology C)
    [Presheaf.IsLocallySurjective J mF] [Presheaf.IsLocallySurjective J mG] :
    Presheaf.IsLocallySurjective J (fibreProductFst mF mG ≫ mF) where
  imageSieve_mem {U} s := by
    refine J.superset_covering
      (S := Presheaf.imageSieve mF s ⊓ Presheaf.imageSieve mG s) ?_
      (J.intersection_covering (Presheaf.imageSieve_mem J mF s)
        (Presheaf.imageSieve_mem J mG s))
    rintro V k ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨(a, b), ha.trans hb.symm⟩, ha⟩

end CategoryTheory.Presheaf

end
