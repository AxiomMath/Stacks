module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf

/-!
# The structure sheaf of a big fppf site

The presheaf of rings `T ↦ Γ(T, 𝒪_T)` is a sheaf on a chosen big fppf site, and on its
localization at an object `S`.

## Main definitions

* `AlgebraicGeometry.BigFppfSite.lineObject`: the affine line as an object of the site.
* `AlgebraicGeometry.BigFppfSite.structureSheaf`: the structure sheaf of the site.
* `AlgebraicGeometry.BigFppfOver.structureSheaf`: the structure sheaf of the site over `S`.
  It is the structure sheaf `𝒪_S` of Stacks 04HS for the site `(Sch/S)_fppf`.

## Main results

* `AlgebraicGeometry.contains_affineLineOverInt`: the affine line is an object of every big
  fppf site.
* `AlgebraicGeometry.BigFppfSite.structure_isSheaf`: global functions are a sheaf of rings on
  the site.
* `AlgebraicGeometry.BigFppfOver.structure_isSheaf`: global functions are a sheaf of rings on the
  site over `S`.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 04HS](https://stacks.math.columbia.edu/tag/04HS)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

/-- The affine line is an object of every big fppf site. -/
theorem contains_affineLineOverInt (B : BigFppfSite.{u}) :
    B.Contains Stacks.Sites.affineLineOverInt.{u} := by
  have hZ : (Spec (CommRingCat.of (ULift.{u} ℤ))).size < B.cutoff := by
    rw [Scheme.size_Spec]
    simpa using B.aleph0_lt_cutoff
  exact Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (ULift.{u} ℤ) (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)) hZ

namespace BigFppfSite

/-- The affine line, as an object of a big fppf site. Its functor of points on the site is the
presheaf of global functions. -/
noncomputable def lineObject (B : BigFppfSite.{u}) : B.Schemes :=
  B.obj (contains_affineLineOverInt B)

/-- Full faithfulness of a site's inclusion, as an equivalence between the morphisms of the site
into the affine line and the morphisms of schemes into the affine line. -/
noncomputable def inclusionHomEquiv (B : BigFppfSite.{u}) (Z : B.Schemes) :
    (B.inclusion.obj Z ⟶ Stacks.Sites.affineLineOverInt.{u}) ≃ (Z ⟶ lineObject B) where
  toFun g := B.inclusion.preimage (Y := lineObject B) g
  invFun f := B.inclusion.map f
  left_inv _ := Functor.map_preimage _ _
  right_inv _ := Functor.preimage_map _

/-- The presheaf of global functions on a big fppf site is represented by the affine line. -/
@[ega "I 3.3.15" "special case", ega "II 1.7.13" "partial", sga "3 I 4.3.1" "special case"]
noncomputable def globalSectionsIsoYoneda (B : BigFppfSite.{u}) :
    B.inclusion.op ⋙ Scheme.Γ.{u} ⋙ forget CommRingCat ≅ yoneda.obj (lineObject B) :=
  Functor.isoWhiskerLeft B.inclusion.op Stacks.Sites.globalSectionsIsoYoneda.{u} ≪≫
    NatIso.ofComponents (fun Z => Equiv.toIso (inclusionHomEquiv B Z.unop))
      (by
        intro Z Z' h
        ext g
        apply B.inclusion.map_injective
        change B.inclusion.map (B.inclusion.preimage (Y := lineObject B)
            (B.inclusion.map h.unop ≫ g)) =
          B.inclusion.map (h.unop ≫ B.inclusion.preimage (Y := lineObject B) g)
        rw [Functor.map_preimage, Functor.map_comp]
        exact congrArg (fun k => B.inclusion.map h.unop ≫ k)
          (Functor.map_preimage B.inclusion (Y := lineObject B) g).symm)

/-- Global functions are a sheaf of types on a big fppf site. -/
theorem isSheaf_globalSections (B : BigFppfSite.{u}) :
    Presieve.IsSheaf B.topology (B.inclusion.op ⋙ Scheme.Γ.{u} ⋙ forget CommRingCat) := by
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  rw [← isSheaf_iff_isSheaf_of_type,
    Presheaf.isSheaf_of_iso_iff (globalSectionsIsoYoneda B), isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- Global functions are a sheaf of rings on a big fppf site. -/
theorem structure_isSheaf (B : BigFppfSite.{u}) :
    Presheaf.IsSheaf B.topology
      (B.inclusion.op ⋙ Scheme.Γ.{u} ⋙ forget₂ CommRingCat RingCat) :=
  Stacks.Sites.isSheaf_ringCat_of_isSheaf_forget _ _ (isSheaf_globalSections B)

/-- The structure sheaf of a big fppf site. -/
noncomputable def structureSheaf (B : BigFppfSite.{u}) : Sheaf B.topology RingCat.{u} :=
  ⟨B.inclusion.op ⋙ Scheme.Γ.{u} ⋙ forget₂ CommRingCat RingCat, structure_isSheaf B⟩

end BigFppfSite

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The presheaf of global functions is a sheaf of rings on the big fppf site over `S`. -/
@[stacks 03DU "big fppf structure sheaf"]
theorem structure_isSheaf :
    Presheaf.IsSheaf (topology B S hS)
      (Stacks.Sites.structurePresheaf S (Over.post B.inclusion)) :=
  ((B.structureSheaf).over (B.obj hS)).property

/-- The structure sheaf of the big fppf site over `S`. -/
@[stacks 03DU "big fppf structure sheaf construction"]
noncomputable def structureSheaf : Sheaf (topology B S hS) RingCat.{u} :=
  ⟨Stacks.Sites.structurePresheaf S (Over.post B.inclusion), structure_isSheaf B S hS⟩

/-- The structure sheaf of the big fppf site over `S` has the presheaf of global functions as its
underlying presheaf. -/
@[simp]
theorem structureSheaf_obj :
    (structureSheaf B S hS).obj = Stacks.Sites.structurePresheaf S (Over.post B.inclusion) :=
  rfl

end BigFppfOver

end AlgebraicGeometry

add_to_stacks 04HS "big fppf structure sheaf" AlgebraicGeometry.BigFppfOver.structureSheaf

end
