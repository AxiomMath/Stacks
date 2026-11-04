module

public import StacksFrontier.AlgebraicGeometry.Scheme.AffineOpenNeighborhood

/-!
# Sections of the structure sheaf are determined on affine opens

A section of `𝒪_X` over an arbitrary open is determined by its restrictions to the affine opens
inside it, those affine opens covering it (`AlgebraicGeometry.exists_affineOpen_mem_le`).

This is what carries an identity between sections which is available only on affine opens to an
arbitrary open.  The situation it is for: an ideal sheaf whose sections are *generated* by a
single function only affine-locally — the components of an
`AlgebraicGeometry.Scheme.IdealSheafData` are indexed by `X.affineOpens`, and generation does not
glue, the coefficient writing a section as a multiple of the generator being unique only modulo
the annihilator of the generator.  An *equation* between sections does glue, so a consequence of
generation which is an equation holds over every open although generation itself does not.

## Main results

* `AlgebraicGeometry.section_ext_of_affineOpens`: two sections of `𝒪_X` over an open whose
  restrictions to every affine open inside it agree are equal.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A section of `𝒪_X` over an open is determined by its restrictions to the affine opens
inside it.** The affine opens inside an open cover it, the affine opens being a basis of the
topology, and the structure sheaf is separated. -/
theorem section_ext_of_affineOpens {X : Scheme.{u}} {V : X.Opens} {s t : Γ(X, V)}
    (h : ∀ (W : X.affineOpens) (hW : W.1 ≤ V),
      (X.presheaf.map (homOfLE hW).op).hom s = (X.presheaf.map (homOfLE hW).op).hom t) :
    s = t :=
  X.sheaf.eq_of_locally_eq' (fun W : {W : X.affineOpens // W.1 ≤ V} => W.val.1) V
    (fun W => homOfLE W.property)
    (fun x hx =>
      have ⟨O, hxO, hOV⟩ := exists_affineOpen_mem_le x V hx
      Opens.mem_iSup.mpr ⟨⟨O, hOV⟩, hxO⟩)
    s t fun W => h W.1 W.2

end AlgebraicGeometry

end
