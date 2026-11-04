module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheafify
public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.Anticommutation
public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.FreeBasis

/-!
# Contraction by a coordinate functional of a finite free sheaf of modules

Let `O♯` be a sheaf of commutative rings on a site and let `(O♯)^ι` be the free sheaf of
`O♯`-modules on a finite index type `ι`. Each index `j : ι` gives a coordinate functional on
`(O♯)^ι`, the `j`-th projection, and contraction by it is a degree `-1` endomorphism

`δⱼ : ⋀^{n+1}((O♯)^ι) ⟶ ⋀ⁿ((O♯)^ι)`

of the exterior algebra. This file constructs the `δⱼ` and records the two identities they
satisfy: they anticommute with one another, and they anticommute with the Koszul differential of
any functional whatsoever.

Nothing new is needed for either. The coordinate functional is an instance of
`PresheafOfModules.ExteriorFunctional`, whose `dual` is the coordinate form of the natural basis
`Stacks.SheafOfModules.freeCoordBasis` of the sections of a finite free sheaf and whose
naturality is that basis being carried to itself by restriction
(`Stacks.SheafOfModules.freeCoordBasis_map`); so `δⱼ` is `SheafOfModules.koszulD` of Stacks tag
062K at that functional, and both identities are
`SheafOfModules.koszulD_comp_koszulD_comm`. In particular `δⱼ` *is* a Koszul differential — the
one of the sequence `(0, …, 0, 1, 0, …, 0)` — which is why it inherits the whole API of
`StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.SheafifiedDifferential`, including the graded Leibniz
rule.

## Main definitions

* `Stacks.SheafOfModules.coordExteriorFunctional`: **the `j`-th coordinate functional of the free
  sheaf of modules on a finite index type.**
* `Stacks.SheafOfModules.coordKoszulD`: **the contraction `δⱼ` by the `j`-th coordinate
  functional**, on the exterior algebra of the free sheaf.

## Main results

* `Stacks.SheafOfModules.coordExteriorFunctional_dual_apply`: the functional reads off the `j`-th
  coordinate of a local section.
* `Stacks.SheafOfModules.coordKoszulD_comp_coordKoszulD_comm`: **the contractions by two
  coordinate functionals anticommute**, `δⱼ δₖ = - δₖ δⱼ`.
* `Stacks.SheafOfModules.coordKoszulD_comp_koszulD_comm` and
  `Stacks.SheafOfModules.koszulD_comp_coordKoszulD_comm`: **`δⱼ` anticommutes with the Koszul
  differential of an arbitrary functional**, in either order; taking that functional to be the one
  whose Koszul complex is under study, this is the identity `δⱼ d + d δⱼ = 0`.
* `Stacks.SheafOfModules.coordKoszulD_comp_coordKoszulD_self`: the square of a single `δⱼ` is
  zero, which does not follow from the anticommutation identity.

## Implementation notes

**Why the coordinate functional is built from a basis rather than from the projection morphism.**
The `j`-th coordinate of a local section of the free sheaf is `Stacks.SheafOfModules.freeCoord`,
which is the projection morphism `Stacks.SheafOfModules.freeProj j` evaluated on sections; it
would therefore seem to give the functional directly. It does not, because its target is the
sections of `SheafOfModules.unit`, which are the ring of sections only after unfolding `unit`, and
instance search does not unfold it — the obstruction recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.Differential`, which is also why
`PresheafOfModules.ExteriorFunctional` bundles a `Module.Dual` rather than a morphism into the
unit. The coordinate form of `Stacks.SheafOfModules.freeCoordBasis` is a `Module.Dual` on the
nose, and `Stacks.SheafOfModules.freeCoord_freeCoordBasis` identifies it with the projection, so
nothing is lost.

**The base ring sheaf.** `Stacks.SheafOfModules.freeCoordBasis` is stated over
`SheafOfModules.GradedAlgebra.ringSheafOfIsSheaf`, which keeps the ring presheaf in the
syntactic form `O ⋙ forget₂ CommRingCat RingCat` that the sectionwise exterior powers need, while
`SheafOfModules.koszulD` is stated over `CategoryTheory.Sheaf.toRingCat`. The two agree, and the
sheaf property of the latter is what is fed to the former, exactly as in
`Stacks.SheafOfModules.freeSheafBasis`.

**Naturality of the functional is coordinate naturality of a semilinear map.** The restriction map
of the free sheaf is semilinear over the restriction map of the structure sheaf and carries the
`j`-th basis vector to the `j`-th basis vector, so it carries the `j`-th coordinate to the image
of the `j`-th coordinate. That is `Module.Basis.repr_map_of_map_basis`, and the
`ExteriorFunctional` naturality field is its symmetric form.

## References

* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 062L](https://stacks.math.columbia.edu/tag/062L)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf Opposite PresheafOfModules

universe v u w

namespace Stacks.SheafOfModules

open SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {ι : Type w} [DecidableEq ι] [Finite ι]

/-- **The `j`-th coordinate functional of the free sheaf of modules on a finite index type.**
Over each object it is the `j`-th coordinate form of the natural basis
`Stacks.SheafOfModules.freeCoordBasis` of the sections, and it is compatible with restriction
because that basis is. -/
def coordExteriorFunctional (j : ι) :
    ExteriorFunctional.{v, u, w, w}
      (_root_.SheafOfModules.free (R := toRingCat J Osharp) ι).val where
  dual V := (freeCoordBasis (toRingCat J Osharp).property V).coord j
  naturality {V W} f m :=
    (Module.Basis.repr_map_of_map_basis
      (freeCoordBasis (toRingCat J Osharp).property V)
      (freeCoordBasis (toRingCat J Osharp).property W)
      ((_root_.SheafOfModules.free (R := toRingCat J Osharp) ι).val.restrictₛₗ f)
      (fun i => freeCoordBasis_map (toRingCat J Osharp).property f i) m j).symm

/-- **The `j`-th coordinate functional reads off the `j`-th coordinate of a local section**, the
coordinates being those of `Stacks.SheafOfModules.freeCoordBasis`. -/
theorem coordExteriorFunctional_dual_apply (j : ι) (V : Cᵒᵖ)
    (m : ((_root_.SheafOfModules.free (R := toRingCat J Osharp) ι).val.obj V : Type w)) :
    (coordExteriorFunctional (Osharp := Osharp) j).dual V m =
      (freeCoordBasis (toRingCat J Osharp).property V).repr m j :=
  rfl

section Contraction

/-- **Contraction `δⱼ` by the `j`-th coordinate functional of the free sheaf of modules on a
finite index type**, from the homogeneous piece of degree `p` of the exterior algebra to the one
of degree `q`, for degrees with `q + 1 = p`. It is the Koszul differential of Stacks tag 062K at
the `j`-th coordinate functional, so it satisfies every law proved there, in particular the graded
Leibniz rule `SheafOfModules.koszulD_mul`. -/
def coordKoszulD (j : ι) {p q : ℤ} (h : q + 1 = p) :
    (_root_.SheafOfModules.sheafifiedExteriorAlgebra J
        (_root_.SheafOfModules.free (R := toRingCat J Osharp) ι)).piece p ⟶
      (_root_.SheafOfModules.sheafifiedExteriorAlgebra J
        (_root_.SheafOfModules.free (R := toRingCat J Osharp) ι)).piece q :=
  _root_.SheafOfModules.koszulD J _ (coordExteriorFunctional j) h

/-- **Contraction by two coordinate functionals anticommutes:** `δⱼ δₖ = - δₖ δⱼ`. For `k = j`
the two sides are equal to each other and the identity is vacuous; the vanishing of `δⱼ δⱼ` is
`Stacks.SheafOfModules.coordKoszulD_comp_coordKoszulD_self`. -/
theorem coordKoszulD_comp_coordKoszulD_comm (j k : ι) {p q r : ℤ} (h : q + 1 = p)
    (h' : r + 1 = q) :
    coordKoszulD (Osharp := Osharp) k h ≫ coordKoszulD j h' =
      -(coordKoszulD (Osharp := Osharp) j h ≫ coordKoszulD k h') :=
  _root_.SheafOfModules.koszulD_comp_koszulD_comm J _ (coordExteriorFunctional j)
    (coordExteriorFunctional k) h h'

/-- **The square of a single coordinate contraction is zero.** This is
`SheafOfModules.koszulD_comp_koszulD`, not a consequence of the anticommutation identity. -/
theorem coordKoszulD_comp_coordKoszulD_self (j : ι) {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) :
    coordKoszulD (Osharp := Osharp) j h ≫ coordKoszulD j h' = 0 :=
  _root_.SheafOfModules.koszulD_comp_koszulD J _ (coordExteriorFunctional j) h h'

/-- **The coordinate contraction `δⱼ` anticommutes with the Koszul differential of an arbitrary
functional `φ`**, applied first. Taking `φ` to be the functional whose Koszul complex is the
resolution under study, this is one half of the identity `δⱼ d + d δⱼ = 0`. -/
theorem coordKoszulD_comp_koszulD_comm (j : ι)
    (φ : ExteriorFunctional.{v, u, w, w}
      (_root_.SheafOfModules.free (R := toRingCat J Osharp) ι).val)
    {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) :
    _root_.SheafOfModules.koszulD J _ φ h ≫ coordKoszulD j h' =
      -(coordKoszulD (Osharp := Osharp) j h ≫ _root_.SheafOfModules.koszulD J _ φ h') :=
  _root_.SheafOfModules.koszulD_comp_koszulD_comm J _ (coordExteriorFunctional j) φ h h'

/-- **The coordinate contraction `δⱼ` anticommutes with the Koszul differential of an arbitrary
functional `φ`**, applied second. This is the other half of `δⱼ d + d δⱼ = 0`. -/
theorem koszulD_comp_coordKoszulD_comm (j : ι)
    (φ : ExteriorFunctional.{v, u, w, w}
      (_root_.SheafOfModules.free (R := toRingCat J Osharp) ι).val)
    {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) :
    coordKoszulD (Osharp := Osharp) j h ≫ _root_.SheafOfModules.koszulD J _ φ h' =
      -(_root_.SheafOfModules.koszulD J _ φ h ≫ coordKoszulD j h') :=
  _root_.SheafOfModules.koszulD_comp_koszulD_comm J _ φ (coordExteriorFunctional j) h h'

end Contraction

end Stacks.SheafOfModules

end
