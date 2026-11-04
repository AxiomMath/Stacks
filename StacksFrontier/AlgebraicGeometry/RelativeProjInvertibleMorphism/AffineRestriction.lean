module

public import StacksFrontier.AlgebraicGeometry.Modules.QcqsLocalization
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.LocalOnBase
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.Locus

/-!
# `U(ψ) ∩ f^{-1}(V) = U(ψ_V)`: the open of Tag 01O8 over an affine open of the base

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `f : T ⟶ S` a morphism of
schemes, `ℒ` an invertible `𝒪_T`-module and `ψ` a graded map from `f^*𝒜` to the powers of `ℒ` —
the data of [Stacks, Tag 01O8], carried by
`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap`.  The open `U(ψ)` of
that tag is the union of the nonvanishing opens `U_{ψ(a)}` over **all** triples `(V, d, a)` with
`V ⊆ S` affine open and `a ∈ 𝒜_d(V)` homogeneous of positive degree.

Clause (3) of [Stacks, Tag 01O9] restricts the triple `(U(ψ), r_{ℒ,ψ}, θ)` to `U(ψ) ∩ f^{-1}(V)`
for one affine open `V` of the base and matches it with the triple of [Stacks, Tag 01NK] for the
graded ring `A = 𝒜(V)`.  The open of that absolute triple is the union of the `U_{ψ(g)}` over the
homogeneous `g ∈ A_+` — that is, over the sections of positive degree **over `V` itself**, a far
smaller family than the one defining `U(ψ)`.  This file proves the two opens agree:

`U(ψ) ∩ f^{-1}(V) = U(ψ_V)` for `V ⊆ S` affine open.

`⊇` is formal: `V` is one of the affine opens the union defining `U(ψ)` ranges over, so each
member of the smaller family is a member of the larger, and each lies in `f^{-1}(V)`.

`⊆` is not formal, and is the content of the file.  A point of `U(ψ) ∩ f^{-1}(V)` is given by a
section `a` of `𝒜_d` over *some* affine open `W`, which need not extend to `V`; what makes the
inclusion true is that the homogeneous pieces of `𝒜` are **quasi-coherent**, so that over an
affine open a section defined on a basic open becomes the restriction of a global one after
multiplication by a power of the defining function.  That hypothesis needs no importing: it is
the field `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.isQuasicoherent`,
registered as an instance, so the identification holds for every `GradedPowerMap` on no
hypothesis beyond the affineness of `V`.

## Main definitions

* `…GradedPowerMap.coveringOpenOver`: **`U(ψ_V)`**, the union of the `U_{ψ(a)}` over the
  homogeneous sections `a` of positive degree of `𝒜` **over the single open `V`**.  For `V`
  affine this is the open of the Tag 01NK triple that clause (3) of Tag 01O9 compares against.

## Main results

* `…GradedPowerMap.value_res` and `…GradedPowerMap.value_smul`: the value `ψ(a)` commutes with
  restriction of the base open, and is `𝒪_S`-linear in `a`, the scalar acting on `ℒ^{⊗ n}`
  through `f^♯`.  These are the naturality and the linearity of the component `ψ_n`, read through
  the identification of the sections of `f_*(ℒ^{⊗ n})` over `V` with those of `ℒ^{⊗ n}` over
  `f^{-1}(V)`.
* `…GradedPowerMap.exists_section_over_of_mem`: **the quasi-coherence step.**  If `ψ(a)` does not
  vanish at a point `x` lying over an affine open `V`, for `a` a section of `𝒜_n` over any open,
  then there is a section `t` of `𝒜_n` **over `V`** with `ψ(t)` not vanishing at `x`.
* `…GradedPowerMap.coveringOpen_inf_preimage_eq`: **`U(ψ) ∩ f^{-1}(V) = U(ψ_V)`** for `V` affine,
  with the two inclusions `coveringOpenOver_le_inf` and `inf_le_coveringOpenOver`.
* `…GradedPowerMap.iSup_coveringOpenOver_eq_coveringOpen` and
  `…GradedPowerMap.coveringOpenOver_inf_preimage_eq`: the same equality read as the two inputs a
  directed gluing along the preimages of the affine opens of the base consumes — that the
  `U(ψ_V)` cover `U(ψ)`, and that `U(ψ_V) ∩ f^{-1}(Z) = U(ψ_Z)` for affine `Z ≤ V`.
* `…GradedPowerMap.preimage_toBase_eq` and `…GradedPowerMap.image_preimage_toBase_eq`: the
  identification at the shape `AlgebraicGeometry.Scheme.glueOverAffinePreimages` presents its
  pieces in.  Along the structure morphism `…GradedPowerMap.toBase` of `U(ψ)` over the base, the
  preimage of an affine open `V` is the part of `U(ψ)` cut out by `U(ψ_V)`, and its image in `T`
  is `U(ψ_V)` on the nose — so the pieces of that gluing *are* the sources of the
  [Stacks, Tag 01NK] prescriptions, with nothing cut away.

## Implementation notes

The proof of `exists_section_over_of_mem` is the classical one.  Given `x ∈ U_{ψ(a)}` with
`a ∈ 𝒜_n(W)` and `f(x) ∈ V`, the basic opens of the affine `V` are a basis
(`AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le`), so there is `g ∈ Γ(V, 𝒪_S)` with
`f(x) ∈ S_g ⊆ W`.  Quasi-coherence over `V` — affine, hence quasi-compact and quasi-separated —
gives `k` and `t ∈ 𝒜_n(V)` with `t|_{S_g} = g^k · a|_{S_g}`
(`Stacks.AlgebraicGeometry.QcqsLocalization.exists_eq_pow_smul_of_isCompact_of_isQuasiSeparated`).
Applying `ψ` and computing nonvanishing loci, `ψ(t)` and `ψ(a)` differ over `f^{-1}(S_g)` by the
scalar `f^♯(g^k)`, which is a unit there; and scaling by a function intersects the nonvanishing
locus with a basic open (`Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_smul`), that basic
open being everything when the function is a unit.  So the two loci agree over `f^{-1}(S_g)`,
which contains `x`.

The degree is carried as `d + 1`, matching
`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.PositiveSection`, so that positivity
needs no side condition; `coveringOpenOver` is indexed by a sigma type rather than a structure
because, `V` being fixed, only the degree and the section vary.

## The tag

The whole statement of [Stacks, Tag 01O9] is
`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.tag01O9`.

## References

* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn nonvanishingLocusOn_res
  nonvanishingLocusOn_smul)
open Stacks.AlgebraicGeometry.QcqsLocalization
  (exists_eq_pow_smul_of_isCompact_of_isQuasiSeparated)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace GradedPowerMap

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f)

/-! ### Restriction and linearity of the values of `ψ` -/

/-- **`ψ` is `𝒪_S`-linear on homogeneous sections**, the scalar acting on the value through
`f^♯`: for `r ∈ Γ(V, 𝒪_S)` the value `ψ(r · a)` is `f^♯(r) · ψ(a)` in `Γ(f^{-1}(V), ℒ^{⊗ n})`.
This is the linearity of the component `ψ_n` over `Γ(V, 𝒪_S)`, the sections of `f_*(ℒ^{⊗ n})`
over `V` being a `Γ(V, 𝒪_S)`-module exactly through `f^♯`. -/
public theorem value_smul (n : ℕ) (V : S.Opens) (r : Γ(S, V)) (a : Γ(A.piece (n : ℤ), V)) :
    P.value n V (r • a) = (f.app V r) • P.value n V a :=
  ((P.ψ n).val.app (op V)).hom.map_smul r a

/-- **The value of `ψ` commutes with restriction of the base open**: for `V ≤ W` the value of `ψ`
at `a|_V` is the restriction to `f^{-1}(V)` of its value at `a`.  This is the naturality of the
component `ψ_n`. -/
public theorem value_res (n : ℕ) {V W : S.Opens} (hVW : V ≤ W) (a : Γ(A.piece (n : ℤ), W)) :
    P.value n V ((A.piece (n : ℤ)).presheaf.map (homOfLE hVW).op a) =
      (natTensorPow P.L n).presheaf.map (homOfLE (f.preimage_mono hVW)).op (P.value n W a) :=
  congrFun (congrArg (fun g => g.hom) ((P.ψ n).val.naturality (homOfLE hVW).op)) a

/-! ### The quasi-coherence step -/

/-- **A member of the family defining `U(ψ)` is, over an affine open of the base, caught by a
section over that open alone.**  If the value of `ψ` at a homogeneous section `a` of `𝒜_n` over
an arbitrary open `W` does not vanish at a point `x` lying over an affine open `V`, then there is
a homogeneous section `t` of `𝒜_n` **over `V`** whose value does not vanish at `x` either.

This is where quasi-coherence of `𝒜_n` enters, and it is the one non-formal ingredient of
`coveringOpen_inf_preimage_eq`: a section over a basic open `S_g` of `V` becomes the restriction
of a section over `V` after multiplication by a power of `g`, and that power is a unit on `S_g`,
so applying `ψ` changes the nonvanishing locus only outside `f^{-1}(S_g)`. -/
public theorem exists_section_over_of_mem {V : S.Opens} (hV : IsAffineOpen V) (n : ℕ)
    (W : S.Opens) (a : Γ(A.piece (n : ℤ), W)) {x : T}
    (hx : x ∈ P.nonvanishingOpenAt n W a) (hxV : x ∈ f ⁻¹ᵁ V) :
    ∃ t : Γ(A.piece (n : ℤ), V), x ∈ P.nonvanishingOpenAt n V t := by
  have hxW : x ∈ f ⁻¹ᵁ W := P.nonvanishingOpenAt_le_preimage n W a hx
  obtain ⟨g, hgW, hg⟩ := hV.exists_basicOpen_le (⟨f.base x, hxW⟩ : W) hxV
  have hBV : S.basicOpen g ≤ V := S.basicOpen_le g
  obtain ⟨k, t, ht⟩ := exists_eq_pow_smul_of_isCompact_of_isQuasiSeparated
    (A.piece (n : ℤ)) hV.isCompact hV.isQuasiSeparated g
    ((A.piece (n : ℤ)).presheaf.map (homOfLE hgW).op a)
  refine ⟨t, ?_⟩
  have e1 : (natTensorPow P.L n).presheaf.map (homOfLE (f.preimage_mono hBV)).op
        (P.value n V t)
      = (f.app (S.basicOpen g) ((S.presheaf.map (homOfLE hBV).op g) ^ k)) •
        (natTensorPow P.L n).presheaf.map (homOfLE (f.preimage_mono hgW)).op
          (P.value n W a) := by
    rw [← P.value_res n hBV t, ht, P.value_smul, P.value_res n hgW a]
  have hunit : IsUnit (f.app (S.basicOpen g) ((S.presheaf.map (homOfLE hBV).op g) ^ k)) :=
    IsUnit.map (f.app (S.basicOpen g)).hom
      ((S.toRingedSpace.isUnit_res_basicOpen g).pow k)
  have key := nonvanishingLocusOn_res (natTensorPow P.L n) (f.preimage_mono hBV)
    (P.value n V t)
  rw [e1, nonvanishingLocusOn_smul, Scheme.basicOpen_of_isUnit _ hunit,
    nonvanishingLocusOn_res] at key
  have hxB : x ∈ f ⁻¹ᵁ S.basicOpen g := hg
  exact (key.subset ⟨hxB, hxB, hx⟩).2

/-! ### The open over one open of the base -/

/-- **`U(ψ_V)`**: the union of the opens `U_{ψ(a)}` on which the value of `ψ` at a homogeneous
section `a` of positive degree of `𝒜` **over the single open `V`** does not vanish.

For `V` affine this is the open of the [Stacks, Tag 01NK] triple that clause (3) of
[Stacks, Tag 01O9] compares the restriction of `(U(ψ), r_{ℒ,ψ}, θ)` against: the graded ring
there is `A = 𝒜(V)`, whose homogeneous elements of positive degree are exactly the sections
indexed here.  The degree is carried as `d + 1`, as in `PositiveSection`. -/
public def coveringOpenOver (V : S.Opens) : T.Opens :=
  ⨆ p : (d : ℕ) × Γ(A.piece ((d + 1 : ℕ) : ℤ), V), P.nonvanishingOpenAt (p.1 + 1) V p.2

/-- Each member of the family defining `U(ψ_V)` lies in it. -/
public theorem nonvanishingOpenAt_le_coveringOpenOver (V : S.Opens) (d : ℕ)
    (a : Γ(A.piece ((d + 1 : ℕ) : ℤ), V)) :
    P.nonvanishingOpenAt (d + 1) V a ≤ P.coveringOpenOver V :=
  le_iSup (fun p : (d : ℕ) × Γ(A.piece ((d + 1 : ℕ) : ℤ), V) =>
    P.nonvanishingOpenAt (p.1 + 1) V p.2) ⟨d, a⟩

/-- `U(ψ_V)` lies over `V`: its members are nonvanishing loci of sections over `f^{-1}(V)`. -/
public theorem coveringOpenOver_le_preimage (V : S.Opens) :
    P.coveringOpenOver V ≤ f ⁻¹ᵁ V :=
  iSup_le fun p => P.nonvanishingOpenAt_le_preimage (p.1 + 1) V p.2

/-- For `V` affine, `U(ψ_V)` lies in `U(ψ)`: the triples it is indexed by are among those
defining `U(ψ)`. -/
public theorem coveringOpenOver_le_coveringOpen {V : S.Opens} (hV : IsAffineOpen V) :
    P.coveringOpenOver V ≤ P.coveringOpen :=
  iSup_le fun p => P.nonvanishingOpenAt_le_coveringOpen p.1 V hV p.2

/-- **The formal inclusion `U(ψ_V) ⊆ U(ψ) ∩ f^{-1}(V)`** for `V` affine. -/
public theorem coveringOpenOver_le_inf {V : S.Opens} (hV : IsAffineOpen V) :
    P.coveringOpenOver V ≤ P.coveringOpen ⊓ f ⁻¹ᵁ V :=
  le_inf (P.coveringOpenOver_le_coveringOpen hV) (P.coveringOpenOver_le_preimage V)

/-- **The inclusion `U(ψ) ∩ f^{-1}(V) ⊆ U(ψ_V)`** for `V` affine: a point of `U(ψ)` lying over
`V` is already caught by a section of `𝒜` over `V` itself.  This is `exists_section_over_of_mem`
applied to the triple whose member contains the point, and it is the half of the identification
that uses quasi-coherence of the homogeneous pieces of `𝒜`. -/
public theorem inf_le_coveringOpenOver {V : S.Opens} (hV : IsAffineOpen V) :
    P.coveringOpen ⊓ f ⁻¹ᵁ V ≤ P.coveringOpenOver V := by
  intro x hx
  obtain ⟨p, hp⟩ := P.exists_mem_openOfPositiveSection_of_mem_coveringOpen hx.1
  obtain ⟨t, ht⟩ := P.exists_section_over_of_mem hV (p.deg + 1) p.base p.val hp hx.2
  exact P.nonvanishingOpenAt_le_coveringOpenOver V p.deg t ht

/-- **`U(ψ) ∩ f^{-1}(V) = U(ψ_V)` for `V ⊆ S` an affine open**: the part of the open `U(ψ)` of
[Stacks, Tag 01O8] lying over an affine open of the base is the union of the nonvanishing opens
of the values of `ψ` at the homogeneous sections of positive degree over that one open.

This is the identification of opens that clause (3) of [Stacks, Tag 01O9] asserts, and it is what
lets the affine-local morphisms `r_{ℒ,ψ}` be glued along the preimages of the affine opens of the
base: the piece of `U(ψ)` over `V` is exactly the source of the [Stacks, Tag 01NK] prescription
over `V`, with nothing cut away. -/
public theorem coveringOpen_inf_preimage_eq {V : S.Opens} (hV : IsAffineOpen V) :
    P.coveringOpen ⊓ f ⁻¹ᵁ V = P.coveringOpenOver V :=
  le_antisymm (P.inf_le_coveringOpenOver hV) (P.coveringOpenOver_le_inf hV)

/-- **`U(ψ)` is covered by the opens `U(ψ_V)` over the affine opens `V` of the base.**  This is
`coveringOpen_inf_preimage_eq` read as a cover: the pieces of `U(ψ)` lying over the affine opens
of the base are the sources of the [Stacks, Tag 01NK] prescriptions, so a morphism out of `U(ψ)`
may be prescribed on them. -/
public theorem iSup_coveringOpenOver_eq_coveringOpen :
    (⨆ V : {V : S.Opens // IsAffineOpen V}, P.coveringOpenOver V.1) = P.coveringOpen :=
  le_antisymm (iSup_le fun V => P.coveringOpenOver_le_coveringOpen V.2)
    (P.coveringOpen_le_iff.2 fun p =>
      le_trans (P.nonvanishingOpenAt_le_coveringOpenOver p.base p.deg p.val)
        (le_iSup (fun V : {V : S.Opens // IsAffineOpen V} => P.coveringOpenOver V.1)
          ⟨p.base, p.isAffineOpen⟩))

/-- **`U(ψ_V)` is compatible with shrinking the affine open of the base**: for affine opens
`Z ≤ V` of `S`, the part of `U(ψ_V)` lying over `Z` is `U(ψ_Z)`.  This is the nested
compatibility a directed gluing argument along the preimages of the affine opens consumes, and it
is two applications of `coveringOpen_inf_preimage_eq`. -/
public theorem coveringOpenOver_inf_preimage_eq {Z V : S.Opens} (hZ : IsAffineOpen Z)
    (hV : IsAffineOpen V) (hZV : Z ≤ V) :
    P.coveringOpenOver V ⊓ f ⁻¹ᵁ Z = P.coveringOpenOver Z := by
  rw [← P.coveringOpen_inf_preimage_eq hV, ← P.coveringOpen_inf_preimage_eq hZ, inf_assoc,
    inf_eq_right.mpr (f.preimage_mono hZV)]

/-! ### The identification at the shape a directed gluing consumes -/

/-- **The structure morphism of `U(ψ)` over the base**, the inclusion of `U(ψ)` in `T` followed
by `f`.  `AlgebraicGeometry.Scheme.glueOverAffinePreimages` assembles a morphism out of
`U(ψ).toScheme` from morphisms on the preimages of the affine opens of `S` along this morphism,
so it is the morphism whose preimages the two results below compute. -/
public def toBase : P.coveringOpen.toScheme ⟶ S := P.coveringOpen.ι ≫ f

/-- **The piece of `U(ψ)` over an affine open `V` of the base is `U(ψ_V)`.**  Read inside
`U(ψ).toScheme`, the preimage of `V` along the structure morphism is the preimage of `U(ψ_V)`
along the inclusion of `U(ψ)`.  This is `coveringOpen_inf_preimage_eq` at the shape the pieces of
`AlgebraicGeometry.Scheme.glueOverAffinePreimages` are presented in. -/
public theorem preimage_toBase_eq (V : S.Opens) (hV : IsAffineOpen V) :
    P.toBase ⁻¹ᵁ V = P.coveringOpen.ι ⁻¹ᵁ P.coveringOpenOver V := by
  rw [← P.coveringOpen_inf_preimage_eq hV]
  show _ = P.coveringOpen.ι ⁻¹ᵁ (P.coveringOpen ⊓ f ⁻¹ᵁ V)
  rw [Scheme.Hom.preimage_inf, P.coveringOpen.ι_preimage_self, top_inf_eq]
  rfl

/-- **The same piece, read back in `T`**: the image in `T` of the part of `U(ψ)` lying over an
affine open `V` of the base is `U(ψ_V)` on the nose.  This is the form in which the local pieces
of a glued `r_{ℒ,ψ}` are compared with the sources of the [Stacks, Tag 01NK] prescriptions. -/
public theorem image_preimage_toBase_eq (V : S.Opens) (hV : IsAffineOpen V) :
    P.coveringOpen.ι ''ᵁ (P.toBase ⁻¹ᵁ V) = P.coveringOpenOver V := by
  rw [P.preimage_toBase_eq V hV]
  simpa [Scheme.Hom.image_preimage_eq_opensRange_inf] using
    inf_eq_right.mpr (P.coveringOpenOver_le_coveringOpen hV)

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
