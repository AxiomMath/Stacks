module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleSurjective
public import StacksFrontier.AlgebraicGeometry.Size.BlowupContains
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChowDiagram
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# A scheme cover of a quasi-compact quasi-separated space, and a blowing up of that cover

An object `T` of the big fppf site over `S` whose represented presheaf admits a morphism of
finite presentation to a quasi-compact and absolutely quasi-separated algebraic space `X` has
quasi-compact and quasi-separated underlying scheme.  This is Stacks 06G5
(`AlgebraicGeometry.Space.qcqs_of_isFinitePresentation`) read on the scheme, through
`AlgebraicGeometry.Space.compactSpace_of_isQuasiCompactSpace_yoneda_obj` and
`AlgebraicGeometry.Space.quasiSeparatedSpace_of_isAbsolutelyQuasiSeparated_yoneda` (the
homeomorphism of Stacks 03BX between the point space of the represented presheaf and the scheme).

An admissible blowing up of a scheme contained in a big fppf site, in the sense of Stacks 080K,
is contained in the site, since the size of a blowing up is at most the size of its base
(`AlgebraicGeometry.Scheme.size_blowUp_le`) and the size of a scheme is an isomorphism invariant
(`AlgebraicGeometry.Scheme.size_congr`).  So the blowing up is an object of the big fppf category
over `S` whose underlying scheme is the blown-up scheme itself, and the blowing-up morphism is a
morphism of that category; as a morphism of algebraic spaces it is proper, and surjective when
the admissible open is dense.

## Main results

* `AlgebraicGeometry.Space.compactSpace_and_quasiSeparatedSpace_of_isFinitePresentation`: the
  scheme of a site object of finite presentation over a quasi-compact and absolutely
  quasi-separated algebraic space is quasi-compact and quasi-separated.
* `AlgebraicGeometry.BigFppfSite.contains_of_isAdmissibleBlowup`: an admissible blowing up of a
  scheme contained in a big fppf site is contained in it.
* `AlgebraicGeometry.Space.admissibleBlowupObj` and
  `AlgebraicGeometry.Space.admissibleBlowupObjHom`: that blowing up and its morphism, as an
  object and a morphism of the big fppf category over `S`.  The underlying scheme and the
  underlying morphism of schemes are the given ones, by
  `AlgebraicGeometry.Space.toScheme_obj_admissibleBlowupObj` and
  `AlgebraicGeometry.Space.toScheme_map_admissibleBlowupObjHom`, both true by definition.
* `AlgebraicGeometry.Space.isProper_yoneda_map_admissibleBlowupObjHom` and
  `AlgebraicGeometry.Space.isSurjective_yoneda_map_admissibleBlowupObjHom`: that morphism is
  proper, and — when the admissible open is dense — surjective, as a morphism of algebraic
  spaces.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 06G5](https://stacks.math.columbia.edu/tag/06G5)
* [Stacks Project, Tag 080K](https://stacks.math.columbia.edu/tag/080K)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0F86](https://stacks.math.columbia.edu/tag/0F86)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace BigFppfSite

/-- **An admissible blowing up of a scheme contained in a big fppf site is contained in it.** -/
theorem contains_of_isAdmissibleBlowup (B : BigFppfSite.{u}) {X X' : Scheme.{u}}
    (hX : B.Contains X) {U : X.Opens} {f : X' ⟶ X}
    (hf : Stacks.Blowup.IsAdmissibleBlowup U f) : B.Contains X' := by
  obtain ⟨I, -, -, e, -⟩ := (Stacks.Blowup.isAdmissibleBlowup_iff U f).mp hf
  exact (Scheme.size_congr e).trans_lt (B.contains_blowUp hX I)

end BigFppfSite

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-compactness and quasi-separatedness of a scheme cover -/

/-- **The scheme of a site object of finite presentation over a quasi-compact and absolutely
quasi-separated algebraic space is quasi-compact and quasi-separated.** -/
theorem compactSpace_and_quasiSeparatedSpace_of_isFinitePresentation
    (hZ : B.Contains (⊤_ Scheme.{u})) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hf : IsFinitePresentation B S hS f) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj T) ∧
      QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj T) := by
  obtain ⟨hqc, hqs⟩ := qcqs_of_isFinitePresentation B S hS hZ
    (isAlgebraicSpace_yoneda B S hS T) hX hXqc hXqs hf
  exact ⟨compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hqc,
    quasiSeparatedSpace_of_isAbsolutelyQuasiSeparated_yoneda B S hS hZ T hqs⟩

/-! ### An admissible blowing up of a scheme of the site, as an object of the site -/

variable {B S hS}

/-- **An admissible blowing up of the scheme of a site object, as an object of the big fppf
category over `S`.**  Its underlying scheme is the blown-up scheme itself, by
`AlgebraicGeometry.Space.toScheme_obj_admissibleBlowupObj`; the structure morphism to `S` is the
blowing-up morphism followed by that of `T`. -/
def admissibleBlowupObj (T : BigFppfOver B S hS) {T' : Scheme.{u}}
    {U : ((BigFppfOver.toScheme B S hS).obj T).Opens}
    {f : T' ⟶ (BigFppfOver.toScheme B S hS).obj T}
    (hf : Stacks.Blowup.IsAdmissibleBlowup U f) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (B.contains_of_isAdmissibleBlowup T.left.property hf)
    (f ≫ B.inclusion.map T.hom)

/-- The blowing-up morphism, as a morphism of the big fppf category over `S`. -/
def admissibleBlowupObjHom (T : BigFppfOver B S hS) {T' : Scheme.{u}}
    {U : ((BigFppfOver.toScheme B S hS).obj T).Opens}
    {f : T' ⟶ (BigFppfOver.toScheme B S hS).obj T}
    (hf : Stacks.Blowup.IsAdmissibleBlowup U f) : admissibleBlowupObj T hf ⟶ T :=
  Over.homMk (ObjectProperty.homMk f) rfl

/-- The scheme underlying `AlgebraicGeometry.Space.admissibleBlowupObj` is the blown-up scheme
itself. -/
theorem toScheme_obj_admissibleBlowupObj (T : BigFppfOver B S hS) {T' : Scheme.{u}}
    {U : ((BigFppfOver.toScheme B S hS).obj T).Opens}
    {f : T' ⟶ (BigFppfOver.toScheme B S hS).obj T}
    (hf : Stacks.Blowup.IsAdmissibleBlowup U f) :
    (BigFppfOver.toScheme B S hS).obj (admissibleBlowupObj T hf) = T' :=
  rfl

/-- The morphism of schemes underlying
`AlgebraicGeometry.Space.admissibleBlowupObjHom` is the blowing-up morphism itself. -/
theorem toScheme_map_admissibleBlowupObjHom (T : BigFppfOver B S hS) {T' : Scheme.{u}}
    {U : ((BigFppfOver.toScheme B S hS).obj T).Opens}
    {f : T' ⟶ (BigFppfOver.toScheme B S hS).obj T}
    (hf : Stacks.Blowup.IsAdmissibleBlowup U f) :
    (BigFppfOver.toScheme B S hS).map (admissibleBlowupObjHom T hf) = f :=
  rfl

/-- **An admissible blowing up of the scheme of a site object is proper as a morphism of
algebraic spaces.** -/
theorem isProper_yoneda_map_admissibleBlowupObjHom (T : BigFppfOver B S hS) {T' : Scheme.{u}}
    {U : ((BigFppfOver.toScheme B S hS).obj T).Opens}
    {f : T' ⟶ (BigFppfOver.toScheme B S hS).obj T}
    (hf : Stacks.Blowup.IsAdmissibleBlowup U f) :
    IsProper B S hS (yoneda.map (admissibleBlowupObjHom T hf)) :=
  isProper_yoneda_map B S hS _ hf.isProper

/-- **An admissible blowing up of the scheme of a site object along a topologically dense open
is surjective as a morphism of algebraic spaces.** -/
theorem isSurjective_yoneda_map_admissibleBlowupObjHom (T : BigFppfOver B S hS)
    {T' : Scheme.{u}} {U : ((BigFppfOver.toScheme B S hS).obj T).Opens}
    {f : T' ⟶ (BigFppfOver.toScheme B S hS).obj T}
    (hf : Stacks.Blowup.IsAdmissibleBlowup U f)
    (hU : Dense (U : Set ((BigFppfOver.toScheme B S hS).obj T))) :
    IsSurjective B S hS (yoneda.map (admissibleBlowupObjHom T hf)) :=
  isSurjective_yoneda_map B S hS _ (hf.surjective hU)

end Space

end AlgebraicGeometry

end
