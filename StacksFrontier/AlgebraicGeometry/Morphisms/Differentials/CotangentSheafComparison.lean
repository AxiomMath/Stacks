module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSheafQuasicoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two sheaves of relative differentials of a morphism of schemes agree

The repository carries two independent constructions of the sheaf of relative differentials of
a morphism of schemes `f : X ⟶ S`, each with its own API and with no statement relating them.

* `AlgebraicGeometry.Scheme.Hom.relativeDifferentials f` is the object corepresenting the
  derivations functor, obtained from corepresentability on the open-cover site. The canonical
  morphism of Stacks Project, Tag 01UV is built from it.
* `Stacks.Smooth.cotangentSheaf f` is the sheafification of the presheaf of sectionwise Kähler
  differentials. Quasi-coherence, the affine comparison with `Ω[Γ(X,W)⁄Γ(S,V)]`, and the
  corepresentability statements in chart form are all proved for it.

Both are objects of `X.Modules` carrying a universal derivation of the *same* morphism of
sheaves of rings `f⁻¹𝒪_S ⟶ 𝒪_X`, namely `AlgebraicGeometry.inverseImageStructureMap f`, and in
both developments a relative derivation is the same type, `M.val.Derivation' φ.hom`. So the two
universal properties — Tag 08RM for the first and Tag 04BL for the second — identify the two
objects, uniquely and compatibly with their universal derivations. That identification is what
this file provides.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.cotangentSheafIso` is the canonical isomorphism
  `Ω_{X/S} ≅ Ω_{X/S}` between the two constructions.

## Main results

* `AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation_postcomp_cotangentSheafIso_hom` and
  `AlgebraicGeometry.Scheme.Hom.universalDerivation_postcomp_cotangentSheafIso_inv`: the
  isomorphism carries each universal derivation to the other, which is what makes it canonical.
* `AlgebraicGeometry.Scheme.Hom.eq_of_postcomp_eq_universalDerivation` and
  `AlgebraicGeometry.Scheme.Hom.eq_of_postcomp_eq_universalRelativeDerivation`: nothing else
  does, in either direction.
* `AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentials`: the first consequence,
  transported across the isomorphism from `Stacks.Smooth.isQuasicoherent_cotangentSheaf`.

## Implementation notes

The two developments are stated over different sites — `TopCat.Sheaf CommRingCat X` with the
module universe left free in the first, the small open-cover site of a `RingedSpace` in the
second — but at a morphism of schemes both specialize to the same site, the same sheaf of
rings, and the same derivation type. Every such coincidence used here is a definitional one,
recorded as a `rfl` proof (`inverseImageStructureMap_ringedSpaceHom`, and the `rfl` bodies of
the two unique-existence statements), so no transport along an equation of types is needed.

No `@[stacks …]` attribute is placed. The isomorphism is a statement about two formalizations
of one notion rather than about the mathematics of any tag, and `isQuasicoherent_cotangentSheaf`
— the only mathematical content transported — is itself untagged in the development it comes
from, so tagging the transported copy would claim more than the source does.

## References

* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM)
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The structure map `f⁻¹𝒪_S ⟶ 𝒪_X` used by the two developments is the same morphism: the
one of the morphism of schemes, and the one of the underlying morphism of ringed spaces. -/
theorem inverseImageStructureMap_ringedSpaceHom :
    Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap
      (Stacks.Smooth.ringedSpaceHom f) = inverseImageStructureMap f :=
  rfl

/-- Postcomposing a relative derivation with a composite of morphisms of sheaves of modules is
postcomposing twice. -/
theorem relativeDerivation_postcomp_comp {F G H : X.Modules}
    (d : SheafOfModules.SheafDerivation (inverseImageStructureMap f) F) (α : F ⟶ G) (β : G ⟶ H) :
    d.postcomp (α ≫ β).val = (d.postcomp α.val).postcomp β.val :=
  rfl

/-- Postcomposing a relative derivation with the identity does nothing. -/
theorem relativeDerivation_postcomp_id {F : X.Modules}
    (d : SheafOfModules.SheafDerivation (inverseImageStructureMap f) F) :
    d.postcomp (𝟙 F : F ⟶ F).val = d :=
  rfl

/-- Equal relative derivations have equal postcompositions. Stated as a lemma rather than
rewritten at the use sites: the two developments spell the ambient site differently, so a
`rw` of an equation of derivations is not type-correct at `implicit` transparency, while an
application of this lemma is. -/
theorem relativeDerivation_postcomp_congr {F G : X.Modules}
    {d d' : SheafOfModules.SheafDerivation (inverseImageStructureMap f) F}
    (h : d = d') (α : F ⟶ G) : d.postcomp α.val = d'.postcomp α.val := by
  rw [h]

/-- **Stacks Project, Tag 04BL** at a morphism of schemes, stated for the derivation type of
the `relativeDifferentials` development: every relative derivation factors uniquely through the
universal derivation of `Stacks.Smooth.cotangentSheaf`. -/
theorem existsUnique_hom_cotangentSheaf (F : X.Modules)
    (D : SheafOfModules.SheafDerivation (inverseImageStructureMap f) F) :
    ∃! α : Stacks.Smooth.cotangentSheaf f ⟶ F,
      (Stacks.Sheaves.RingedSpaceDifferentials.universalDerivation
        (Stacks.Smooth.ringedSpaceHom f)).postcomp α.val = D :=
  Stacks.Sheaves.Differentials.universalDerivation_isUniversal _ _ _ F D

/-- **Stacks Project, Tag 08RM** at a morphism of schemes: every relative derivation factors
uniquely through the universal derivation of
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials`. -/
@[ega "IV 16.5.3" "(ii)"]
theorem existsUnique_hom_relativeDifferentials (F : X.Modules)
    (D : SheafOfModules.SheafDerivation (inverseImageStructureMap f) F) :
    ∃! α : relativeDifferentials f ⟶ F,
      (universalRelativeDerivation f).postcomp α.val = D :=
  SheafOfModules.universalDerivation_isUniversal _ F D

/-- A morphism out of `Stacks.Smooth.cotangentSheaf f` is determined by the derivation it
induces. -/
theorem eq_of_postcomp_eq_universalDerivation {F : X.Modules}
    {α β : Stacks.Smooth.cotangentSheaf f ⟶ F}
    (h : (Stacks.Sheaves.RingedSpaceDifferentials.universalDerivation
        (Stacks.Smooth.ringedSpaceHom f)).postcomp α.val =
      (Stacks.Sheaves.RingedSpaceDifferentials.universalDerivation
        (Stacks.Smooth.ringedSpaceHom f)).postcomp β.val) : α = β :=
  (existsUnique_hom_cotangentSheaf f F _).unique h rfl

/-- A morphism out of `AlgebraicGeometry.Scheme.Hom.relativeDifferentials f` is determined by
the derivation it induces. -/
theorem eq_of_postcomp_eq_universalRelativeDerivation {F : X.Modules}
    {α β : relativeDifferentials f ⟶ F}
    (h : (universalRelativeDerivation f).postcomp α.val =
      (universalRelativeDerivation f).postcomp β.val) : α = β :=
  (existsUnique_hom_relativeDifferentials f F _).unique h rfl

/-- The canonical morphism from the corepresenting sheaf of relative differentials to the
sheafification of the sectionwise Kähler differentials: the unique one carrying the universal
derivation of the first to that of the second. -/
noncomputable def toCotangentSheaf :
    relativeDifferentials f ⟶ Stacks.Smooth.cotangentSheaf f :=
  (existsUnique_hom_relativeDifferentials f _
    (Stacks.Sheaves.RingedSpaceDifferentials.universalDerivation
      (Stacks.Smooth.ringedSpaceHom f))).exists.choose

/-- The defining property of `AlgebraicGeometry.Scheme.Hom.toCotangentSheaf`. -/
theorem universalRelativeDerivation_postcomp_toCotangentSheaf :
    (universalRelativeDerivation f).postcomp (toCotangentSheaf f).val =
      Stacks.Sheaves.RingedSpaceDifferentials.universalDerivation
        (Stacks.Smooth.ringedSpaceHom f) :=
  (existsUnique_hom_relativeDifferentials f _
    (Stacks.Sheaves.RingedSpaceDifferentials.universalDerivation
      (Stacks.Smooth.ringedSpaceHom f))).exists.choose_spec

/-- The canonical morphism from the sheafification of the sectionwise Kähler differentials to
the corepresenting sheaf of relative differentials: the unique one carrying the universal
derivation of the first to that of the second. -/
noncomputable def ofCotangentSheaf :
    Stacks.Smooth.cotangentSheaf f ⟶ relativeDifferentials f :=
  (existsUnique_hom_cotangentSheaf f _ (universalRelativeDerivation f)).exists.choose

/-- The defining property of `AlgebraicGeometry.Scheme.Hom.ofCotangentSheaf`. -/
theorem universalDerivation_postcomp_ofCotangentSheaf :
    (Stacks.Sheaves.RingedSpaceDifferentials.universalDerivation
        (Stacks.Smooth.ringedSpaceHom f)).postcomp (ofCotangentSheaf f).val =
      universalRelativeDerivation f :=
  (existsUnique_hom_cotangentSheaf f _ (universalRelativeDerivation f)).exists.choose_spec

/-- The two sheaves of relative differentials of a morphism of schemes are canonically
isomorphic. -/
noncomputable def cotangentSheafIso :
    relativeDifferentials f ≅ Stacks.Smooth.cotangentSheaf f where
  hom := toCotangentSheaf f
  inv := ofCotangentSheaf f
  hom_inv_id :=
    eq_of_postcomp_eq_universalRelativeDerivation f
      ((relativeDerivation_postcomp_comp f _ (toCotangentSheaf f)
            (ofCotangentSheaf f)).trans
        (((relativeDerivation_postcomp_congr f
                (universalRelativeDerivation_postcomp_toCotangentSheaf f)
              (ofCotangentSheaf f)).trans
            (universalDerivation_postcomp_ofCotangentSheaf f)).trans
          (relativeDerivation_postcomp_id f _).symm))
  inv_hom_id :=
    eq_of_postcomp_eq_universalDerivation f
      ((relativeDerivation_postcomp_comp f _ (ofCotangentSheaf f)
            (toCotangentSheaf f)).trans
        (((relativeDerivation_postcomp_congr f (universalDerivation_postcomp_ofCotangentSheaf f)
              (toCotangentSheaf f)).trans
            (universalRelativeDerivation_postcomp_toCotangentSheaf f)).trans
          (relativeDerivation_postcomp_id f _).symm))

/-- The forward map of `cotangentSheafIso` is `toCotangentSheaf`. -/
@[simp]
theorem cotangentSheafIso_hom : (cotangentSheafIso f).hom = toCotangentSheaf f := rfl

/-- The inverse map of `cotangentSheafIso` is `ofCotangentSheaf`. -/
@[simp]
theorem cotangentSheafIso_inv : (cotangentSheafIso f).inv = ofCotangentSheaf f := rfl

/-- The isomorphism carries the universal derivation of the corepresenting sheaf to the
universal derivation of the sheafified sectionwise one. -/
theorem universalRelativeDerivation_postcomp_cotangentSheafIso_hom :
    (universalRelativeDerivation f).postcomp (cotangentSheafIso f).hom.val =
      Stacks.Sheaves.RingedSpaceDifferentials.universalDerivation
        (Stacks.Smooth.ringedSpaceHom f) :=
  universalRelativeDerivation_postcomp_toCotangentSheaf f

/-- The inverse of `cotangentSheafIso` carries the universal derivation of the sheafified
sectionwise sheaf to the universal derivation of the corepresenting one. -/
theorem universalDerivation_postcomp_cotangentSheafIso_inv :
    (Stacks.Sheaves.RingedSpaceDifferentials.universalDerivation
        (Stacks.Smooth.ringedSpaceHom f)).postcomp (cotangentSheafIso f).inv.val =
      universalRelativeDerivation f :=
  universalDerivation_postcomp_ofCotangentSheaf f

/-- The sheaf of relative differentials of a morphism of schemes is quasi-coherent, for the
corepresenting construction: transported across
`AlgebraicGeometry.Scheme.Hom.cotangentSheafIso` from the sheafified construction, where it is
`Stacks.Smooth.isQuasicoherent_cotangentSheaf`. No hypothesis on `f` is needed, there as
here. -/
theorem isQuasicoherent_relativeDifferentials :
    (relativeDifferentials f).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (cotangentSheafIso f).symm
    (Stacks.Smooth.isQuasicoherent_cotangentSheaf f)

end AlgebraicGeometry.Scheme.Hom

end
