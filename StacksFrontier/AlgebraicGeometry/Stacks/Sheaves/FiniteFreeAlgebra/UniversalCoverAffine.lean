module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.ActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.SpecBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.UniversalCover

/-!
# The universal degree-`d` cover over an affine base

Over an affine scheme `T` the degree-`d` cover attached to a point `y : T ⟶ X` of the scheme of
structure constants — the base change of the universal degree-`d` cover along `y` — is the
spectrum of the algebra of the free `d`-dimensional structure that `y` classifies. This is the
affine form of the comparison that the proof of Stacks 05YQ makes between the 1-morphism
`Spec : FA_d ⟶ ℋ_d` and the spectrum of a family of structures.

The same comparison turns clause (a) of that proof into a geometric statement: a unit-fixing
matrix `g` over `Γ(T, 𝒪_T)` carries the structure classified by `y` to the structure classified
by the image of `y` under the conjugation action, and therefore identifies the two degree-`d`
covers as schemes over `T`.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.conjugationStructureIsoOf`: the isomorphism of free
  `d`-dimensional structures given by a unit-fixing matrix.
* `AlgebraicGeometry.FiniteFreeAlgebra.conjugationSpecIsoOf` and
  `AlgebraicGeometry.FiniteFreeAlgebra.conjugationSpecIso`: the induced isomorphism of spectra
  over `Spec Γ(T, 𝒪_T)`, for an arbitrary representation and for the one of Stacks 05YM.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.exists_isPullback_specCover_universalCoverHom`: over an
  affine base, the spectrum of the structure classified by `y` is the base change of the
  universal degree-`d` cover along `y`.
* `AlgebraicGeometry.FiniteFreeAlgebra.exists_iso_pullback_universalCoverHom_conjugation`:
  clause (a) of the proof of Stacks 05YQ over an affine base — the conjugation action of a
  unit-fixing matrix does not change the degree-`d` cover as a scheme over the base.

## Implementation notes

The affine comparison is
`AlgebraicGeometry.FiniteFreeAlgebra.Carrier.isPullback_specCover_baseChange` for the
`Γ(X, 𝒪_X)`-algebra `Γ(T, 𝒪_T)` defined by `y`, pasted with the square of isomorphisms
`AlgebraicGeometry.Scheme.isoSpec_inv_naturality` that replaces `Spec Γ(T, 𝒪_T)` by `T` and
`Spec Γ(X, 𝒪_X)` by `X`; the structure classified by `y` is the extension of scalars of the
tautological one by
`AlgebraicGeometry.FiniteFreeAlgebra.map_universalStructure`. The comparison morphism is left
existentially quantified, because naming it would require the `Γ(X, 𝒪_X)`-algebra structure on
`Γ(T, 𝒪_T)` in the statement.

The isomorphism of structures attached to a unit-fixing matrix is built field by field out of
`AlgebraicGeometry.FiniteFreeAlgebra.conjugationIso` rather than by transporting that
isomorphism along the equality of structures: the equality holds by a rewrite inside the
representation of Stacks 05YM, which is a large tactic-generated term, and a transport along it
makes the kernel reduce a projection out of that term. Only the propositional field has to be
moved, and `AlgebraicGeometry.FiniteFreeAlgebra.StructureIso` is determined by its matrix.

## References

* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
* [Stacks Project, Tag 05YP](https://stacks.math.columbia.edu/tag/05YP)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable {d : ℕ} [NeZero d]

/-- Over an affine base, the degree-`d` cover attached to a point `y` of the scheme of structure
constants is the spectrum of the algebra of the free `d`-dimensional structure that `y`
classifies. -/
theorem exists_isPullback_specCover_universalCoverHom {T : Scheme.{u}} [IsAffine T]
    (y : T ⟶ scheme.{u} d) :
    ∃ p, IsPullback
      ((specCover ((representation.{u} d).equiv T y)).hom ≫ T.isoSpec.inv) p y
      (universalCoverHom.{u} d) := by
  let : Algebra ↥Γ(scheme.{u} d, ⊤) ↥Γ(T, ⊤) := y.appTop.hom.toAlgebra
  have halg : algebraMap ↥Γ(scheme.{u} d, ⊤) ↥Γ(T, ⊤) = y.appTop.hom :=
    RingHom.algebraMap_toAlgebra _
  have hn : map (algebraMap ↥Γ(scheme.{u} d, ⊤) ↥Γ(T, ⊤)) (universalStructure.{u} d) =
      (representation.{u} d).equiv T y := by
    rw [halg]; exact map_universalStructure d y
  have hcomm : T.isoSpec.inv ≫ y =
      Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(scheme.{u} d, ⊤) ↥Γ(T, ⊤))) ≫
        (scheme.{u} d).isoSpec.inv := by
    simp only [halg, CommRingCat.ofHom_hom]
    exact (Scheme.isoSpec_inv_naturality y).symm
  have hright : IsPullback T.isoSpec.inv
      (Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(scheme.{u} d, ⊤) ↥Γ(T, ⊤)))) y
      (scheme.{u} d).isoSpec.inv := IsPullback.of_horiz_isIso ⟨hcomm⟩
  have key : ∃ p, IsPullback
      ((specCover (map (algebraMap ↥Γ(scheme.{u} d, ⊤) ↥Γ(T, ⊤))
        (universalStructure.{u} d))).hom ≫ T.isoSpec.inv) p y (universalCoverHom.{u} d) :=
    ⟨_, (Carrier.isPullback_specCover_baseChange (S' := ↥Γ(T, ⊤))
      (universalStructure.{u} d)).paste_horiz hright⟩
  rw [← hn]
  exact key

/-- Clause (a) of the proof of Stacks 05YQ, in the form of an isomorphism of free
`d`-dimensional structures: a unit-fixing matrix `g` over the global sections of `T` carries the
structure classified by a point `y` of the scheme of structure constants to the structure
classified by the image of `y` under the conjugation action. -/
noncomputable def conjugationStructureIsoOf {T : Scheme.{u}} (rep : Representation.{u} d)
    (laws : ConjugationPreservesAlgebraLaws.{u} d) (g : UnitFixingMatrix Γ(T, ⊤) d)
    (y : T ⟶ scheme.{u} d) :
    StructureIso (rep.equiv T y) (rep.equiv T (conjugationOnPointsOf rep laws T g y)) where
  matrix := g.1⁻¹
  map_unit := (conjugationIso laws g (rep.equiv T y)).map_unit
  map_mul := by
    have h : conjugationAction laws g (rep.equiv T y) =
        rep.equiv T (conjugationOnPointsOf rep laws T g y) := by
      rw [conjugationOnPointsOf, Equiv.apply_symm_apply]
    have hcoeff : (conjugationAction laws g (rep.equiv T y)).coeff =
        (rep.equiv T (conjugationOnPointsOf rep laws T g y)).coeff :=
      congrArg FiniteFreeAlgebra.coeff h
    intro i j k
    simp_rw [← hcoeff]
    exact (conjugationIso laws g (rep.equiv T y)).map_mul i j k

/-- Clause (a) of the proof of Stacks 05YQ, geometrically: a unit-fixing matrix `g` over the
global sections of `T` induces an isomorphism, over `Spec Γ(T, 𝒪_T)`, of the spectra of the
structure classified by a point `y` and of the structure classified by the image of `y` under
the conjugation action. -/
noncomputable def conjugationSpecIsoOf {T : Scheme.{u}} (rep : Representation.{u} d)
    (laws : ConjugationPreservesAlgebraLaws.{u} d) (g : UnitFixingMatrix Γ(T, ⊤) d)
    (y : T ⟶ scheme.{u} d) :
    specCover (rep.equiv T y) ≅
      specCover (rep.equiv T (conjugationOnPointsOf rep laws T g y)) :=
  structureIsoEquivSpecIso _ _ (conjugationStructureIsoOf rep laws g y)

/-- `AlgebraicGeometry.FiniteFreeAlgebra.conjugationSpecIsoOf` for the representation of
Stacks 05YM. -/
noncomputable def conjugationSpecIso {T : Scheme.{u}}
    (laws : ConjugationPreservesAlgebraLaws.{u} d) (g : UnitFixingMatrix Γ(T, ⊤) d)
    (y : T ⟶ scheme.{u} d) :
    specCover ((representation.{u} d).equiv T y) ≅
      specCover ((representation.{u} d).equiv T (conjugationOnPoints laws T g y)) :=
  conjugationSpecIsoOf (representation.{u} d) laws g y

/-- Clause (a) of the proof of Stacks 05YQ for the universal cover, over an affine base: the
degree-`d` cover attached to a point `y` of the scheme of structure constants and the one
attached to its image under the conjugation action of a unit-fixing matrix are isomorphic as
schemes over the base. -/
theorem exists_iso_pullback_universalCoverHom_conjugation {T : Scheme.{u}} [IsAffine T]
    (laws : ConjugationPreservesAlgebraLaws.{u} d) (g : UnitFixingMatrix Γ(T, ⊤) d)
    (y : T ⟶ scheme.{u} d) :
    ∃ e : pullback (universalCoverHom.{u} d) y ≅
        pullback (universalCoverHom.{u} d) (conjugationOnPoints laws T g y),
      e.hom ≫ pullback.snd (universalCoverHom.{u} d) (conjugationOnPoints laws T g y) =
        pullback.snd (universalCoverHom.{u} d) y := by
  obtain ⟨p₁, sq₁⟩ := exists_isPullback_specCover_universalCoverHom (d := d) y
  obtain ⟨p₂, sq₂⟩ :=
    exists_isPullback_specCover_universalCoverHom (d := d) (conjugationOnPoints laws T g y)
  set c := conjugationSpecIso laws g y with hc
  refine ⟨sq₁.flip.isoPullback.symm ≪≫ (Over.forget _).mapIso c ≪≫ sq₂.flip.isoPullback, ?_⟩
  have hw : (c.hom).left ≫
      (specCover ((representation.{u} d).equiv T (conjugationOnPoints laws T g y))).hom =
      (specCover ((representation.{u} d).equiv T y)).hom := Over.w c.hom
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Over.forget_map, Category.assoc]
  rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd,
    ← Category.assoc, hw]

end AlgebraicGeometry.FiniteFreeAlgebra

end
