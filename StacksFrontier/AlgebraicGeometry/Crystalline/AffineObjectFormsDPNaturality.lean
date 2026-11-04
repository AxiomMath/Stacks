module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineObjectDifferentialFormsNaturality
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Functoriality

/-!
# The naturality of [Stacks, Tag 07J0] in every degree, as a divided power morphism

`Crystalline.GlobalCrystallineSituation.affineCrysDifferentialFormsIso_naturality` of
`AffineObjectDifferentialFormsNaturality.lean` states the naturality of the affine identification
of [Stacks, Tag 07J0] with the right-hand vertical spelled
`Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsMapₛₗ`, the map on divided power
differentials that `Crystalline.dpMap` produces out of a commuting square of rings.  Every
consumer of that square in the proof of [Stacks, Tag 07LF] needs it with the vertical spelled
`Crystalline.mapDifferentialFormsOfDPMorphism` instead — the functoriality of
`Crystalline.dividedPowerDifferentialForms` in a divided power morphism of `Γ(S, ⊤)`-algebras,
which is what `Crystalline.tensorFormsLevelComposite_naturality` asks for in its hypothesis on
the left vertical.  **This file is that restatement**, for `V = ⊤` on the divided power base.

The two verticals are the same map, and the file proves it: both are determined by their values
on the universal divided power differentials `d b`, where both give `d (k b)`, and
`Crystalline.differentials_hom_ext` turns that into an equality of semilinear maps.  The degree-`i`
statement is then the degree-one one carried up the exterior powers by `congrArg`, both sides
being `ExteriorAlgebra.powMapₛₗ` of their degree-one map.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.crysTopAlgebra` — the `Γ(S, ⊤)`-algebra structure on the
  global sections of the ambient scheme of an object of `CRIS(X/S)`, through
  `...affineBaseAppLE` at `V = ⊤`.  It is supplied positionally at every use, for the reason the
  implementation notes of `AffineObjectDifferentialForms.lean` record.
* `Crystalline.GlobalCrystallineSituation.crysSectionsRestrictionAlgHom` — the restriction map on
  global sections along a morphism of `CRIS(X/S)`, as a morphism of `Γ(S, ⊤)`-algebras.  Its
  compatibility with the two structure maps is `...affineBaseAppLE_fac`.

## Main results

* `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsMapₛₗ_eq` — **the degree-one
  verticals agree**: the map of `Crystalline.dpMap` is the map of
  `Crystalline.mapDifferentialsOfDPMorphismₛₗ` at the restriction algebra map.
* `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialFormsIso_naturality_dp` —
  **[Stacks, Tag 07J0] in every degree is natural, with the vertical spelled
  `Crystalline.mapDifferentialFormsOfDPMorphism`.**

## Implementation notes

**Every statement supplies the two algebra instances positionally.**  Left to synthesis they are
not found: `Crystalline.dividedPowerDifferentialForms` reaches the instance problem through the
ideal of `Crystalline.GlobalCrystallineSituation.crysDividedPowers`, in the unfolded spelling of
the sections of a scheme's structure sheaf, while the instance given by the structure morphism is
keyed at the folded one.  Supplying it positionally asks for a definitional check instead of a
search, and that check is immediate.

The affine open `V` of the divided power base is `⊤` throughout, and its two factorization
hypotheses are `le_rfl` because `AlgebraicGeometry.Scheme.Hom.preimage_top` is `rfl`.  The
affineness of `V` is carried as a hypothesis `hV` rather than discharged by
`AlgebraicGeometry.isAffineOpen_top`, so that no `[IsAffine S.S.scheme]` instance is needed here
and the consumer supplies the same proof term it uses elsewhere.

## What is and is not proved

**No tag attribute is placed and [Stacks, Tag 07LF] is not proved.**  What is proved is one
restatement of the naturality of [Stacks, Tag 07J0]: the two spellings of the transition map on
divided power differential forms of an affine object of `CRIS(X/S)` relative to `Γ(S, ⊤)` are the
same map, and the identification of [Stacks, Tag 07J0] commutes with them.  No hypothesis beyond
the two affineness instances on the ambient schemes and the affineness of `⊤ ⊆ S` is carried, and
nothing is assumed of the morphism `k`.

## References

* [Stacks Project, Tag 07J0](https://stacks.math.columbia.edu/tag/07J0)
* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
* [Stacks Project, Lemma 60.21.1, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u}) {A B : Thickening S} (k : A ⟶ B)

/-- **The `Γ(S, ⊤)`-algebra structure on the global sections of the ambient scheme** of an object
of `CRIS(X/S)`, through `...affineBaseAppLE` at `V = ⊤`.  This is the instance
`...affineCrysDifferentialForms_eq` states its conclusion under; it is an `abbrev` so that
supplying it positionally costs one definitional unfolding. -/
abbrev crysTopAlgebra (A : Thickening S) :
    Algebra (Γ(S.S.scheme, ⊤) : Type u) (Γ(A.thickening.target.scheme, ⊤) : Type u) :=
  (affineBaseAppLE S A (V := ⊤) le_rfl).hom.toAlgebra

/-- **The restriction map on global sections along a morphism of `CRIS(X/S)`, as a morphism of
`Γ(S, ⊤)`-algebras.**  The underlying ring map is the map on global sections of the morphism of
ambient schemes; that it commutes with the two structure maps `Γ(S, ⊤) ⟶ Γ(T, 𝒪_T)` is
`...affineBaseAppLE_fac` at `V = ⊤`, read on an element.

This is the divided power morphism `u` of `Crystalline.tensorFormsLevelComposite_naturality` at
the objects of `...SmallSite.wholeSpaceSystem`; its divided power half is
`AlgebraicGeometry.DividedPowerScheme.Hom.compatible` of the morphism of thickenings. -/
def crysSectionsRestrictionAlgHom :
    @AlgHom (Γ(S.S.scheme, ⊤) : Type u) (Γ(B.thickening.target.scheme, ⊤) : Type u)
      (Γ(A.thickening.target.scheme, ⊤) : Type u) _ _ _
      (crysTopAlgebra S B) (crysTopAlgebra S A) :=
  letI := crysTopAlgebra S B
  letI := crysTopAlgebra S A
  { k.targetHom.hom.appTop.hom with
    commutes' := fun a ↦ congrArg (fun q ↦ CommRingCat.Hom.hom q a)
      (affineBaseAppLE_fac S k (V := ⊤) le_rfl le_rfl).symm }

/-- **The two spellings of the degree-one vertical agree.**  The map
`Ω¹_{Γ(T',𝒪)/Γ(S,⊤),δ'} ⟶ Ω¹_{Γ(T,𝒪)/Γ(S,⊤),δ}` of `...affineCrysDifferentialsMapₛₗ`, built by
`Crystalline.dpMap` out of the commuting square of rings, is the functoriality
`Crystalline.mapDifferentialsOfDPMorphismₛₗ` of the divided power differentials at
`crysSectionsRestrictionAlgHom`.

Both are additive, both are semilinear over the map on sections, and both carry the universal
divided power differential `d b` to `d (k b)` — by `...affineCrysDifferentialsMap_dpd` and by
`Crystalline.mapDifferentialsOfDPMorphism_d` — so `Crystalline.differentials_hom_ext` identifies
them.  **No tag attribute is placed.** -/
theorem affineCrysDifferentialsMapₛₗ_eq :
    affineCrysDifferentialsMapₛₗ S k (V := ⊤) le_rfl le_rfl =
      @_root_.Crystalline.mapDifferentialsOfDPMorphismₛₗ (Γ(S.S.scheme, ⊤) : Type u)
        (Γ(B.thickening.target.scheme, ⊤) : Type u) _ _ (crysTopAlgebra S B) _
        (crysDividedPowers S B) (Γ(A.thickening.target.scheme, ⊤) : Type u) _
        (crysTopAlgebra S A) _ (crysDividedPowers S A)
        (crysSectionsRestrictionAlgHom S k) (k.targetHom.compatible ⊤) := by
  refine LinearMap.ext fun x ↦ DFunLike.congr_fun
    (@_root_.Crystalline.differentials_hom_ext (Γ(S.S.scheme, ⊤) : Type u)
      (Γ(B.thickening.target.scheme, ⊤) : Type u) _ _ (crysTopAlgebra S B) _
      (crysDividedPowers S B) (Γ(A.thickening.target.scheme, ⊤) : Type u) _ _ _ _
      k.targetHom.hom.appTop.hom
      (affineCrysDifferentialsMapₛₗ S k (V := ⊤) le_rfl le_rfl).toAddMonoidHom
      (@_root_.Crystalline.mapDifferentialsOfDPMorphismₛₗ (Γ(S.S.scheme, ⊤) : Type u)
        (Γ(B.thickening.target.scheme, ⊤) : Type u) _ _ (crysTopAlgebra S B) _
        (crysDividedPowers S B) (Γ(A.thickening.target.scheme, ⊤) : Type u) _
        (crysTopAlgebra S A) _ (crysDividedPowers S A)
        (crysSectionsRestrictionAlgHom S k) (k.targetHom.compatible ⊤)).toAddMonoidHom
      (fun b y ↦ (affineCrysDifferentialsMapₛₗ S k (V := ⊤) le_rfl le_rfl).map_smul' b y)
      (fun b y ↦ (@_root_.Crystalline.mapDifferentialsOfDPMorphismₛₗ
        (Γ(S.S.scheme, ⊤) : Type u) (Γ(B.thickening.target.scheme, ⊤) : Type u) _ _
        (crysTopAlgebra S B) _ (crysDividedPowers S B)
        (Γ(A.thickening.target.scheme, ⊤) : Type u) _ (crysTopAlgebra S A) _
        (crysDividedPowers S A) (crysSectionsRestrictionAlgHom S k)
        (k.targetHom.compatible ⊤)).map_smul' b y)
      fun b ↦ ?_) x
  exact (affineCrysDifferentialsMap_dpd S k (V := ⊤) le_rfl le_rfl b).trans
    (@_root_.Crystalline.mapDifferentialsOfDPMorphism_d (Γ(S.S.scheme, ⊤) : Type u)
      (Γ(B.thickening.target.scheme, ⊤) : Type u) _ _ (crysTopAlgebra S B) _
      (crysDividedPowers S B) (Γ(A.thickening.target.scheme, ⊤) : Type u) _
      (crysTopAlgebra S A) _ (crysDividedPowers S A) (crysSectionsRestrictionAlgHom S k)
      (k.targetHom.compatible ⊤) b).symm

/-- **[Stacks, Tag 07J0] in every degree is natural in the object, with the vertical spelled as a
divided power morphism.**

For a morphism `k : (U, T, δ) ⟶ (U', T', δ')` of `CRIS(X/S)` between objects with affine ambient
schemes, restricting a section of `Ω^i_{X/S}` and then identifying it with a divided power
differential form is identifying it and then applying
`Crystalline.mapDifferentialFormsOfDPMorphism` at the restriction map on sections.

This is `...affineCrysDifferentialFormsIso_naturality` with its right-hand vertical rewritten by
`affineCrysDifferentialsMapₛₗ_eq`: both verticals are `ExteriorAlgebra.powMapₛₗ` of their
degree-one map, so the rewriting is one `congrArg`.  This is the shape the hypothesis `hPhi` of
`Crystalline.tensorFormsLevelComposite_naturality` consumes.  **No tag attribute is placed.** -/
theorem affineCrysDifferentialFormsIso_naturality_dp
    [IsAffine A.thickening.target.scheme] [IsAffine B.thickening.target.scheme]
    (hV : IsAffineOpen (⊤ : S.S.scheme.Opens)) (i : ℕ)
    (z : ((crysDifferentialForms S i).obj (op B) : Type u)) :
    affineCrysDifferentialFormsIso S A (V := ⊤) le_rfl hV i
        ((crysDifferentialForms S i).map k.op z) =
      @_root_.Crystalline.mapDifferentialFormsOfDPMorphism (Γ(S.S.scheme, ⊤) : Type u)
        (Γ(B.thickening.target.scheme, ⊤) : Type u) _ _ (crysTopAlgebra S B) _
        (crysDividedPowers S B) (Γ(A.thickening.target.scheme, ⊤) : Type u) _
        (crysTopAlgebra S A) _ (crysDividedPowers S A)
        (crysSectionsRestrictionAlgHom S k) (k.targetHom.compatible ⊤) i
        (affineCrysDifferentialFormsIso S B (V := ⊤) le_rfl hV i z) :=
  (affineCrysDifferentialFormsIso_naturality S k le_rfl le_rfl hV i z).trans
    (congrArg (fun G ↦ ExteriorAlgebra.powMapₛₗ i k.targetHom.hom.appTop.hom G
        (affineCrysDifferentialFormsIso S B (V := ⊤) le_rfl hV i z))
      (affineCrysDifferentialsMapₛₗ_eq S k))

end Crystalline.GlobalCrystallineSituation

end

end
