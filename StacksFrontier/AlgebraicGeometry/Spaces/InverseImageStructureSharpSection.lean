module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
import StacksCore.Tactic.StacksAttribute

/-!
# A left inverse splits the inverse-image form of the structure map

Let `i : Z ⟶ X` be a morphism of algebraic spaces over a scheme `S` admitting a left inverse
`g : X ⟶ Z`, that is `i ≫ g = 𝟙 Z`.  This file produces a homomorphism of sheaves of
commutative rings
```
  s : 𝒪_Z ⟶ i⁻¹𝒪_X
```
on the small étale site of `Z` with `s ≫ i♯ = 𝟙`, where `i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z` is the
inverse-image form `AlgebraicGeometry.Space.structureSharpInverseImage` of the structure map of
`i`.

## Main results

* `AlgebraicGeometry.Space.isIso_structureSharpInverseImage_id`: the inverse-image form of the
  structure map of an identity is an isomorphism.
* `AlgebraicGeometry.Space.inverseImageStructureSharpSection` and
  `AlgebraicGeometry.Space.inverseImageStructureSharpSection_comp`: the section attached to a
  left inverse.
* `AlgebraicGeometry.Space.inverseImageStructureSharpSection_fixes`: the section fixes
  everything coming from the base along `g`.
* `AlgebraicGeometry.Space.directImageInverseImageStructureSharpSection_comp`: the direct image
  along `i` of the split surjection is a split surjection of sheaves of commutative rings on the
  small étale site of `X`.

## Implementation notes

The composition law of Stacks 03G8 in inverse-image form,
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage`,
factors the structure map of a composite through that of its first factor; at the composite `i ≫ g`
that is the map `(i ≫ g)⁻¹𝒪_Z ⟶ i⁻¹𝒪_X` written out of `i⁻¹(g♯)`. The left inverse makes the
composite an identity, and the structure map of an identity is invertible: its direct image is an
equivalence (`AlgebraicGeometry.Space.isEquivalence_smallEtaleDirectImage_id`) and its structure
map is invertible (`AlgebraicGeometry.Space.isIso_structureSharp_id`), which is what
`AlgebraicGeometry.RingedToposHom.isIso_fSharpInverseImage` asks for.

The invertibility of the `CommRingCat`-valued structure map of an identity is deduced from the
`RingCat`-valued one through `AlgebraicGeometry.Space.map_structureSharpCommRing`: the forgetful
functor on sheaves of commutative rings is fully faithful, so it reflects isomorphisms.  Nothing
here unfolds `AlgebraicGeometry.Space.structureSharpCommRing`, which is irreducible.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Identity

variable (X : AlgebraicSpaces B S hS)

/-- **The `CommRingCat`-valued structure map of an identity is invertible.**  Forgetting
commutativity it is `AlgebraicGeometry.Space.structureSharp` of the identity, which is
invertible by `AlgebraicGeometry.Space.isIso_structureSharp_id`, and the forgetful functor on
sheaves of commutative rings is fully faithful. -/
instance isIso_structureSharpCommRing_id :
    IsIso (structureSharpCommRing B S hS (𝟙 X)) := by
  have : IsIso ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).map (structureSharpCommRing B S hS (𝟙 X))) := by
    rw [map_structureSharpCommRing B S hS (𝟙 X)]
    exact isIso_structureSharp_id B S hS X
  exact (Stacks.Sheaves.ToposPullback.fullyFaithfulForgetCommRingSheaf.{u, u, u + 1}
    (SmallEtale.topology B S hS X.1)).isIso_of_isIso_map _

/-- The structure map of the morphism of small étale ringed topoi of an identity is
invertible, in the spelling `AlgebraicGeometry.RingedToposHom.isIso_fSharpInverseImage`
consumes. -/
instance isIso_fSharp_smallEtaleRingedToposHom_id :
    IsIso (smallEtaleRingedToposHom B S hS (𝟙 X)).fSharp :=
  isIso_structureSharpCommRing_id B S hS X

/-- The direct image of the morphism of small étale topoi of an identity is an equivalence. -/
instance isEquivalence_smallEtaleRingedToposHom_id_pushforward :
    (smallEtaleRingedToposHom B S hS (𝟙 X)).toToposHom.pushforward.IsEquivalence :=
  isEquivalence_smallEtaleDirectImage_id B S hS X

/-- **The inverse-image form of the structure map of an identity is an isomorphism.** -/
instance isIso_structureSharpInverseImage_id :
    IsIso (structureSharpInverseImage B S hS (𝟙 X)) :=
  RingedToposHom.isIso_fSharpInverseImage (smallEtaleRingedToposHom B S hS (𝟙 X))

end Identity

section Section

variable {Z X : AlgebraicSpaces B S hS}

/-- The inverse-image form of the structure map of a morphism with a left inverse is an
isomorphism at the composite, which is an identity. -/
theorem isIso_structureSharpInverseImage_of_comp_eq_id (i : Z ⟶ X) (g : X ⟶ Z)
    (hg : i ≫ g = 𝟙 Z) : IsIso (structureSharpInverseImage B S hS (i ≫ g)) := by
  rw [hg]
  infer_instance

/-- The comparison of the iterated inverse image of sheaves of commutative rings with the
inverse image along a composite, at the structure sheaf: `i⁻¹(g⁻¹𝒪_Z) ≅ (i ≫ g)⁻¹𝒪_Z`.  This is
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageRingIso` of Stacks 03G8 read
at one object. -/
noncomputable abbrev inverseImageStructureCompIso (i : Z ⟶ X) (g : X ⟶ Z) :
    (smallEtaleInverseImageRing B S hS i).obj (inverseImageStructureSheaf B S hS g) ≅
      inverseImageStructureSheaf B S hS (i ≫ g) :=
  (smallEtaleRingedToposHom_compInverseImageRingIso B S hS i g).app
    (smallEtaleRingedTopos B S hS Z).O

/-- The inverse image along `i` of the structure map of `g`, read as a map out of the inverse
image along the composite `i ≫ g` through the comparison of Stacks 03G8. -/
noncomputable abbrev inverseImageStructureSharpFactor (i : Z ⟶ X) (g : X ⟶ Z) :
    inverseImageStructureSheaf B S hS (i ≫ g) ⟶ inverseImageStructureSheaf B S hS i :=
  (inverseImageStructureCompIso B S hS i g).inv ≫
    (smallEtaleInverseImageRing B S hS i).map (structureSharpInverseImage B S hS g)

/-- **The factorization of Stacks 03G8**: the factor above, followed by `i♯`, is the structure
map of the composite.  This is
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage`
with the comparison moved to the other side. -/
theorem inverseImageStructureSharpFactor_comp (i : Z ⟶ X) (g : X ⟶ Z) :
    inverseImageStructureSharpFactor B S hS i g ≫ structureSharpInverseImage B S hS i =
      structureSharpInverseImage B S hS (i ≫ g) :=
  Eq.trans (Category.assoc _ _ _)
    (Eq.trans
      (congrArg (fun t => (inverseImageStructureCompIso B S hS i g).inv ≫ t)
        (smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage B S hS i g).symm)
      (Eq.trans (Category.assoc _ _ _).symm
        (Eq.trans
          (congrArg (fun t => t ≫ structureSharpInverseImage B S hS (i ≫ g))
            (inverseImageStructureCompIso B S hS i g).inv_hom_id)
          (Category.id_comp _))))

/-- **A left inverse splits the inverse-image form of the structure map.**  For `i : Z ⟶ X` with
`i ≫ g = 𝟙 Z`, this is a homomorphism of sheaves of commutative rings `𝒪_Z ⟶ i⁻¹𝒪_X` which is a
section of `i♯ : i⁻¹𝒪_X ⟶ 𝒪_Z`.

It is written out of the inverse image along `i` of the structure map of `g`, and not merely
obtained from the existence statement
`AlgebraicGeometry.Space.exists_structureSharpInverseImage_comp_factorization`: a consumer needs
not only that it is a section but what it does to sections coming from `g`, which is
`AlgebraicGeometry.Space.inverseImageStructureSharpSection_fixes` below, and that is visible
only in the written-out form. -/
noncomputable def inverseImageStructureSharpSection (i : Z ⟶ X) (g : X ⟶ Z)
    (hg : i ≫ g = 𝟙 Z) :
    (smallEtaleRingedTopos B S hS Z).O ⟶ inverseImageStructureSheaf B S hS i :=
  haveI := isIso_structureSharpInverseImage_of_comp_eq_id B S hS i g hg
  inv (structureSharpInverseImage B S hS (i ≫ g)) ≫
    inverseImageStructureSharpFactor B S hS i g

/-- **`AlgebraicGeometry.Space.inverseImageStructureSharpSection` is a section of `i♯`.** -/
theorem inverseImageStructureSharpSection_comp (i : Z ⟶ X) (g : X ⟶ Z) (hg : i ≫ g = 𝟙 Z) :
    inverseImageStructureSharpSection B S hS i g hg ≫ structureSharpInverseImage B S hS i =
      𝟙 (smallEtaleRingedTopos B S hS Z).O := by
  have := isIso_structureSharpInverseImage_of_comp_eq_id B S hS i g hg
  exact Eq.trans (Category.assoc _ _ _)
    (Eq.trans
      (congrArg (fun t => inv (structureSharpInverseImage B S hS (i ≫ g)) ≫ t)
        (inverseImageStructureSharpFactor_comp B S hS i g))
      (IsIso.inv_hom_id _))

/-- **The section fixes everything coming from the base along `g`.**  The inverse image along
`i` of the structure map of `g`, followed by `i♯` and then by the section, is itself.

This is the one property beyond being a section that the derivation of Stacks 02HP needs: it is
what makes that derivation a `Z`-derivation, `Z` being the base through `g`.  It holds because
the section is written out of `i⁻¹(g♯)`, so the two comparison isomorphisms cancel. -/
theorem inverseImageStructureSharpSection_fixes (i : Z ⟶ X) (g : X ⟶ Z) (hg : i ≫ g = 𝟙 Z) :
    (smallEtaleInverseImageRing B S hS i).map (structureSharpInverseImage B S hS g) ≫
        structureSharpInverseImage B S hS i ≫
          inverseImageStructureSharpSection B S hS i g hg =
      (smallEtaleInverseImageRing B S hS i).map (structureSharpInverseImage B S hS g) := by
  have := isIso_structureSharpInverseImage_of_comp_eq_id B S hS i g hg
  have key : inverseImageStructureSharpFactor B S hS i g ≫
      (structureSharpInverseImage B S hS i ≫
        inverseImageStructureSharpSection B S hS i g hg) =
      inverseImageStructureSharpFactor B S hS i g := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun t => t ≫ inverseImageStructureSharpSection B S hS i g hg)
      (inverseImageStructureSharpFactor_comp B S hS i g)) ?_
    exact IsIso.hom_inv_id_assoc _ _
  exact (Iso.cancel_iso_inv_left (inverseImageStructureCompIso B S hS i g) _ _).mp
    ((Category.assoc _ _ _).symm.trans key)


/-! ### The split surjection on the small étale site of the ambient space -/

/-- The direct image along `i` of the inverse-image structure sheaf, `i_*i⁻¹𝒪_X`.  This is the
sheaf of commutative rings on the small étale site of `X` in which a section of `𝒪_X` and its
pullback along `g ≫ i` can be compared: the unit of `i⁻¹ ⊣ i_*` maps `𝒪_X` into it, and so does
the structure map of `g ≫ i`. -/
noncomputable abbrev directImageInverseImageStructureSheaf (i : Z ⟶ X) :
    Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u} :=
  (Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
    (smallEtaleRingedToposHom B S hS i).toToposHom).obj (inverseImageStructureSheaf B S hS i)

/-- The direct image along `i` of the inverse-image form of the structure map of `i`,
`i_*i⁻¹𝒪_X ⟶ i_*𝒪_Z`. -/
noncomputable abbrev directImageStructureSharpInverseImage (i : Z ⟶ X) :
    directImageInverseImageStructureSheaf B S hS i ⟶
      (Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS i).toToposHom).obj
          (smallEtaleRingedTopos B S hS Z).O :=
  (Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
    (smallEtaleRingedToposHom B S hS i).toToposHom).map (structureSharpInverseImage B S hS i)

/-- The direct image along `i` of the section of
`AlgebraicGeometry.Space.inverseImageStructureSharpSection`. -/
noncomputable abbrev directImageInverseImageStructureSharpSection (i : Z ⟶ X) (g : X ⟶ Z)
    (hg : i ≫ g = 𝟙 Z) :
    (Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS i).toToposHom).obj
          (smallEtaleRingedTopos B S hS Z).O ⟶
      directImageInverseImageStructureSheaf B S hS i :=
  (Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
    (smallEtaleRingedToposHom B S hS i).toToposHom).map
      (inverseImageStructureSharpSection B S hS i g hg)

/-- **The direct image of the split surjection is a split surjection.**  On the small étale site
of `X` the comparison `i_*i⁻¹𝒪_X ⟶ i_*𝒪_Z` is split by the direct image of the section, by
functoriality of the direct image.

This is the datum `PresheafOfModules.splitSurjectionDerivation` consumes, and it is the reason
the derivation of Stacks 02HP can be written on the site of `X` at all: on `𝒪_X` itself the
comparison with `(g ≫ i)^♯` is not split, and is not even a pair of parallel maps. -/
theorem directImageInverseImageStructureSharpSection_comp (i : Z ⟶ X) (g : X ⟶ Z)
    (hg : i ≫ g = 𝟙 Z) :
    directImageInverseImageStructureSharpSection B S hS i g hg ≫
        directImageStructureSharpInverseImage B S hS i =
      𝟙 ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS i).toToposHom).obj
          (smallEtaleRingedTopos B S hS Z).O) :=
  Eq.trans
    ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
      (smallEtaleRingedToposHom B S hS i).toToposHom).map_comp _ _).symm
    (Eq.trans
      (congrArg
        (Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS i).toToposHom).map
        (inverseImageStructureSharpSection_comp B S hS i g hg))
      (CategoryTheory.Functor.map_id
        (Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS i).toToposHom)
        (smallEtaleRingedTopos B S hS Z).O))

end Section

end AlgebraicGeometry.Space

end
