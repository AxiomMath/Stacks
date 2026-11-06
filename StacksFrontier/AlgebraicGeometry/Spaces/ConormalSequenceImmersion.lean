module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealSheafCartesianSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceKernelIdeal

/-!
# The conormal sequence of a pair of immersions of algebraic spaces

Let `S` be a scheme and let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions of algebraic spaces over
`S`.  [Stacks Project, Tag 06BD] asserts that there is a canonical exact sequence of
`𝒪_Z`-modules

`i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0`

whose maps come from [Stacks Project, Tag 04CP].  This file proves it, with `𝒞` the conormal
module of an immersion of Stacks 04CN, `AlgebraicGeometry.Space.conormalModuleOfImmersion`: the
inverse image along the closed factorisation `Z ⟶ X ∖ ∂Z` of Stacks 04CE of the ideal sheaf of
its image.

## The maps

Stacks proves 04CP by first shrinking the two ambient spaces to opens in which the immersions are
closed, and then pulling back the map `g^{-1}𝓘' ⟶ 𝓘` of ideal sheaves.  The maps here are built
the same way, with one fixed choice of open: the complement `U = X ∖ ∂Y` of the boundary of `Y`,
in which `j` factors as a closed immersion `c : Y ⟶ U` followed by the inclusion `ι : U ⟶ X`.

* The first map is `AlgebraicGeometry.Space.kernelConormalSequenceFirstMap i c`, the map of
  Stacks 04CP for the square with `f = i` and `g = 𝟙_U`, and
* the second map is `AlgebraicGeometry.Space.kernelConormalSequenceSecondMap i c`, the map of
  Stacks 04CP for the square with `f = 𝟙_Z` and `g = c`,

both in the form `f^*𝒞 = f^*Ker(f^♯)` of the conormal module of a morphism; they are read on the
conormal modules of Stacks 04CN through canonical identifications:

* `𝒞_{Y/X}` *is* `c^*Ker(c^♯)`, since `c` is the closed factorisation of `j`
  (`AlgebraicGeometry.Space.conormalModuleOfImmersion_eq_kernelIdealModule`);
* `𝒞_{Z/X}`, formed in `X ∖ ∂Z`, and `(i ≫ c)^*Ker((i ≫ c)^♯)`, formed in `X ∖ ∂Y`, are both
  identified with the conormal module formed in `X` itself by Stacks 09RR for the open immersions
  `X ∖ ∂Z ⟶ X` and `X ∖ ∂Y ⟶ X` (`AlgebraicGeometry.Space.conormalAlgebraPieceIsoOfEtaleMono`);
* `𝒞_{Z/Y}`, formed in `Y ∖ ∂Z`, is identified with `i^*Ker(i^♯)`, formed in `Y`, in the same way.

These are the identifications that the replacement of the ambient spaces by opens performs in the
source's proof of Stacks 04CP.

## The proof

The source's proof localizes on an étale chart of `X` and quotes the case of schemes,
Stacks 062S.  This development has no comparison between modules on the small étale site of a
scheme and quasi-coherent modules on its Zariski site at that level, so the exactness is proved
globally instead: by `AlgebraicGeometry.Space.kernelConormalSequenceShortComplex_exact` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceKernelIdeal.lean` the sequence
`i^*c^*Ker(c^♯) ⟶ (i ≫ c)^*Ker((i ≫ c)^♯) ⟶ i^*Ker(i^♯) ⟶ 0` is exact because `c` is a closed
immersion, and the sequence of the statement is isomorphic to it.

## Main results

* `AlgebraicGeometry.Space.conormalSequenceImmersion_exact`: **[Stacks Project, Tag 06BD]**, the
  whole statement — the two maps compose to zero, the sequence is exact at `𝒞_{Z/X}`, and the
  second map is surjective (an epimorphism of `𝒪_Z`-modules).
* `AlgebraicGeometry.Space.conormalAlgebraPieceIsoOfEtaleMono`: the pieces of the conormal algebra
  of `k ≫ ι` and of `k` agree for an étale monomorphism `ι`, by Stacks 09RR.

## References

* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 09RR](https://stacks.math.columbia.edu/tag/09RR)
* [Stacks Project, Tag 062S](https://stacks.math.columbia.edu/tag/062S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Independence of the ambient open -/

section OpenAmbient

variable {Z U X : AlgebraicSpaces B S hS}

/-- **The conormal algebra does not see an étale monomorphism of the ambient space.**  For
`k : Z ⟶ U`, an étale monomorphism `ι : U ⟶ X` — for instance the inclusion of an open subspace —
and `m = k ≫ ι`, the degree-`n` pieces of the conormal algebras of `m` and of `k` are canonically
isomorphic: the square `𝟙 ≫ m = k ≫ ι` is cartesian because `ι` is a monomorphism, so
Stacks 09RR applies to it, and the inverse image along the identity of `Z` is the identity. -/
noncomputable def conormalAlgebraPieceIsoOfEtaleMono (k : Z ⟶ U) (ι : U ⟶ X) (m : Z ⟶ X)
    (hkm : k ≫ ι = m) [Mono ι] (hι : IsEtale B S hS ι.hom) (n : ℤ) :
    (conormalAlgebra B S hS m).piece n ≅ (conormalAlgebra B S hS k).piece n :=
  ((modulePullbackIdIso B S hS Z).app ((conormalAlgebra B S hS m).piece n)).symm ≪≫
    conormalAlgebraEtaleRestrictionPieceIso B S hS (𝟙 Z) k m ι
      (IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, hkm]⟩) hι n

end OpenAmbient

/-! ### The inclusion of the complement of the boundary of an immersion -/

section Immersion

attribute [local instance] pointTopology

variable {Z₀ X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 04CE**, for the closed factorisation read as a morphism of algebraic spaces. -/
theorem isClosedImmersion_immersionClosedFactorization (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    IsClosedImmersion B S hS (immersionClosedFactorization B S hS hX hZ i hi).hom :=
  isClosedImmersion_boundaryComplementLift B S hS hX hZ i hi

/-- The conormal module of an immersion is the inverse image along its closed factorisation of
the kernel ideal sheaf of that factorisation. -/
theorem conormalModuleOfImmersion_eq_kernelIdealModule (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    conormalModuleOfImmersion B S hS hX hZ i hi =
      (modulePullback B S hS (immersionClosedFactorization B S hS hX hZ i hi)).obj
        (kerIdealOneModule B S hS (immersionClosedFactorization B S hS hX hZ i hi)) :=
  conormalModuleOfImmersion_eq_conormalAlgebraOfImmersion_piece_one B S hS hX hZ i hi

end Immersion

/-! ### The conormal sequence of a pair of immersions -/

section Sequence

attribute [local instance] pointTopology

variable {Z₀ Y₀ X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X₀)
  (hY : IsAlgebraicSpace B S hS Y₀) (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ Y₀) (j : Y₀ ⟶ X₀)
  (hi : IsImmersion B S hS i) (hj : IsImmersion B S hS j)

/-- `i` followed by the closed factorisation of `j` and the inclusion of `X ∖ ∂Y` is `i ≫ j`. -/
theorem homMk_comp_immersionClosedFactorization_comp_immersionAmbientι :
    ((ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y₀, hY⟩) ≫
        immersionClosedFactorization B S hS hX hY j hj) ≫
      immersionAmbientι B S hS
        (ObjectProperty.homMk j : (⟨Y₀, hY⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X₀, hX⟩) hj =
      (ObjectProperty.homMk (i ≫ j) : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X₀, hX⟩) := by
  rw [Category.assoc]
  exact congrArg (_ ≫ ·) (immersionClosedFactorization_comp_immersionAmbientι B S hS
    (ObjectProperty.homMk j : (⟨Y₀, hY⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X₀, hX⟩) hj)

/-- The identification of the first term: `i^*𝒞_{Y/X}`, for the conormal module of the immersion
`j` of Stacks 04CN, is `i^*c^*Ker(c^♯)` for the closed factorisation `c : Y ⟶ X ∖ ∂Y` of `j`. -/
noncomputable def conormalSequenceImmersionFirstTermIso :
    (modulePullback B S hS (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨Y₀, hY⟩)).obj (conormalModuleOfImmersion B S hS hX hY j hj) ≅
      (modulePullback B S hS (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨Y₀, hY⟩)).obj
        ((modulePullback B S hS (immersionClosedFactorization B S hS hX hY j hj)).obj
          (kerIdealOneModule B S hS (immersionClosedFactorization B S hS hX hY j hj))) :=
  (modulePullback B S hS (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨Y₀, hY⟩)).mapIso
    (eqToIso (conormalModuleOfImmersion_eq_kernelIdealModule B S hS hX hY j hj))

/-- The identification of the middle term: the conormal module of the immersion `i ≫ j`, formed
in `X ∖ ∂Z`, is the kernel-ideal conormal module of `Z` in `X ∖ ∂Y` along
`i ≫ c`, both being identified with the one formed in `X` by Stacks 09RR. -/
noncomputable def conormalSequenceImmersionMiddleTermIso :
    conormalModuleOfImmersion B S hS hX hZ (i ≫ j) (isImmersion_comp B S hS i j hi hj) ≅
      (modulePullback B S hS ((ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨Y₀, hY⟩) ≫ immersionClosedFactorization B S hS hX hY j hj)).obj
        (kerIdealOneModule B S hS ((ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨Y₀, hY⟩) ≫ immersionClosedFactorization B S hS hX hY j hj)) :=
  eqToIso (conormalModuleOfImmersion_eq_kernelIdealModule B S hS hX hZ (i ≫ j)
      (isImmersion_comp B S hS i j hi hj)) ≪≫
    (eqToIso (conormalAlgebra_piece B S hS (immersionClosedFactorization B S hS hX hZ (i ≫ j)
      (isImmersion_comp B S hS i j hi hj)) 1)).symm ≪≫
    (conormalAlgebraPieceIsoOfEtaleMono B S hS _ _ _
      (immersionClosedFactorization_comp_immersionAmbientι B S hS
        (ObjectProperty.homMk (i ≫ j) : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X₀, hX⟩)
        (isImmersion_comp B S hS i j hi hj))
      (isEtale_immersionAmbientι B S hS
        (ObjectProperty.homMk (i ≫ j) : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X₀, hX⟩)
        (isImmersion_comp B S hS i j hi hj)) 1).symm ≪≫
    conormalAlgebraPieceIsoOfEtaleMono B S hS _ _ _
      (homMk_comp_immersionClosedFactorization_comp_immersionAmbientι B S hS hX hY hZ i j hj)
      (isEtale_immersionAmbientι B S hS
        (ObjectProperty.homMk j : (⟨Y₀, hY⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X₀, hX⟩) hj) 1 ≪≫
    eqToIso (conormalAlgebra_piece B S hS ((ObjectProperty.homMk i : (⟨Z₀, hZ⟩ :
      AlgebraicSpaces B S hS) ⟶ ⟨Y₀, hY⟩) ≫ immersionClosedFactorization B S hS hX hY j hj) 1)

/-- The identification of the last term: the conormal module of the immersion `i`, formed in
`Y ∖ ∂Z`, is the kernel-ideal conormal module `i^*Ker(i^♯)` formed in `Y`, by Stacks 09RR. -/
noncomputable def conormalSequenceImmersionLastTermIso :
    conormalModuleOfImmersion B S hS hY hZ i hi ≅
      (modulePullback B S hS (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨Y₀, hY⟩)).obj (kerIdealOneModule B S hS (ObjectProperty.homMk i :
          (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y₀, hY⟩)) :=
  eqToIso (conormalModuleOfImmersion_eq_kernelIdealModule B S hS hY hZ i hi) ≪≫
    (eqToIso (conormalAlgebra_piece B S hS
      (immersionClosedFactorization B S hS hY hZ i hi) 1)).symm ≪≫
    (conormalAlgebraPieceIsoOfEtaleMono B S hS _ _ _
      (immersionClosedFactorization_comp_immersionAmbientι B S hS
        (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y₀, hY⟩) hi)
      (isEtale_immersionAmbientι B S hS
        (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y₀, hY⟩) hi)
      1).symm ≪≫
    eqToIso (conormalAlgebra_piece B S hS (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ :
      AlgebraicSpaces B S hS) ⟶ ⟨Y₀, hY⟩) 1)

/-- **The first map `i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X}` of the conormal sequence of Stacks 06BD**: the map
of Stacks 04CP for the square with `f = i` and `g = 𝟙`, computed in the open `X ∖ ∂Y` in which `j`
is a closed immersion (`AlgebraicGeometry.Space.kernelConormalSequenceFirstMap`), and read on the
conormal modules of Stacks 04CN through the canonical identifications of the module
documentation. -/
noncomputable def conormalSequenceImmersionFirstMap :
    (modulePullback B S hS (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨Y₀, hY⟩)).obj (conormalModuleOfImmersion B S hS hX hY j hj) ⟶
      conormalModuleOfImmersion B S hS hX hZ (i ≫ j) (isImmersion_comp B S hS i j hi hj) :=
  (conormalSequenceImmersionFirstTermIso B S hS hX hY hZ i j hj).hom ≫
    kernelConormalSequenceFirstMap B S hS (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ :
      AlgebraicSpaces B S hS) ⟶ ⟨Y₀, hY⟩) (immersionClosedFactorization B S hS hX hY j hj) ≫
    (conormalSequenceImmersionMiddleTermIso B S hS hX hY hZ i j hi hj).inv

/-- **The second map `𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` of the conormal sequence of Stacks 06BD**: the map of
Stacks 04CP for the square with `f = 𝟙` and `g = j`, computed in the open `X ∖ ∂Y`
(`AlgebraicGeometry.Space.kernelConormalSequenceSecondMap`), and read on the conormal modules of
Stacks 04CN through the canonical identifications of the module documentation. -/
noncomputable def conormalSequenceImmersionSecondMap :
    conormalModuleOfImmersion B S hS hX hZ (i ≫ j) (isImmersion_comp B S hS i j hi hj) ⟶
      conormalModuleOfImmersion B S hS hY hZ i hi :=
  (conormalSequenceImmersionMiddleTermIso B S hS hX hY hZ i j hi hj).hom ≫
    kernelConormalSequenceSecondMap B S hS (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ :
      AlgebraicSpaces B S hS) ⟶ ⟨Y₀, hY⟩) (immersionClosedFactorization B S hS hX hY j hj) ≫
    (conormalSequenceImmersionLastTermIso B S hS hY hZ i hi).inv

/-- The two maps of the conormal sequence of Stacks 06BD compose to zero. -/
theorem conormalSequenceImmersionFirstMap_comp_secondMap :
    conormalSequenceImmersionFirstMap B S hS hX hY hZ i j hi hj ≫
      conormalSequenceImmersionSecondMap B S hS hX hY hZ i j hi hj = 0 := by
  rw [conormalSequenceImmersionFirstMap, conormalSequenceImmersionSecondMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% (kernelConormalSequenceFirstMap_comp_secondMap B S hS
    (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y₀, hY⟩)
    (immersionClosedFactorization B S hS hX hY j hj)), zero_comp, comp_zero]

/-- **[Stacks Project, Tag 06BD].**  Let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions of algebraic
spaces over `S`.  The canonical sequence of `𝒪_Z`-modules

`i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0`

of the conormal modules of Stacks 04CN, with the maps of Stacks 04CP
(`AlgebraicGeometry.Space.conormalSequenceImmersionFirstMap` and
`AlgebraicGeometry.Space.conormalSequenceImmersionSecondMap`), is exact: the two maps compose to
zero, the resulting short complex is exact, and the second map is an epimorphism.

It is isomorphic to the sequence `i^*c^*Ker(c^♯) ⟶ (i ≫ c)^*Ker((i ≫ c)^♯) ⟶ i^*Ker(i^♯) ⟶ 0` of
the closed factorisation `c : Y ⟶ X ∖ ∂Y` of `j`, which is exact by
`AlgebraicGeometry.Space.kernelConormalSequenceShortComplex_exact`. -/
@[stacks 06BD "the canonical exact sequence i^*C_{Y/X} → C_{Z/X} → C_{Z/Y} → 0 for immersions \
Z → Y → X of algebraic spaces, with the maps of Tag 04CP: the composite is zero, the sequence is \
exact at C_{Z/X}, and C_{Z/X} → C_{Z/Y} is an epimorphism"]
theorem conormalSequenceImmersion_exact :
    ∃ h : conormalSequenceImmersionFirstMap B S hS hX hY hZ i j hi hj ≫
        conormalSequenceImmersionSecondMap B S hS hX hY hZ i j hi hj = 0,
      (ShortComplex.mk _ _ h).Exact ∧
        Epi (conormalSequenceImmersionSecondMap B S hS hX hY hZ i j hi hj) := by
  refine ⟨conormalSequenceImmersionFirstMap_comp_secondMap B S hS hX hY hZ i j hi hj, ?_⟩
  obtain ⟨hexact, hepi⟩ := kernelConormalSequenceShortComplex_exact B S hS
    (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y₀, hY⟩)
    (immersionClosedFactorization B S hS hX hY j hj)
    (isClosedImmersion_immersionClosedFactorization B S hS hX hY j hj)
  let e : ShortComplex.mk _ _
      (conormalSequenceImmersionFirstMap_comp_secondMap B S hS hX hY hZ i j hi hj) ≅
      kernelConormalSequenceShortComplex B S hS (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ :
        AlgebraicSpaces B S hS) ⟶ ⟨Y₀, hY⟩) (immersionClosedFactorization B S hS hX hY j hj) :=
    ShortComplex.isoMk (conormalSequenceImmersionFirstTermIso B S hS hX hY hZ i j hj)
      (conormalSequenceImmersionMiddleTermIso B S hS hX hY hZ i j hi hj)
      (conormalSequenceImmersionLastTermIso B S hS hY hZ i hi)
      (by simp [conormalSequenceImmersionFirstMap])
      (by simp [conormalSequenceImmersionSecondMap])
  refine ⟨(ShortComplex.exact_iff_of_iso e).2 hexact, ?_⟩
  rw [conormalSequenceImmersionSecondMap]
  exact epi_comp' (IsIso.epi_of_iso _) (epi_comp' hepi (IsIso.epi_of_iso _))

end Sequence

end AlgebraicGeometry.Space
