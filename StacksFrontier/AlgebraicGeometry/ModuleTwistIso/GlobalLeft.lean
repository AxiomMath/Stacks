module

public import StacksFrontier.AlgebraicGeometry.ModuleTwistIso.SheafMultiplication

/-!
# Equations 01MO and 03GJ on all of `Proj S`, with the second index arbitrary

Let `S` be a graded ring, `X = Proj(S)` and `d` a natural number, and suppose the ratio locus
`W_d = ⋃ D₊(fg)`, `deg f = deg g + d`, is all of `X` — for instance because `X` is covered by the
standard opens of the homogeneous elements of degree `d`. Then the multiplication maps

`𝒪_X(dn) ⊗ 𝒪_X(m) ⟶ 𝒪_X(dn + m)` and `𝒪_X(dn) ⊗ ℱ(m) ⟶ ℱ(dn + m)`

of Equations 01MO and 03GJ are isomorphisms of sheaves on `X`, for every integer `m` and every
sheaf of `𝒪_X`-modules `ℱ`. Only the *first* index has to be a multiple of `d`: the twist in that
slot is the one trivialized by the ratios, and the second factor is carried along.

This is the global form of the statements of `../ModuleTwistIso/Multiplication.lean` and
`../ModuleTwistIso/SheafMultiplication.lean`, which are stated over an open of the ratio locus
and over a standard open respectively, and it is strictly stronger than
`Stacks.AlgebraicGeometry.TwistTensor.isIso_twistMultiplicationMap_of_ratioLocus_eq_top`, where
both indices are multiples of `d` because both twists are trivialized.

## Main results

* `Stacks.AlgebraicGeometry.ModuleTwistIso.isIso_twistMultiplicationMap_left_of_ratioLocus_eq_top`:
  **Equation 01MO globally**, `𝒪(dn) ⊗ 𝒪(m) ≅ 𝒪(dn + m)`.
* `Stacks.AlgebraicGeometry.ModuleTwistIso`
  `.isIso_twistSheafMultiplicationMap_left_of_ratioLocus_eq_top`: **Equation 03GJ globally**,
  `𝒪(dn) ⊗ ℱ(m) ≅ ℱ(dn + m)`.
* `Stacks.AlgebraicGeometry.ModuleTwistIso.twistSheafMultiplicationIsoLeft`: the second one as an
  isomorphism.
* `Stacks.AlgebraicGeometry.ModuleTwistIso.twistSheafIterateIso`: `(ℱ(m))(dn) ≅ ℱ(dn + m)`, the
  form a degree-`d` residue argument consumes, obtained from the previous one by the braiding of
  the tensor product.

## Implementation notes

The first statement is the stalk argument of
`Stacks.AlgebraicGeometry.TwistTensor.isIso_twistMultiplicationMap_of_ratioLocus_eq_top` run with
`Stacks.AlgebraicGeometry.ModuleTwistIso.isIso_stalkFunctor_map_twistMultiplication_left` in place
of its two-sided counterpart: a point of the ratio locus lies in some `D₊(fg)` with
`deg f = deg g + d`, the composite of the sheafification unit with the multiplication map is an
isomorphism of abelian presheaves there, and the unit cancels.

The second is the first one fed to
`AlgebraicGeometry.ProjectiveSpectrum.Proj`
`.isIso_twistSheafMultiplicationMap_of_isIso_twistMultiplicationMap`, the source's deduction of
the 03GJ clause from the 01MO clause, which is stated once where
`twistSheafMultiplicationMap` is defined and is shared with
`Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isIso_twistSheafMultiplicationMap`, the same
deduction at a degree-one cover.

`twistSheafIterateIso` is the only place the braiding is used for its own sake: Equation 03GJ has
the twist in the left slot, while a twist of a twist `(ℱ(m))(dn)` has it in the right one.

## References

* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 03GJ](https://stacks.math.columbia.edu/tag/03GJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

open Stacks.SheafOfModules.Invertible

universe u w

attribute [local implicit_reducible] CategoryTheory.sheafCompose TopCat.Sheaf
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Presheaf.IsSheaf

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **Equation 03GJ is an isomorphism as soon as Equation 01MO is**, for the same pair of
indices and every sheaf of `𝒪_X`-modules `ℱ`.

This is the source's own deduction of the 03GJ clause from the 01MO clause, and it is the whole
content of that deduction: by construction `twistSheafMultiplicationMap` is the composite of the
inverse associator, the braiding on `𝒪(n) ⊗ ℱ` tensored with `𝒪(m)`, the associator and
`𝟙_ℱ ⊗ (Equation 01MO)`. The first three factors are isomorphisms unconditionally and the fourth
is one because the tensor bifunctor maps a product of two isomorphisms to an isomorphism.

Every hypothesis under which Equation 01MO is a global isomorphism therefore gives the 03GJ
clause for free; the two such hypotheses in this library are a degree-one cover
(`Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isIso_twistSheafMultiplicationMap`) and the
ratio locus of `d` being everything with the first index a multiple of `d`
(`Stacks.AlgebraicGeometry.ModuleTwistIso`
`.isIso_twistSheafMultiplicationMap_left_of_ratioLocus_eq_top`). -/
public theorem isIso_twistSheafMultiplicationMap_of_isIso_twistMultiplicationMap
    (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮))) (n m : ℤ)
    (h : IsIso (twistMultiplicationMap 𝒮 n m)) :
    IsIso (twistSheafMultiplicationMap 𝒮 F n m) := by
  let O := (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj
  let J := Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮)
  let hO : Presheaf.IsSheaf J
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O) :=
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).property
  let L (k : ℤ) := twistingSheaf 𝒮 k
  let tensorProduct := Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮))
  show IsIso (_ ≫ _ ≫ _ ≫ _)
  have firstIso : IsIso (tensorProductAssociator O hO (L n) F (L m)).inv := inferInstance
  have secondIso : IsIso (tensorProduct.map
      (((tensorProductBraiding O hO (L n) F).hom, 𝟙 (L m)) : (_, _) ⟶ (_, _))) :=
    (tensorProduct.mapIso
      (Iso.prod (tensorProductBraiding O hO (L n) F) (Iso.refl (L m)))).isIso_hom
  have thirdIso := (tensorProductAssociator O hO F (L n) (L m)).isIso_hom
  have fourthIso : IsIso (tensorProduct.map
      ((𝟙 F, twistMultiplicationMap 𝒮 n m) : (_, _) ⟶ (_, _))) :=
    (tensorProduct.mapIso (Iso.prod (Iso.refl F)
      (@asIso _ _ _ _ (twistMultiplicationMap 𝒮 n m) h))).isIso_hom
  exact IsIso.comp_isIso' firstIso
    (IsIso.comp_isIso' secondIso (IsIso.comp_isIso' thirdIso fourthIso))

end AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ModuleTwistIso

universe u w

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **Equation 01MO on all of `Proj S`, with the second index arbitrary.** If the ratio locus of
`d` is everything then `𝒪(dn) ⊗ 𝒪(m) ⟶ 𝒪(dn + m)` is an isomorphism for every integer `m`. -/
public theorem isIso_twistMultiplicationMap_left_of_ratioLocus_eq_top {d : ℕ}
    (hd : ProjShared.ratioLocus 𝒮 d = ⊤) (n m : ℤ) :
    IsIso (twistMultiplicationMap 𝒮 ((d : ℤ) * n) m) := by
  have hstalk : ∀ x : ↑↑(AlgebraicGeometry.Proj 𝒮).toRingedSpace.toPresheafedSpace,
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((SheafOfModules.toSheaf (structureSheafRing
          (AlgebraicGeometry.Proj 𝒮).toRingedSpace)).map
          (twistMultiplicationMap 𝒮 ((d : ℤ) * n) m)).hom) := by
    intro x
    have hx : x ∈ ProjShared.ratioLocus 𝒮 d := by
      rw [hd]
      trivial
    obtain ⟨e, f, g, hf, hg, hfx, hgx⟩ := (ProjShared.mem_ratioLocus_iff 𝒮 d x).mp hx
    have hx' : x ∈ ProjectiveSpectrum.basicOpen 𝒮 (f * g) := fun hmul =>
      (x.isPrime.mem_or_mem hmul).elim hfx hgx
    exact isIso_stalkFunctor_map_twistMultiplication_left 𝒮 hf hg
      (mul_comm (n : ℤ) (d : ℤ)) m hx'
  have h := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
    ((SheafOfModules.toSheaf (structureSheafRing
      (AlgebraicGeometry.Proj 𝒮).toRingedSpace)).map
      (twistMultiplicationMap 𝒮 ((d : ℤ) * n) m))
  exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (SheafOfModules.toSheaf
    (structureSheafRing (AlgebraicGeometry.Proj 𝒮).toRingedSpace)) h
    (PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
      (R := structureSheafRing (AlgebraicGeometry.Proj 𝒮).toRingedSpace))

/-- **Equation 03GJ on all of `Proj S`, with the second index arbitrary.** If the ratio locus of
`d` is everything then `𝒪(dn) ⊗ ℱ(m) ⟶ ℱ(dn + m)` is an isomorphism for every sheaf of
`𝒪_X`-modules `ℱ` and all integers `n` and `m`. -/
public theorem isIso_twistSheafMultiplicationMap_left_of_ratioLocus_eq_top {d : ℕ}
    (hd : ProjShared.ratioLocus 𝒮 d = ⊤)
    (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮))) (n m : ℤ) :
    IsIso (twistSheafMultiplicationMap 𝒮 F ((d : ℤ) * n) m) :=
  isIso_twistSheafMultiplicationMap_of_isIso_twistMultiplicationMap 𝒮 F _ m
    (isIso_twistMultiplicationMap_left_of_ratioLocus_eq_top 𝒮 hd n m)

/-- **Equation 03GJ as an isomorphism**, `𝒪(dn) ⊗ ℱ(m) ≅ ℱ(dn + m)`. -/
public def twistSheafMultiplicationIsoLeft {d : ℕ}
    (hd : ProjShared.ratioLocus 𝒮 d = ⊤)
    (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮))) (n m : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).obj
        (twistingSheaf 𝒮 ((d : ℤ) * n))).obj (twistSheafOfModules 𝒮 F m)) ≅
      twistSheafOfModules 𝒮 F ((d : ℤ) * n + m) :=
  @asIso _ _ _ _ (twistSheafMultiplicationMap 𝒮 F ((d : ℤ) * n) m)
    (isIso_twistSheafMultiplicationMap_left_of_ratioLocus_eq_top 𝒮 hd F n m)

/-- **A twist of a twist, when the outer index is a multiple of `d`:**
`(ℱ(m))(dn) ≅ ℱ(dn + m)`.

Equation 03GJ has the twist in the left slot of the tensor product and a twist of a twist has it
in the right one, so the braiding of the tensor product crosses the two. -/
public def twistSheafIterateIso {d : ℕ} (hd : ProjShared.ratioLocus 𝒮 d = ⊤)
    (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮))) (n m : ℤ) :
    twistSheafOfModules 𝒮 (twistSheafOfModules 𝒮 F m) ((d : ℤ) * n) ≅
      twistSheafOfModules 𝒮 F ((d : ℤ) * n + m) :=
  (Stacks.SheafOfModules.Invertible.tensorProductBraiding
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj
    (hO := ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮)).property)
    (twistSheafOfModules 𝒮 F m) (twistingSheaf 𝒮 ((d : ℤ) * n))).trans
    (twistSheafMultiplicationIsoLeft 𝒮 hd F n m)

end Stacks.AlgebraicGeometry.ModuleTwistIso

end
