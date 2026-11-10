module

public import StacksFrontier.AlgebraicGeometry.Conormal.ConormalSequence
public import StacksFrontier.AlgebraicGeometry.Conormal.ConormalSequenceMiddle

/-!
# Exactness of the conormal sequence at its middle term

For immersions `Z --i--→ Y --j--→ X` of schemes the canonical sequence of
[Stacks Project, Tag 062S] is `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0`, both maps being the
canonical maps of [Stacks Project, Tag 01R4]. Surjectivity of the right-hand map is
`Stacks.Immersion.epi_conormalSequenceRightMap`; this file proves that the composite of the two
maps vanishes, assembles them into a two-term complex, and proves that the complex is exact —
the exactness of the sequence at `𝒞_{Z/X}`.

## Main definitions

* `Stacks.Immersion.conormalSequenceShortComplex` is the two-term complex
  `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` formed by the two canonical maps.

## Main results

* `Stacks.Immersion.ConormalChart.rightMap_toCotangent`: over a chart of the chain, the
  right-hand map carries the class of a function cutting out `Z` in the chart to the class of
  its restriction to the preimage of the chart in `Y`.
* `Stacks.Immersion.ConormalChart.exists_leftMap_eq`: over a chart, a conormal section killed by
  the right-hand map comes from the pullback of the conormal sheaf of `Y` in `X`.
* `Stacks.Immersion.conormalSequence_comp_zero`: the two canonical maps compose to zero.
* `Stacks.Immersion.conormalSequence_exact`: the conormal sequence is exact at `𝒞_{Z/X}`, that
  is, the kernel of `𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` is the image of `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X}`.

## Implementation notes

The left-hand map used here is `Stacks.Immersion.conormalLeftMap`, the canonical map of
[Stacks Project, Tag 01R4] for the square with horizontal maps `i ≫ j` and `j` and vertical maps
`i` and `𝟙_X`. It agrees by definition with
`Stacks.AlgebraicGeometry.conormalSequenceLeftMap` of
`StacksFrontier.AlgebraicGeometry.Conormal.SplitSequence`, which is where that arrow carries its
clause of [Stacks Project, Tag 062S]; the two spellings are identified by
`Stacks.AlgebraicGeometry.conormalSequenceLeftMap_eq`.

Exactness at `𝒞_{Z/X}` is local on `Z`, and it is tested over the charts of the chain of
immersions supplied by `Stacks.Immersion.exists_conormalChart`: affine opens `V ⊆ X` with affine
preimage in `Y` over which each of `j`, `i ≫ j` and `i` is cut out by an ideal. Over such a chart
`Stacks.Immersion.ConormalChart.leftMap_toCotangent` and
`Stacks.Immersion.ConormalChart.rightMap_toCotangent` identify the two maps on conormal sections
with the two maps of conormal modules of the tower of rings
`Γ(X, V) ⟶ Γ(X, V) ⟶ Γ(Y, j⁻¹V)`, whose exactness is
`Stacks.Conormal.exact_mapCotangent_comap`. The passage from the charts to `Z` is
`Stacks.Immersion.exact_of_chartwise`.

The vanishing of the composite is proved after transposing along `i^* ⊣ i_*`, where both maps act
on sections over opens of `Y`; the transposed composite vanishes over the preimage of every chart,
and the charts refine every open of `Y`.

## References

* [Stacks Project, Tag 062S](https://stacks.math.columbia.edu/tag/062S)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.ClosedImmersion Stacks.ClosedImmersion.AffineConormal
open Stacks.ClosedImmersion.IdealSheafAffine

universe u

namespace Stacks.Immersion

variable {Z Y X : Scheme.{u}}

/-- **The inverse of the affine identification of [Stacks Project, Tag 01R3] part (2) carries
zero to zero.** `Stacks.Conormal.affineConormalIsoCotangent` is an isomorphism of modules over
the ring
of sections of the structure sheaf over the ambient affine open, a ring whose spelling on the
conormal-sections side differs from the spelling `Ideal.Cotangent` carries on the quotient side;
the module structure on the quotient side is therefore supplied explicitly, after which
additivity of the map is available. -/
private theorem affineConormalIsoCotangent_inv_zero {S T : Scheme.{u}} (f : S ⟶ T) [IsImmersion f]
    (V : T.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(T, V))
    (e : pullback f V.ι ≅ Spec (quotRing I))
    (he : pullback.snd f V.ι ≫ hV.isoSpec.hom = e.hom ≫ quotImmersion Γ(T, V) I) :
    (Stacks.Conormal.affineConormalIsoCotangent f V hV I e he).inv.hom 0 = 0 := by
  let : Module ↑((structureSheafRing T.toSheafedSpace).obj.obj (op V))
      (↑(ModuleCat.of (↑Γ(T, V)) I.Cotangent)) :=
    (ModuleCat.of (↑Γ(T, V)) I.Cotangent).isModule
  exact map_zero _

/-- **A class in `I/I²` whose image under the affine identification of
[Stacks Project, Tag 01R3] part (2) vanishes is zero**, that identification being an
isomorphism: apply the identification to the hypothesis and use the round trip. -/
private theorem eq_zero_of_affineConormalIsoCotangent_inv_eq_zero {S T : Scheme.{u}} (f : S ⟶ T)
    [IsImmersion f] (V : T.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(T, V))
    (e : pullback f V.ι ≅ Spec (quotRing I))
    (he : pullback.snd f V.ι ≫ hV.isoSpec.hom = e.hom ≫ quotImmersion Γ(T, V) I)
    (v : I.Cotangent)
    (hv : (Stacks.Conormal.affineConormalIsoCotangent f V hV I e he).inv.hom v = 0) : v = 0 :=
  Function.LeftInverse.injective
    (iso_hom_inv_apply (Stacks.Conormal.affineConormalIsoCotangent f V hV I e he))
    (hv.trans (affineConormalIsoCotangent_inv_zero f V hV I e he).symm)

/-- **The right-hand map on an affine generator.** Over a chart of the chain `Z ⟶ Y ⟶ X`, the map
`𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` carries the class in `J/J²` of a function `c` cutting out `Z` in the chart to
the class in `I/I²` of its restriction to the preimage of the chart in `Y`.

This is the affine characterisation of [Stacks Project, Tag 01R4] for the square defining the
right-hand map, read through `RingedSpaceModuleAdjunction.homEquiv_id_eq`, which
identifies the transpose along `(𝟙_Z)^* ⊣ (𝟙_Z)_*` with precomposition by the pullback-identity
isomorphism. -/
theorem ConormalChart.rightMap_toCotangent {i : Z ⟶ Y} {j : Y ⟶ X} [IsImmersion i]
    [IsImmersion j] (C : ConormalChart i j) (c : C.idealZ) :
    (conormalSequenceRightMap i j).val.app (op ((i ≫ j) ⁻¹ᵁ C.V))
        (C.isoZ.inv.hom (C.idealZ.toCotangent c)) =
      C.isoZY.inv.hom (C.idealZY.toCotangent
        ⟨(j.app C.V).hom (c : Γ(X, C.V)), C.map_mem_idealZY c⟩) := by
  have h := isInducedConormalSheafMap_immersionConormalSheafMap i (i ≫ j) (𝟙 Z) j
    (conormalSequence_isPullback i j).w (j ⁻¹ᵁ C.V) C.hW C.V C.hV le_rfl
    C.idealZY C.idealZ C.eI C.heI C.eZ C.heZ c
    ⟨(j.app C.V).hom (c : Γ(X, C.V)), C.map_mem_idealZY c⟩ (by rw [Scheme.Hom.appLE_eq_app])
  have hid : (modulePullbackPushforwardAdjunction
        (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom).homEquiv
        (conormalSheaf (i ≫ j).liftCoborder.toLRSHom.toShHom)
        (conormalSheaf i.liftCoborder.toLRSHom.toShHom)
        (immersionConormalSheafMap i (i ≫ j) (𝟙 Z) j
          (toShHom_square (conormalSequence_isPullback i j).w)) =
      conormalSequenceRightMap i j :=
    RingedSpaceModuleAdjunction.homEquiv_id_eq
      Z.toLocallyRingedSpace.toRingedSpace _ _ _
  rw [hid] at h
  exact (val_map_self_apply (conormalSheaf i.liftCoborder.toLRSHom.toShHom)
    (homOfLE (le_refl (i ⁻¹ᵁ (j ⁻¹ᵁ C.V)))) _).symm.trans h

/-- **Over a chart, a conormal section of `Z` in `X` killed by the right-hand map comes from the
pullback of the conormal sheaf of `Y` in `X`.** This is the exactness of the conormal sequence at
`𝒞_{Z/X}` read over the preimage of a chart.

The two maps on conormal sections over the chart are the two maps of conormal modules of the
tower `Γ(X, V) ⟶ Γ(X, V) ⟶ Γ(Y, j⁻¹V)` by
`Stacks.Immersion.ConormalChart.leftMap_unit_toCotangent` and
`Stacks.Immersion.ConormalChart.rightMap_toCotangent`, and that sequence is exact by
`Stacks.Conormal.exact_mapCotangent_comap`, the map `Γ(X, V) ⟶ Γ(Y, j⁻¹V)` being surjective. -/
theorem ConormalChart.exists_leftMap_eq {i : Z ⟶ Y} {j : Y ⟶ X} [IsImmersion i] [IsImmersion j]
    (C : ConormalChart i j)
    (β : (conormalSheaf (i ≫ j).liftCoborder.toLRSHom.toShHom).val.obj
      (op ((i ≫ j) ⁻¹ᵁ C.V)))
    (hβ : (conormalSequenceRightMap i j).val.app (op ((i ≫ j) ⁻¹ᵁ C.V)) β = 0) :
    ∃ α : ((modulePullback i.toLRSHom.toShHom).obj
        (conormalSheaf j.liftCoborder.toLRSHom.toShHom)).val.obj (op ((i ≫ j) ⁻¹ᵁ C.V)),
      (conormalLeftMap i j).val.app (op ((i ≫ j) ⁻¹ᵁ C.V)) α = β := by
  classical
  obtain ⟨x, rfl⟩ : ∃ x, C.isoZ.inv.hom x = β :=
    ⟨C.isoZ.hom.hom β, iso_inv_hom_apply C.isoZ β⟩
  obtain ⟨c, rfl⟩ := C.idealZ.toCotangent_surjective x
  have hzero : C.isoZY.inv.hom (C.idealZY.toCotangent
      ⟨(j.app C.V).hom (c : Γ(X, C.V)), C.map_mem_idealZY c⟩) = 0 :=
    (C.rightMap_toCotangent c).symm.trans hβ
  have hg : C.idealZY.toCotangent
      ⟨(j.app C.V).hom (c : Γ(X, C.V)), C.map_mem_idealZY c⟩ = 0 :=
    eq_zero_of_affineConormalIsoCotangent_inv_eq_zero i (j ⁻¹ᵁ C.V) C.hW C.idealZY C.eI C.heI _
      hzero
  let : Algebra Γ(X, C.V) Γ(Y, j ⁻¹ᵁ C.V) := (j.app C.V).hom.toAlgebra
  have hle₁ : C.idealY ≤ Ideal.comap (Algebra.ofId Γ(X, C.V) Γ(X, C.V)) C.idealZ :=
    fun _ hy => C.idealY_le_idealZ hy
  have hle₂ : C.idealZ ≤ Ideal.comap (Algebra.ofId Γ(X, C.V) Γ(Y, j ⁻¹ᵁ C.V)) C.idealZY :=
    fun y hy => C.map_mem_idealZY ⟨y, hy⟩
  have hex : Function.Exact
      (Ideal.mapCotangent C.idealY C.idealZ (Algebra.ofId Γ(X, C.V) Γ(X, C.V)) hle₁)
      (Ideal.mapCotangent C.idealZ C.idealZY
        (Algebra.ofId Γ(X, C.V) Γ(Y, j ⁻¹ᵁ C.V)) hle₂) :=
    Stacks.Conormal.exact_mapCotangent_comap C.hq C.idealZY hle₁ hle₂
  obtain ⟨w, hw⟩ := (hex (C.idealZ.toCotangent c)).mp hg
  obtain ⟨k, rfl⟩ := C.idealY.toCotangent_surjective w
  refine ⟨((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
    (conormalSheaf j.liftCoborder.toLRSHom.toShHom)).val.app (op (j ⁻¹ᵁ C.V))
      (C.isoY.inv.hom (C.idealY.toCotangent k)), ?_⟩
  rw [C.leftMap_unit_toCotangent k]
  exact congrArg C.isoZ.inv.hom hw

/-- **[Stacks Project, Tag 062S]: the two canonical maps of the conormal sequence compose to
zero.** For immersions `Z ⟶ Y ⟶ X` the composite
`i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` vanishes.

Transposing along `i^* ⊣ i_*` turns the statement into one about sections over opens of `Y`. Over
the preimage of a chart a section of `𝒞_{Y/X}` is the class of a function `k` cutting out `Y`, the
left-hand map carries it to the class of `k` as a function cutting out `Z` in `X`, and the
right-hand map carries that to the class of the restriction of `k` to the preimage of the chart
in `Y`, which is zero because `k` vanishes there. The charts refine every open of `Y`. -/
@[stacks 062S "the two canonical maps form a complex: the composite \
i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} is zero, for any immersions i : Z ⟶ Y and j : Y ⟶ X; the \
left-hand map is Stacks.Immersion.conormalLeftMap, equal to \
Stacks.AlgebraicGeometry.conormalSequenceLeftMap by \
Stacks.AlgebraicGeometry.conormalSequenceLeftMap_eq"]
theorem conormalSequence_comp_zero (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    conormalLeftMap i j ≫ conormalSequenceRightMap i j = 0 := by
  classical
  have happ : ∀ (O : Y.Opens)
      (s : (conormalSheaf j.liftCoborder.toLRSHom.toShHom).val.obj (op O)),
      (conormalSequenceRightMap i j).val.app (op (i ⁻¹ᵁ O))
        (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).homEquiv _ _
          (conormalLeftMap i j)).val.app (op O) s) = 0 := by
    intro O s
    obtain ⟨V₀, hV₀⟩ := exists_preimage_eq j O
    let A := {C : ConormalChart i j // C.V ≤ V₀}
    let B : A → Z.Opens := fun p => (i ≫ j) ⁻¹ᵁ p.1.V
    have hOle : ∀ p : A, j ⁻¹ᵁ p.1.V ≤ O := by
      intro p
      rw [← hV₀]
      exact j.preimage_mono p.2
    have hBT : ∀ p : A, B p ≤ i ⁻¹ᵁ O := fun p => i.preimage_mono (hOle p)
    have hcover : i ⁻¹ᵁ O ≤ ⨆ p : A, B p := by
      intro z hz
      rw [← hV₀] at hz
      obtain ⟨C, hCV, hCz⟩ := exists_conormalChart i j z V₀ hz
      exact (Opens.mem_iSup).2 ⟨⟨C, hCV⟩, hCz⟩
    refine (show TopCat.Sheaf _ Z.carrier from
        ⟨(conormalSheaf i.liftCoborder.toLRSHom.toShHom).val.presheaf,
          (conormalSheaf i.liftCoborder.toLRSHom.toShHom).isSheaf⟩).eq_of_locally_eq'
      (U := B) (i ⁻¹ᵁ O) (fun p => homOfLE (hBT p)) hcover _ 0 (fun p => ?_)
    refine Eq.trans ?_ (map_zero _).symm
    obtain ⟨y, hy⟩ : ∃ y, p.1.isoY.inv.hom y =
        (conormalSheaf j.liftCoborder.toLRSHom.toShHom).val.map (homOfLE (hOle p)).op s :=
      ⟨p.1.isoY.hom.hom _, iso_inv_hom_apply p.1.isoY _⟩
    obtain ⟨k, rfl⟩ := p.1.idealY.toCotangent_surjective y
    have hrightNat : (conormalSheaf i.liftCoborder.toLRSHom.toShHom).val.map (homOfLE (hBT p)).op
          ((conormalSequenceRightMap i j).val.app (op (i ⁻¹ᵁ O))
            (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).homEquiv _ _
              (conormalLeftMap i j)).val.app (op O) s)) =
        (conormalSequenceRightMap i j).val.app (op ((i ≫ j) ⁻¹ᵁ p.1.V))
          ((conormalSheaf (i ≫ j).liftCoborder.toLRSHom.toShHom).val.map (homOfLE (hBT p)).op
            (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).homEquiv _ _
              (conormalLeftMap i j)).val.app (op O) s)) :=
      (val_app_naturality (conormalSequenceRightMap i j) (homOfLE (hBT p)) _).symm
    have hleftNat : (conormalSheaf (i ≫ j).liftCoborder.toLRSHom.toShHom).val.map
            (homOfLE (hBT p)).op
          (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).homEquiv _ _
            (conormalLeftMap i j)).val.app (op O) s) =
        ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).homEquiv _ _
            (conormalLeftMap i j)).val.app (op (j ⁻¹ᵁ p.1.V))
          ((conormalSheaf j.liftCoborder.toLRSHom.toShHom).val.map (homOfLE (hOle p)).op s) :=
      (val_app_naturality ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).homEquiv _ _
        (conormalLeftMap i j)) (homOfLE (hOle p)) s).symm
    have hvanish : (conormalSequenceRightMap i j).val.app (op ((i ≫ j) ⁻¹ᵁ p.1.V))
          (p.1.isoZ.inv.hom (p.1.idealZ.toCotangent
            ⟨(k : Γ(X, p.1.V)), p.1.idealY_le_idealZ k.2⟩)) = 0 := by
      refine (p.1.rightMap_toCotangent ⟨(k : Γ(X, p.1.V)), p.1.idealY_le_idealZ k.2⟩).trans ?_
      refine Eq.trans (congrArg p.1.isoZY.inv.hom ?_)
        (affineConormalIsoCotangent_inv_zero i (j ⁻¹ᵁ p.1.V) p.1.hW p.1.idealZY p.1.eI p.1.heI)
      rw [Ideal.toCotangent_eq_zero]
      change (j.app p.1.V).hom (k : Γ(X, p.1.V)) ∈ p.1.idealZY ^ 2
      rw [RingHom.mem_ker.mp k.2]
      exact Submodule.zero_mem _
    change (conormalSheaf i.liftCoborder.toLRSHom.toShHom).val.map (homOfLE (hBT p)).op
      ((conormalSequenceRightMap i j).val.app (op (i ⁻¹ᵁ O))
        (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).homEquiv _ _
          (conormalLeftMap i j)).val.app (op O) s)) = 0
    rw [hrightNat, hleftNat, ← hy, p.1.leftMap_toCotangent k]
    exact hvanish
  have key : (modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).homEquiv _ _
        (conormalLeftMap i j) ≫
      (modulePushforward i.toLRSHom.toShHom).map (conormalSequenceRightMap i j) = 0 :=
    hom_eq_zero_of_val_app _ fun O x => happ O x
  have hzero : (modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).homEquiv
      (conormalSheaf j.liftCoborder.toLRSHom.toShHom)
      (conormalSheaf i.liftCoborder.toLRSHom.toShHom) 0 = 0 := by
    rw [Adjunction.homEquiv_unit, modulePushforward_map_zero]
    exact Limits.comp_zero
  refine ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).homEquiv
    (conormalSheaf j.liftCoborder.toLRSHom.toShHom)
    (conormalSheaf i.liftCoborder.toLRSHom.toShHom)).injective ?_
  rwa [Adjunction.homEquiv_naturality_right, hzero]

/-- **The conormal sequence of [Stacks Project, Tag 062S]** as a two-term complex of
`𝒪_Z`-modules, `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y}`. -/
@[stacks 062S "the sequence as a short complex"]
def conormalSequenceShortComplex (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    ShortComplex (SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)) :=
  ShortComplex.mk (conormalLeftMap i j) (conormalSequenceRightMap i j)
    (conormalSequence_comp_zero i j)

/-- **[Stacks Project, Tag 062S]: the conormal sequence is exact at `𝒞_{Z/X}`.** For immersions
`Z ⟶ Y ⟶ X` the kernel of the canonical map `𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` is the image of the canonical
map `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X}`.

Exactness is local, and it is tested over the preimages of the charts of the chain
(`Stacks.Immersion.exact_of_chartwise`). Over a chart the two maps are, on sections, the two maps
of conormal modules of the tower of rings `Γ(X, V) ⟶ Γ(X, V) ⟶ Γ(Y, j⁻¹V)`, whose exactness is
`Stacks.Conormal.exact_mapCotangent_comap`; that is
`Stacks.Immersion.ConormalChart.exists_leftMap_eq`. -/
@[stacks 062S "exactness in the middle: for any immersions i : Z ⟶ Y and j : Y ⟶ X the image of \
i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} is the kernel of 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} (equality, as ShortComplex.Exact of \
the complex built from the two canonical maps of Tag 01R4); no hypothesis beyond the two \
immersions"]
theorem conormalSequence_exact (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    (conormalSequenceShortComplex i j).Exact :=
  exact_of_chartwise i j _ fun C β hβ => C.exists_leftMap_eq β hβ

end Stacks.Immersion

end
