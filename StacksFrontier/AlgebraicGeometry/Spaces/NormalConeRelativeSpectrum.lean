module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraAffineSections

/-!
# The normal cone and the normal bundle of an immersion of algebraic spaces

Let `S` be a scheme and `i : Z ⟶ X` an immersion of algebraic spaces over `S`, with conormal
algebra `𝒞_{Z/X,*}` of Stacks 09RN (`AlgebraicGeometry.Space.conormalAlgebraOfImmersion`) and
conormal sheaf `𝒞_{Z/X} = 𝒞_{Z/X,1}` of Stacks 04CN
(`AlgebraicGeometry.Space.conormalModuleOfImmersion`, the degree-one piece of `𝒞_{Z/X,*}` by
`AlgebraicGeometry.Space.conormalModuleOfImmersion_eq_conormalAlgebraOfImmersion_piece_one`).
**Stacks 09RU** defines

* the *normal cone* `C_ZX = \underline{Spec}_Z(𝒞_{Z/X,*})`, and
* the *normal bundle* `N_ZX = \underline{Spec}_Z(Sym(𝒞_{Z/X}))`,

relative spectra in the sense of Stacks 081W.  This file constructs both, with no hypothesis
beyond the immersion: each is the relative spectrum
`AlgebraicGeometry.Space.relativeSpecOfBounded` of its algebra — an algebraic space affine over
`Z` whose structure morphism `π` has `π_* 𝒪 ≅` the algebra as sheaves of commutative
`𝒪_Z`-algebras, which is what `\underline{Spec}_Z` of the algebra means — and every input of that
construction is proved here or upstream:

* both algebras are commutative: `𝒞_{Z/X,*}` in every pair of integer degrees by
  `AlgebraicGeometry.Space.isCommutative_conormalAlgebra`, `Sym(𝒞_{Z/X})` by
  `AlgebraicGeometry.Space.symmetricAlgebra_mul_comm`;
* both are quasi-coherent:
  `AlgebraicGeometry.Space.isQuasicoherent_conormalAlgebraSheafOfImmersion` and
  `AlgebraicGeometry.Space.isQuasicoherent_conormalSymmetricAlgebraSheafOfImmersion`;
* both have bounded chart sections, the size condition under which the chart construction stays
  in the big fppf site:
  `AlgebraicGeometry.Space.hasBoundedChartSections_conormalAlgebraSheafOfImmersion` and
  `AlgebraicGeometry.Space.hasBoundedChartSections_conormalSymmetricAlgebraSheafOfImmersion`.

## Main definitions

* `AlgebraicGeometry.Space.immersionNormalCone`: **Stacks 09RU, the normal cone `C_ZX`**, as an
  algebraic space affine over `Z`, with `AlgebraicGeometry.Space.immersionNormalConePushforwardIso`
  identifying the direct image of its structure sheaf with `𝒞_{Z/X,*}`.
* `AlgebraicGeometry.Space.immersionNormalBundle`: **Stacks 09RU, the normal bundle `N_ZX`**, as an
  algebraic space affine over `Z`, with
  `AlgebraicGeometry.Space.immersionNormalBundlePushforwardIso` identifying the direct image of its
  structure sheaf with `Sym(𝒞_{Z/X})`.

## Implementation notes

The declarations here reuse the algebra sheaves `AlgebraicGeometry.Space.conormalAlgebraSheaf`
and `AlgebraicGeometry.Space.conormalSymmetricAlgebraSheaf` of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalConeOfImmersion` verbatim.

## References

* [Stacks Project, Tag 09RU](https://stacks.math.columbia.edu/tag/09RU)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

variable {Z₀ X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The symmetric algebra of the conormal sheaf -/

/-- **`Sym(𝒞_{Z/X})` as a sheaf of commutative `𝒪_Z`-algebras**, for an immersion: the symmetric
algebra of the conormal sheaf, the degree-one piece of the conormal algebra. -/
abbrev conormalSymmetricAlgebraSheafOfImmersion (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    AlgebraSheaf.{u, u} B S hS Z₀ hZ :=
  conormalSymmetricAlgebraSheaf B S hS (immersionClosedFactorization B S hS hX hZ i hi)

/-- The conormal sheaf of an immersion is cartesian on affine charts, being quasi-coherent. -/
theorem isCartesianOnAffineCharts_conormalAlgebraOfImmersion_piece_one
    (hX : IsAlgebraicSpace B S hS X₀) (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀)
    (hi : IsImmersion B S hS i) :
    IsCartesianOnAffineCharts (conormalAlgebraPieceOne B S hS
      (immersionClosedFactorization B S hS hX hZ i hi)) :=
  isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Z₀ hZ _
    (isQuasicoherentOnSite_conormalAlgebraOfImmersion_piece B S hS hX hZ i hi 1)

/-- **`Sym(𝒞_{Z/X})` of an immersion is a quasi-coherent sheaf of commutative `𝒪_Z`-algebras.**
Its module is the coproduct of the symmetric powers of the quasi-coherent conormal sheaf, which
are quasi-coherent and vanish in negative degrees. -/
theorem isQuasicoherent_conormalSymmetricAlgebraSheafOfImmersion
    (hX : IsAlgebraicSpace B S hS X₀) (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀)
    (hi : IsImmersion B S hS i) :
    (conormalSymmetricAlgebraSheafOfImmersion B S hS hX hZ i hi).IsQuasicoherent :=
  isQuasicoherent_gradedAlgebraSheaf B S hS _ _ _
    (fun n hn => @PresheafOfModules.isZero_symmetricAlgebraSheafify_piece _ _
      (SmallEtale.topology B S hS Z₀) (structureSheaf B S hS Z₀ hZ).obj
      (structureRingSheaf B S hS ⟨Z₀, hZ⟩) (𝟙 _)
      (isLocallyInjective_id_structureRingSheaf B S hS ⟨Z₀, hZ⟩)
      (isLocallySurjective_id_structureRingSheaf B S hS ⟨Z₀, hZ⟩)
      (wEqualsLocallyBijective_smallEtale B S hS ⟨Z₀, hZ⟩)
      (hasWeakSheafify_smallEtale B S hS ⟨Z₀, hZ⟩) _ n hn)
    (isQuasicoherentOnSite_symmetricAlgebra_piece_of_isCartesianOnAffineCharts B S hS ⟨Z₀, hZ⟩ _
      (isCartesianOnAffineCharts_conormalAlgebraOfImmersion_piece_one B S hS hX hZ i hi))

/-- **`Sym(𝒞_{Z/X})` of an immersion has bounded chart sections.**  Over an affine chart `O` cut
out of an étale chart `V` of `Z`, the sections of `Symⁿ(𝒞_{Z/X})` are `Symⁿ_{𝒪(O)}(𝒞_{Z/X}(O))`,
bounded by `2 ^ size V` (for `𝒪(O)`), by the uniform bound for the conormal sheaf over the opens of
`V`, and by `ℵ₀`, all independently of `n` and of `O`. -/
theorem hasBoundedChartSections_conormalSymmetricAlgebraSheafOfImmersion
    (hX : IsAlgebraicSpace B S hS X₀) (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀)
    (hi : IsImmersion B S hS i) :
    HasBoundedChartSections B S hS ⟨Z₀, hZ⟩
      (conormalSymmetricAlgebraSheafOfImmersion B S hS hX hZ i hi) := by
  intro V
  obtain ⟨c₁, hc₁, hc₁Ω⟩ :=
    exists_mk_conormalAlgebraOfImmersion_piece_openChart_le B S hS hX hZ i hi 1 V
  have hV : (chartScheme V).size < B.cutoff := SmallEtale.contains_chartScheme B S hS Z₀ V
  set c := max (max (2 ^ (chartScheme V).size) c₁) ℵ₀ with hcdef
  have hc : c < B.cutoff :=
    max_lt (max_lt (B.cutoff_isStrongPrelimit hV) hc₁) B.aleph0_lt_cutoff
  refine ⟨c ^ ℵ₀, power_lt_of_isStrongPrelimit B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hc
    B.aleph0_lt_cutoff, fun O => ?_⟩
  have hO : IsAffine ((SmallEtale.toOver B S hS Z₀ ⋙ BigFppfOver.toScheme B S hS).obj
      (openChart B S hS Z₀ V (O : (chartScheme V).Opens))) := O.2
  refine mk_gradedAlgebraSheaf_sections_le B S hS _ _ _
    (fun n hn => @PresheafOfModules.isZero_symmetricAlgebraSheafify_piece _ _
      (SmallEtale.topology B S hS Z₀) (structureSheaf B S hS Z₀ hZ).obj
      (structureRingSheaf B S hS ⟨Z₀, hZ⟩) (𝟙 _)
      (isLocallyInjective_id_structureRingSheaf B S hS ⟨Z₀, hZ⟩)
      (isLocallySurjective_id_structureRingSheaf B S hS ⟨Z₀, hZ⟩)
      (wEqualsLocallyBijective_smallEtale B S hS ⟨Z₀, hZ⟩)
      (hasWeakSheafify_smallEtale B S hS ⟨Z₀, hZ⟩) _ n hn) _ hO fun n => ?_
  refine (mk_symmetricAlgebra_piece_sections_le B S hS ⟨Z₀, hZ⟩ _
    (isCartesianOnAffineCharts_conormalAlgebraOfImmersion_piece_one B S hS hX hZ i hi) n _ hO).trans
    (max_le_max (max_le_max ?_ (hc₁Ω O)) le_rfl)
  refine (mk_sections_structureRingSheaf_le_two_pow_size B S hS ⟨Z₀, hZ⟩
    (openChart B S hS Z₀ V (O : (chartScheme V).Opens))).trans ?_
  exact Cardinal.power_le_power_left two_ne_zero (Scheme.size_coe_opens_le _ _)

/-! ### Stacks 09RU -/

/-- **Stacks Project, Tag 09RU.  The normal cone `C_ZX = \underline{Spec}_Z(𝒞_{Z/X,*})` of an
immersion `i : Z ⟶ X` of algebraic spaces**, as an algebraic space affine over `Z`: the relative
spectrum (Stacks 081W) of the conormal algebra of Stacks 09RN.  Its structure morphism is affine
(this is the `AffineOver` property) and the direct image of its structure sheaf is `𝒞_{Z/X,*}`
(`AlgebraicGeometry.Space.immersionNormalConePushforwardIso`). -/
@[stacks 09RU "the normal cone C_ZX = Spec_Z(C_{Z/X,*}) of an immersion, as an algebraic space \
affine over Z"]
def immersionNormalCone (hX : IsAlgebraicSpace B S hS X₀) (hZ : IsAlgebraicSpace B S hS Z₀)
    (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    AffineOver B S hS (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) :=
  relativeSpecOfBounded B S hS ⟨Z₀, hZ⟩ (conormalAlgebraSheafOfImmersion B S hS hX hZ i hi)
    (isQuasicoherent_conormalAlgebraSheafOfImmersion B S hS hX hZ i hi)
    (hasBoundedChartSections_conormalAlgebraSheafOfImmersion B S hS hX hZ i hi)

/-- **Stacks Project, Tag 09RU.  `C_ZX` is the relative spectrum of `𝒞_{Z/X,*}`**: for its
projection `π : C_ZX ⟶ Z`, `π_* 𝒪_{C_ZX} ≅ 𝒞_{Z/X,*}` as sheaves of commutative
`𝒪_Z`-algebras. -/
@[stacks 09RU "the direct image of the structure sheaf of the normal cone C_ZX is the conormal \
algebra C_{Z/X,*}, i.e. C_ZX = Spec_Z(C_{Z/X,*})"]
def immersionNormalConePushforwardIso (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    pushforwardAlgebra B S hS (immersionNormalCone B S hS hX hZ i hi).obj ≅
      conormalAlgebraSheafOfImmersion B S hS hX hZ i hi :=
  relativeSpecOfBoundedPushforwardIso B S hS _ _ _ _

/-- **Stacks Project, Tag 09RU.  The normal bundle `N_ZX = \underline{Spec}_Z(Sym(𝒞_{Z/X}))` of
an immersion `i : Z ⟶ X` of algebraic spaces**, as an algebraic space affine over `Z`: the
relative spectrum (Stacks 081W) of the symmetric algebra on the conormal sheaf `𝒞_{Z/X}` of
Stacks 04CN.  Its structure morphism is affine and the direct image of its structure sheaf is
`Sym(𝒞_{Z/X})` (`AlgebraicGeometry.Space.immersionNormalBundlePushforwardIso`). -/
@[stacks 09RU "the normal bundle N_ZX = Spec_Z(Sym(C_{Z/X})) of an immersion, as an algebraic \
space affine over Z"]
def immersionNormalBundle (hX : IsAlgebraicSpace B S hS X₀) (hZ : IsAlgebraicSpace B S hS Z₀)
    (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    AffineOver B S hS (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) :=
  relativeSpecOfBounded B S hS ⟨Z₀, hZ⟩ (conormalSymmetricAlgebraSheafOfImmersion B S hS hX hZ i hi)
    (isQuasicoherent_conormalSymmetricAlgebraSheafOfImmersion B S hS hX hZ i hi)
    (hasBoundedChartSections_conormalSymmetricAlgebraSheafOfImmersion B S hS hX hZ i hi)

/-- **Stacks Project, Tag 09RU.  `N_ZX` is the relative spectrum of `Sym(𝒞_{Z/X})`**: for its
projection `π : N_ZX ⟶ Z`, `π_* 𝒪_{N_ZX} ≅ Sym(𝒞_{Z/X})` as sheaves of commutative
`𝒪_Z`-algebras. -/
@[stacks 09RU "the direct image of the structure sheaf of the normal bundle N_ZX is \
Sym(C_{Z/X}), i.e. N_ZX = Spec_Z(Sym(C_{Z/X}))"]
def immersionNormalBundlePushforwardIso (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    pushforwardAlgebra B S hS (immersionNormalBundle B S hS hX hZ i hi).obj ≅
      conormalSymmetricAlgebraSheafOfImmersion B S hS hX hZ i hi :=
  relativeSpecOfBoundedPushforwardIso B S hS _ _ _ _

end AlgebraicGeometry.Space

end
