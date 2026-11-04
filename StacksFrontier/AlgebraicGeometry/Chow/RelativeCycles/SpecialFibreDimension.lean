module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationCycle
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.JacobsonDimension
public import StacksFrontier.AlgebraicGeometry.FibreDimension.AffineComponents
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.ValuationFibreDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dimension of the special fibre of a schematic closure

Let `R` be a discrete valuation ring with fraction field `K` and residue field `κ`, let
`f : X ⟶ Spec R` be locally of finite type and let `Z ⊆ X_K` be the integral closed subscheme of
the generic fibre whose generic point is `ξ`, of dimension `r`. Write `\overline{Z} ⊆ X` for the
scheme-theoretic image of `Z` and `\overline{Z}_κ ⊆ X_κ` for its special fibre. This file proves
that `\overline{Z}_κ` is again equidimensional of dimension `r` as soon as it is nonempty: every
generic point of it has dimension `r` over `κ`.

The scheme `\overline{Z}` is irreducible, being the reduced closure of the image of `ξ`, and the
structure morphism `q : \overline{Z} ⟶ Spec R` is locally of finite type. If `\overline{Z}_κ` is
nonempty then `q` is moreover surjective: its image contains the generic point of `Spec R`,
because `\overline{Z}` contains the image of `ξ`, and it contains the closed point, because
`\overline{Z}_κ` is nonempty; and a prime ideal of a discrete valuation ring is either zero or
maximal, so these are all the points of `Spec R`. The fibre of `q` over the generic point is `Z`
and its fibre over the closed point is `\overline{Z}_κ`, so the assertion is exactly Tag 0B2J:
the special fibre of a surjective morphism locally of finite type from an irreducible scheme to
the spectrum of a valuation ring is equidimensional of the dimension of the generic fibre.

## Main results

* `Stacks.Chow.fiberPointDimension_specializationSpecialFibre` — every generic point of the
  special fibre of the scheme-theoretic image of an integral closed subscheme of dimension `r`
  of the generic fibre again has dimension `r`, provided that special fibre is nonempty.

## Implementation notes

The two identifications of fibres are packaged as a single homeomorphism
`Stacks.Chow.comapFiberHomeo`: for an ideal sheaf `I` on `Y` and a morphism `p : Y ⟶ S`, the
inverse image of `I` in the fibre of `p` over `t` and the fibre over `t` of the structure
morphism of the closed subscheme cut out by `I` are both the fibred product of
`I.subscheme ⟶ Y` and `Spec κ(t) ⟶ S` over `S`. Taking `t` to be the generic point of `Spec R`
identifies `Z` with a fibre of `q`, and taking `t` to be the closed point identifies
`\overline{Z}_κ` with the other one.

Passing between the topological dimension of a closed subscheme and the relative dimension of a
point is Tag 02QO, in the form `Stacks.Chow.topologicalKrullDim_eq_relativeDimension_toNat`; the
dimension function of the Chow situation on the spectrum of a field vanishes identically, so the
relative dimension there is a transcendence degree and in particular nonnegative.

## References

* [Stacks Project, Tag 0B2J](https://stacks.math.columbia.edu/tag/0B2J)
* [Stacks Project, Section 0H4H](https://stacks.math.columbia.edu/tag/0H4H)
* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Closed subschemes and their supports -/

/-- The closed subscheme cut out by an ideal sheaf is homeomorphic to the support of that ideal
sheaf: the inclusion of the subscheme is a closed embedding with that range. -/
public def subschemeHomeoSupport {Y : Scheme.{u}} (I : Y.IdealSheafData) :
    I.subscheme ≃ₜ (I.support : Set Y) :=
  (Homeomorph.Set.univ I.subscheme).symm.trans <|
    (I.subschemeι.isClosedEmbedding.isEmbedding.homeomorphImage _).trans
      (Homeomorph.setCongr (by rw [Set.image_univ, I.range_subschemeι]))

/-- A closed subscheme has the topological dimension of its support. -/
public theorem topologicalKrullDim_subscheme {Y : Scheme.{u}} (I : Y.IdealSheafData) :
    topologicalKrullDim I.subscheme = topologicalKrullDim (I.support : Set Y) :=
  (subschemeHomeoSupport I).isHomeomorph.topologicalKrullDim_eq

/-- A point of a scheme-theoretic fibre lies over the base point of that fibre. -/
theorem base_fiberι {Y S : Scheme.{u}} (p : Y ⟶ S) (t : S) (z : p.fiber t) :
    p.base (p.fiberι t z) = t := by
  have h : p.fiberι t z ∈ Set.range (p.fiberι t).base := Set.mem_range_self z
  rw [Scheme.Hom.range_fiberι] at h
  exact h

/-- The inverse image of an ideal sheaf `I` on `Y` in the fibre of `p : Y ⟶ S` over `t` cuts out
the fibre over `t` of the structure morphism of the closed subscheme of `Y` defined by `I`: both
are the fibred product of `I.subscheme ⟶ Y` and `Spec κ(t) ⟶ S` over `S`. -/
private def comapFiberHomeo {Y S : Scheme.{u}} (p : Y ⟶ S) (I : Y.IdealSheafData) (t : S) :
    (I.comap (p.fiberι t)).subscheme ≃ₜ (I.subschemeι ≫ p).fiber t :=
  (Scheme.IdealSheafData.comapIso I (p.fiberι t) ≪≫
    pullbackSymmetry (p.fiberι t) I.subschemeι ≪≫
      pullbackRightPullbackFstIso p (S.fromSpecResidueField t) I.subschemeι).hom.homeomorph

/-! ### Dimension and equidimensionality over a field -/

/-- The dimension function of the Chow situation on the spectrum of a field vanishes at closed
points, which is the hypothesis under which Tag 02QO is available for it. -/
private theorem fieldChowSituation_dimensionFunction_eq_zero_of_isClosed (k : Type u) [Field k] :
    ∀ t : (fieldChowSituation k).S, IsClosed ({t} : Set (fieldChowSituation k).S) →
      (fieldChowSituation k).dimensionFunction t = 0 :=
  fun t _ ↦ fieldChowSituation_dimensionFunction_eq_zero k t

/-- **Stacks Project, Tag 02QO.** For a scheme locally of finite type over a field, the
topological dimension of the integral closed subscheme attached to a point is the relative
dimension at that point. -/
public theorem topologicalKrullDim_closure_singleton_eq (k : Type u) [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p] (z : Y) :
    topologicalKrullDim (closure ({z} : Set Y)) =
      (relativeDimension (fieldChowSituation k).dimensionFunction p z).toNat := by
  let _ : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  have hgen : (integralComponentAt z).subschemeι.base
      (genericPoint (integralComponentAt z).subscheme) = z := by
    simpa [genericPointOf] using genericPointOf_integralComponentAt z
  have htop := topologicalKrullDim_eq_relativeDimension_toNat (fieldChowSituation k)
    (fieldChowSituation_dimensionFunction_eq_zero_of_isClosed k) p
    (integralComponentAt z).subschemeι (genericPoint (integralComponentAt z).subscheme)
    ((IrreducibleSpace.isIrreducible_univ _).isGenericPoint_genericPoint isClosed_univ)
  rwa [topologicalKrullDim_subscheme, coe_support_integralComponentAt, hgen] at htop

/-- Every irreducible component of a nonempty equidimensional scheme locally of finite type over
a field has the dimension of the whole scheme: by Tag 0A21 the local dimension at any point is
the dimension of some component, hence constant, and the dimension of the scheme is the supremum
of its local dimensions. -/
private theorem topologicalKrullDim_eq_of_mem_irreducibleComponents (k : Type u) [Field k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hEq : TopologicalSpace.Equidimensional Y) (hne : Nonempty Y)
    {Z : Set Y} (hZ : Z ∈ irreducibleComponents Y) :
    topologicalKrullDim Z = topologicalKrullDim Y := by
  let _ : Nonempty Y := hne
  obtain ⟨y⟩ := hne
  let W : irreducibleComponents Y :=
    ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
  have hlocal : ∀ x : Y, topologicalKrullDimAt Y x = topologicalKrullDim (W : Set Y) := by
    intro x
    obtain ⟨V, hV, -, hdim⟩ :=
      exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k Y p x
    rw [← hdim]
    exact hEq V hV W W.2
  have hdimY : topologicalKrullDim Y = topologicalKrullDim (W : Set Y) := by
    rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    simp only [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
    simp [hlocal]
  exact (hEq Z hZ W W.2).trans hdimY.symm

/-! ### Dimensions in a scheme-theoretic fibre -/

/-- The integral closed subscheme of a scheme-theoretic fibre attached to a point of dimension
`n` has topological dimension `n`, by Tag 02QO over the residue field of the base point. -/
private theorem topologicalKrullDim_closure_singleton_fiber {Y S : Scheme.{u}} (p : Y ⟶ S)
    [LocallyOfFiniteType p] (s : S) (n : ℕ) (z : p.fiber s)
    (hz : fiberPointDimension p s z = (n : ℤ)) :
    topologicalKrullDim (closure ({z} : Set (p.fiber s))) = (n : WithBot ℕ∞) := by
  have hz' : relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
      (p.fiberToSpecResidueField s) z = (n : ℤ) := hz
  rw [topologicalKrullDim_closure_singleton_eq (S.residueField s)
    (p.fiberToSpecResidueField s) z, hz']
  simp

/-- Let `W` be a closed subscheme of a scheme-theoretic fibre of `p` over `s` which is nonempty
and equidimensional of dimension `n`. Then every generic point of `W` has dimension `n` in that
fibre: the integral closed subscheme attached to such a point is an irreducible component of `W`,
hence of dimension `n`, and over the field `κ(s)` the dimension of an integral closed subscheme
is the relative dimension at its generic point. -/
private theorem fiberPointDimension_eq_of_equidimensional {Y S : Scheme.{u}} (p : Y ⟶ S)
    [LocallyOfFiniteType p] (s : S) (n : ℕ) (W : (p.fiber s).IdealSheafData)
    (hEq : TopologicalSpace.Equidimensional W.subscheme) (hne : Nonempty W.subscheme)
    (hdim : topologicalKrullDim W.subscheme = (n : WithBot ℕ∞))
    (ζ : genericPoints W.subscheme) :
    fiberPointDimension p s (W.subschemeι ζ.1) = (n : ℤ) := by
  have hlft : LocallyOfFiniteType (W.subschemeι ≫ p.fiberToSpecResidueField s) := inferInstance
  have hcomp := topologicalKrullDim_eq_of_mem_irreducibleComponents (S.residueField s)
    (W.subschemeι ≫ p.fiberToSpecResidueField s) hEq hne
    (Z := closure ({ζ.1} : Set W.subscheme)) ζ.2
  rw [hdim] at hcomp
  have hrelTop := topologicalKrullDim_closure_singleton_eq (S.residueField s)
    (W.subschemeι ≫ p.fiberToSpecResidueField s) ζ.1
  rw [hcomp] at hrelTop
  have hnat : (relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
      (W.subschemeι ≫ p.fiberToSpecResidueField s) ζ.1).toNat = n := by
    exact_mod_cast hrelTop.symm
  have hval : relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
      (W.subschemeι ≫ p.fiberToSpecResidueField s) ζ.1 = (n : ℤ) := by
    rw [← Int.toNat_of_nonneg (relativeDimension_fieldChowSituation_nonneg
      (S.residueField s) _ ζ.1), hnat]
  exact (relativeDimension_comp_closedImmersion
    (fieldChowSituation (S.residueField s)).dimensionFunction W.subschemeι
    (p.fiberToSpecResidueField s) ζ.1).symm.trans hval

/-! ### The spectrum of a discrete valuation ring -/

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A prime ideal of a discrete valuation ring is either zero or the maximal ideal: a nonzero
prime ideal is generated by an irreducible element, and every irreducible element of a discrete
valuation ring is a uniformizer. -/
private theorem eq_bot_or_eq_maximalIdeal (P : Ideal R) (hP : P.IsPrime) :
    P = ⊥ ∨ P = IsLocalRing.maximalIdeal R := by
  by_cases h0 : P = ⊥
  · exact Or.inl h0
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal P).1
  have ha0 : a ≠ 0 := by
    intro h
    exact h0 (by rw [ha, h]; simp)
  have hirr : Irreducible a :=
    ((Ideal.span_singleton_prime ha0).mp (by simpa [ha] using hP)).irreducible
  exact Or.inr (ha.trans
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer a).mp hirr).symm)

omit [IsDiscreteValuationRing R] in
/-- The generic point of the spectrum of a domain is its zero ideal. -/
private theorem genericPoint_eq_bot_primeSpectrum :
    genericPoint (Spec (.of R) : Scheme.{u}) = (⊥ : PrimeSpectrum R) := by
  simpa using genericPoint_eq_bot_of_affine (CommRingCat.of R)

/-- The spectrum of a discrete valuation ring has exactly two points: the generic point and the
closed point. -/
private theorem eq_genericPoint_or_eq_closedPoint (t : (Spec (.of R) : Scheme.{u})) :
    t = genericPoint (Spec (.of R) : Scheme.{u}) ∨ t = IsLocalRing.closedPoint R := by
  have hbot : (genericPoint (Spec (.of R) : Scheme.{u})).asIdeal = ⊥ :=
    congrArg PrimeSpectrum.asIdeal genericPoint_eq_bot_primeSpectrum
  rcases eq_bot_or_eq_maximalIdeal t.asIdeal t.isPrime with h | h
  · exact Or.inl (PrimeSpectrum.ext (h.trans hbot.symm))
  · exact Or.inr (PrimeSpectrum.ext h)

/-! ### Fibres over the two points of the spectrum of a discrete valuation ring -/

/-- **Stacks Project, Tag 0B2J (equidimensionality).** The fibre over the closed point of a
surjective morphism locally of finite type from an irreducible scheme to the spectrum of a
discrete valuation ring is equidimensional. -/
private theorem equidimensional_fiber_closedPoint {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R))
    [IrreducibleSpace Y] [LocallyOfFiniteType q] [Surjective q] :
    TopologicalSpace.Equidimensional (q.fiber (IsLocalRing.closedPoint R)) :=
  specialFiber_equidimensional q

/-- **Stacks Project, Tag 0B2J (equality of fibre dimensions).** The fibre over the closed point
of such a morphism has the dimension of the fibre over the generic point. -/
@[sga "6 X 7.14" "partial"]
private theorem topologicalKrullDim_fiber_closedPoint_eq_genericPoint {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of R)) [IrreducibleSpace Y] [LocallyOfFiniteType q] [Surjective q] :
    topologicalKrullDim (q.fiber (IsLocalRing.closedPoint R)) =
      topologicalKrullDim (q.fiber (genericPoint (Spec (.of R)))) := by
  have hbot : genericPoint (Spec (.of R) : Scheme.{u}) =
      (⟨⊥, inferInstance⟩ : PrimeSpectrum R) :=
    genericPoint_eq_bot_primeSpectrum.trans (PrimeSpectrum.ext rfl)
  rw [hbot]
  exact topologicalKrullDim_specialFiber_eq_genericFiber q

/-! ### The schematic closure of an integral subscheme of the generic fibre -/

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] (r : ℕ)

omit [IsDiscreteValuationRing R] [LocallyOfFiniteType f] in
/-- The scheme-theoretic image `\overline{Z} ⊆ X` of the reduced closure of a point `ξ` of the
generic fibre is irreducible: it is supported on the closure of the image of `ξ`. -/
private theorem irreducibleSpace_subscheme_specializationClosure
    (ξ : f.fiber (genericPoint (Spec (.of R)))) :
    IrreducibleSpace (specializationClosure f ξ).subscheme :=
  irreducibleSpace_subscheme_of_isIrreducible _ (by
    rw [coe_support_specializationClosure]
    exact isIrreducible_singleton.closure)

omit [IsDiscreteValuationRing R] [LocallyOfFiniteType f] in
/-- The scheme-theoretic image `\overline{Z}` is the closure of the image of `ξ`. -/
private theorem range_subschemeι_specializationClosure
    (ξ : f.fiber (genericPoint (Spec (.of R)))) :
    Set.range (specializationClosure f ξ).subschemeι.base =
      closure ({f.fiberι (genericPoint (Spec (.of R))) ξ} : Set X) := by
  rw [Scheme.IdealSheafData.range_subschemeι, coe_support_specializationClosure]

omit [LocallyOfFiniteType f] in
/-- The structure morphism `\overline{Z} ⟶ Spec R` is surjective once the special fibre of
`\overline{Z}` is nonempty: the image of `\overline{Z}` contains the image of `ξ`, which lies
over the generic point, and the image of `x`, which lies over the closed point, and a prime ideal
of a discrete valuation ring is either zero or maximal. -/
private theorem surjective_specializationClosure_comp
    (ξ : f.fiber (genericPoint (Spec (.of R)))) (x : f.fiber (IsLocalRing.closedPoint R))
    (hξx : f.fiberι (genericPoint (Spec (.of R))) ξ ⤳
      f.fiberι (IsLocalRing.closedPoint R) x) :
    Function.Surjective ((specializationClosure f ξ).subschemeι ≫ f).base := by
  have hmem : ∀ z ∈ closure ({f.fiberι (genericPoint (Spec (.of R))) ξ} : Set X),
      ∃ y, (specializationClosure f ξ).subschemeι.base y = z := fun z hz ↦ by
    rwa [← Set.mem_range, range_subschemeι_specializationClosure]
  have hover : ∀ (s : Spec (.of R)) (z : f.fiber s) (y : (specializationClosure f ξ).subscheme),
      (specializationClosure f ξ).subschemeι.base y = f.fiberι s z →
        ((specializationClosure f ξ).subschemeι ≫ f).base y = s := fun s z y hy ↦ by
    rw [Scheme.Hom.comp_apply, hy]
    exact base_fiberι f s z
  intro t
  rcases eq_genericPoint_or_eq_closedPoint t with rfl | rfl
  · obtain ⟨y, hy⟩ := hmem _ (subset_closure rfl)
    exact ⟨y, hover _ ξ y hy⟩
  · obtain ⟨y, hy⟩ := hmem _ (specializes_iff_mem_closure.mp hξx)
    exact ⟨y, hover _ x y hy⟩

/-- The special fibre `\overline{Z}_κ` is the fibre over the closed point of the structure
morphism `\overline{Z} ⟶ Spec R`. -/
private def specialFibreHomeo (ξ : f.fiber (genericPoint (Spec (.of R)))) :
    (specializationSpecialFibre f ξ).subscheme ≃ₜ
      ((specializationClosure f ξ).subschemeι ≫ f).fiber (IsLocalRing.closedPoint R) :=
  comapFiberHomeo f (specializationClosure f ξ) (IsLocalRing.closedPoint R)

omit [IsDiscreteValuationRing R] [LocallyOfFiniteType f] in
/-- The inverse image of `\overline{Z}` in the generic fibre is the integral closed subscheme
`Z` one started from: its support is the closure of `ξ` in `X_K`. -/
private theorem coe_support_comap_specializationClosure
    (ξ : f.fiber (genericPoint (Spec (.of R)))) :
    (((specializationClosure f ξ).comap
          (f.fiberι (genericPoint (Spec (.of R))))).support :
        Set (f.fiber (genericPoint (Spec (.of R))))) =
      closure ({ξ} : Set (f.fiber (genericPoint (Spec (.of R))))) := by
  have hemb := (f.fiberι (genericPoint (Spec (.of R)))).isEmbedding
  rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
    coe_support_specializationClosure]
  simpa only [Set.image_singleton] using
    (hemb.closure_eq_preimage_closure_image
      ({ξ} : Set (f.fiber (genericPoint (Spec (.of R)))))).symm

omit [IsDiscreteValuationRing R] in
/-- The fibre over the generic point of `\overline{Z} ⟶ Spec R` has dimension `r`: it is the
integral closed subscheme `Z` of `X_K` with generic point `ξ`, whose dimension is the relative
dimension of `ξ` over `κ(η)`, namely `r`. -/
private theorem topologicalKrullDim_fiber_genericPoint
    (ξ : f.fiber (genericPoint (Spec (.of R))))
    (hξ : fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ)) :
    topologicalKrullDim (((specializationClosure f ξ).subschemeι ≫ f).fiber
      (genericPoint (Spec (.of R)))) = (r : WithBot ℕ∞) := by
  rw [← (comapFiberHomeo f (specializationClosure f ξ)
      (genericPoint (Spec (.of R)))).isHomeomorph.topologicalKrullDim_eq,
    topologicalKrullDim_subscheme, coe_support_comap_specializationClosure]
  exact topologicalKrullDim_closure_singleton_fiber f (genericPoint (Spec (.of R))) r ξ hξ

/-! ### The dimension of the special fibre of the schematic closure -/

omit [LocallyOfFiniteType f] in
/-- The special fibre `\overline{Z}_κ` is nonempty: the point `x`, lying in the closure of the
image of `ξ`, belongs to it. -/
private theorem nonempty_subscheme_specializationSpecialFibre
    (ξ : f.fiber (genericPoint (Spec (.of R)))) (x : f.fiber (IsLocalRing.closedPoint R))
    (hξx : f.fiberι (genericPoint (Spec (.of R))) ξ ⤳
      f.fiberι (IsLocalRing.closedPoint R) x) :
    Nonempty (specializationSpecialFibre f ξ).subscheme := by
  have hx : x ∈ Set.range (specializationSpecialFibre f ξ).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι, specializationSpecialFibre,
      Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
      coe_support_specializationClosure]
    exact specializes_iff_mem_closure.mp hξx
  obtain ⟨y, -⟩ := hx
  exact ⟨y⟩

/-- `\overline{Z}_κ` is equidimensional of dimension `r`: it is the fibre over the closed point of
the morphism `\overline{Z} ⟶ Spec R`, a surjective morphism locally of finite type from the
irreducible scheme `\overline{Z}`, so by Tag 0B2J it is equidimensional and has the dimension of
the fibre over the generic point, and that fibre is `Z`. -/
private theorem equidimensional_and_topologicalKrullDim_specializationSpecialFibre
    (ξ : f.fiber (genericPoint (Spec (.of R))))
    (hξ : fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ))
    (x : f.fiber (IsLocalRing.closedPoint R))
    (hξx : f.fiberι (genericPoint (Spec (.of R))) ξ ⤳
      f.fiberι (IsLocalRing.closedPoint R) x) :
    TopologicalSpace.Equidimensional (specializationSpecialFibre f ξ).subscheme ∧
      topologicalKrullDim (specializationSpecialFibre f ξ).subscheme = (r : WithBot ℕ∞) := by
  have hirr := irreducibleSpace_subscheme_specializationClosure f ξ
  have hsurj : Surjective ((specializationClosure f ξ).subschemeι ≫ f) :=
    ⟨surjective_specializationClosure_comp f ξ x hξx⟩
  refine ⟨TopologicalSpace.Equidimensional.of_homeomorph (specialFibreHomeo f ξ)
    (equidimensional_fiber_closedPoint ((specializationClosure f ξ).subschemeι ≫ f)), ?_⟩
  rw [(specialFibreHomeo f ξ).isHomeomorph.topologicalKrullDim_eq,
    topologicalKrullDim_fiber_closedPoint_eq_genericPoint
      ((specializationClosure f ξ).subschemeι ≫ f),
    topologicalKrullDim_fiber_genericPoint f r ξ hξ]

/-- Let `R` be a discrete valuation ring with fraction field `K` and residue field `κ`, let
`f : X ⟶ Spec R` be locally of finite type, and let `Z ⊆ X_K` be the integral closed subscheme
of the generic fibre with generic point `ξ`, of dimension `r`. Suppose the special fibre
`\overline{Z}_κ` of the scheme-theoretic image `\overline{Z}` of `Z` is nonempty, as witnessed by
a point `x` of `X_κ` whose image in `X` is a specialization of the image of `ξ`. Then every
generic point of `\overline{Z}_κ` again has dimension `r`.

The scheme `\overline{Z}` is irreducible with generic point the image of `ξ`, and it surjects
onto `Spec R` because it contains the image of `x` as well; its fibre over the generic point is
`Z` and its fibre over the closed point is `\overline{Z}_κ`. So the assertion is that the special
fibre of a surjective morphism locally of finite type from an irreducible scheme to the spectrum
of a discrete valuation ring is equidimensional of the dimension of the generic fibre, which is
Tag 0B2J. -/
@[sga "6 X 7.14" "partial"]
theorem fiberPointDimension_specializationSpecialFibre
    (ξ : f.fiber (genericPoint (Spec (.of R))))
    (hξ : fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ))
    (x : f.fiber (IsLocalRing.closedPoint R))
    (hξx : f.fiberι (genericPoint (Spec (.of R))) ξ ⤳
      f.fiberι (IsLocalRing.closedPoint R) x)
    (ζ : genericPoints (specializationSpecialFibre f ξ).subscheme) :
    fiberPointDimension f (IsLocalRing.closedPoint R)
      ((specializationSpecialFibre f ξ).subschemeι ζ.1) = (r : ℤ) :=
  fiberPointDimension_eq_of_equidimensional f (IsLocalRing.closedPoint R) r
    (specializationSpecialFibre f ξ)
    (equidimensional_and_topologicalKrullDim_specializationSpecialFibre f r ξ hξ x hξx).1
    (nonempty_subscheme_specializationSpecialFibre f ξ x hξx)
    (equidimensional_and_topologicalKrullDim_specializationSpecialFibre f r ξ hξ x hξx).2 ζ

end Stacks.Chow

end
