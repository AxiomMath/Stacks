module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickening

/-!
# The de Rham differential on the sheaf of divided power differentials, and the third map `q₁₂`

Let `(T, J, δ)` be a divided power scheme over a scheme `Y`, let `Ω_{T/Y,δ}` be its sheaf of
divided power differentials with universal divided power derivation `d`, and let `Ω²_{T/Y,δ}` be
its second exterior power, as in
`StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickening`.  This module constructs the
**degree-one divided power de Rham differential on the sheaf**

`d : Ω_{T/Y,δ} → Ω²_{T/Y,δ}`,

an additive family of maps on sections, compatible with restriction, obeying

`d (a ω) = a (d ω) + (d a) ∧ ω` and `d (d a) = 0`,

and uses it to construct the third of the three maps `𝒪_{T'} → 𝒪_{T''}` of [Stacks, Tag 07J3],

`q₁₂ (f, ω) = (f, d f, ω, d ω)`,

out of the first-order universal thickening `T'` of
`StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickenings`.  It is a homomorphism of
presheaves of rings, it is compatible with the divided power structures `δ'` and `δ''`, and it
satisfies the two remaining composition relations of the source,

`q₁ = q₁₂ ∘ p₀` and `q₂ = q₁₂ ∘ p₁`.

## Main definitions

* `Crystalline.DpJet` — the sections of the *sheaf of jets* `Ω_{T/Y,δ} ⊕ Ω²_{T/Y,δ}`, carrying
  the twisted `𝒪_T`-module structure `a (ω, η) = (a ω, a η + (d a) ∧ ω)`, with
  `Crystalline.dpJetSheaf` the resulting sheaf of `𝒪_T`-modules.
* `Crystalline.dpJetTheta` — the divided power derivation `a ↦ (d a, 0)` into the jets, and
  `Crystalline.dpJetDerivation` its packaging as a
  `Crystalline.DividedPowerSchemeDerivation`.
* `Crystalline.dpJetLift` — the map of sheaves of modules `Ω_{T/Y,δ} → ` jets through which that
  derivation factors, namely `ω ↦ (ω, d ω)`.
* `Crystalline.dpDeRham` — **the de Rham differential `d : Ω_{T/Y,δ} → Ω²_{T/Y,δ}`** on sections,
  the second coordinate of `Crystalline.dpJetLift`.
* `Crystalline.secondOrderThickeningQ₁₂` — the map `q₁₂ (f, ω) = (f, d f, ω, d ω)`.

## Main results

* `Crystalline.dpDeRham_add`, `dpDeRham_smul` and `dpDeRham_naturality` — `d` is additive, obeys
  the Leibniz rule `d (a ω) = a (d ω) + (d a) ∧ ω`, and commutes with restriction.
* `Crystalline.dpJetLift_unique` — the sense in which `d` is *the* de Rham differential: the map
  `ω ↦ (ω, d ω)` is the only morphism of sheaves of modules carrying every exact differential
  `d a` to the jet `(d a, 0)`.  (That `d` is the only additive, natural family obeying the two
  displayed rules is true as well — two of them differ by a linear map of sheaves vanishing on
  the exact differentials, which generate locally — but is not proved here.)
* `Crystalline.dpDeRham_d` — `d (d a) = 0`: the de Rham differential kills every exact
  differential.
* `Crystalline.dpDeRham_dpow_smul` — the divided power form of the Leibniz rule,
  `d (δ_{k+1}(a) ω) = δ_{k+1}(a) (d ω) + δ_k(a) ((d a) ∧ ω)`, which is the identity the
  divided power compatibility of `q₁₂` rests on.
* `Crystalline.secondOrderThickeningQ₁₂_isDPMorphism` — `q₁₂` is compatible with the divided
  power structures on `J'` and `J''`.
* `Crystalline.secondOrderThickeningQ₁_eq_Q₁₂_comp_P₀` and
  `Crystalline.secondOrderThickeningQ₂_eq_Q₁₂_comp_P₁` — the two composition relations.

## Implementation notes

**Why the sheaf of jets.**  The de Rham differential is not a morphism of sheaves of modules: it
is only additive, with the Leibniz correction `(d a) ∧ ω`.  So it cannot be obtained from a
sectionwise construction by the universal property of the sheafification, which produces
`𝒪_T`-linear maps.  The device used here is that the *graph* of `d` is linear for a twisted
module structure: on `Ω_{T/Y,δ} ⊕ Ω²_{T/Y,δ}` the operation

`a (ω, η) = (a ω, a η + (d a) ∧ ω)`

is an `𝒪_T`-module structure — associativity is the Leibniz rule for `d` on functions and
unitality is `d 1 = 0` — and for it the map `ω ↦ (ω, d ω)` is linear, because
`a (ω, d ω) = (a ω, d (a ω))`.  Those jets are a *sheaf* of modules, since additively they are
the product of two sheaves, so the universal property of the universal divided power derivation,
`Crystalline.universalDPSchemeDerivation_isUniversal`, applies: the derivation
`a ↦ (d a, 0)`, which is one because the exterior product is antisymmetric
(`(d a) ∧ (d b) + (d b) ∧ (d a) = 0`) and because `(d (δ_n a)) ∧ (d a) = 0`, factors uniquely
through `Ω_{T/Y,δ}`.  The first coordinate of that factorisation is the identity — again by the
uniqueness half of the universal property — so its second coordinate is a map
`Ω_{T/Y,δ} → Ω²_{T/Y,δ}` whose Leibniz rule and naturality are the linearity and the naturality
of the factorisation, and which kills exact differentials because the derivation it came from has
vanishing second coordinate.  That last property, `d ∘ d = 0`, is exactly what the relation
`q₂ = q₁₂ ∘ p₁` consumes.

**Why not the ring-level divided power de Rham complex.**  `Crystalline.dividedPowerDeRhamComplex`
is the de Rham complex of a divided power *ring*, and `Ω_{T/Y,δ}` is the sheafification of a
presheaf of such modules, so a sectionwise differential would land in the sectionwise second
exterior power of the *presheaf*, not of the sheaf, and would still have to be transported across
the sheafification — which is the step that the twisted module structure above is what makes
possible.  Nothing of the ring-level complex is used here.

**What is not proved.**  Only degrees zero and one of the divided power de Rham complex of
`Ω_{T/Y,δ}` appear: `d : 𝒪_T → Ω_{T/Y,δ}` is `Crystalline.sheafApp` and
`d : Ω_{T/Y,δ} → Ω²_{T/Y,δ}` is `Crystalline.dpDeRham`, and the only square-zero statement proved
is `Crystalline.dpDeRham_d`, the composite of those two.  The higher exterior powers, the higher
differentials and the complex itself are not constructed.  The thickening is not realized as a
*scheme* in this module either; that realization, and the statement that `(U, T'', δ'')` is an
object of `CRIS(X/S)`, are `Crystalline.secondOrderThickeningScheme` and
`Crystalline.GlobalCrystallineSituation.secondOrderThickeningObject` of
`StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningScheme`, which realizes `T''`
over the *first-order* thickening `T'` rather than over `T`:
`Stacks.Thickenings.squareZeroExtension_realization` wants an ideal of square zero, and the ideal
of `T → T''` has vanishing cube but not vanishing square, as
`StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningOrder` records
(`Crystalline.secondOrderThickening_ker_cube`,
`Crystalline.secondOrderThickening_ker_sq_eq_bot_iff`).

## References

* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry

universe u

namespace Crystalline

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-! ### The sheaf of jets of divided power differentials -/

/-- The divided power chain rule for the universal derivation on sections. -/
private theorem dpDerivationHom_dpow_succ (W : (Opens ↑T.scheme)ᵒᵖ) (k : ℕ)
    {a : ↑(T.scheme.sheaf.obj.obj W)} (ha : a ∈ sectionIdeal T.scheme.sheaf T.ideal W) :
    dpDerivationHom T Y f W ((T.dividedPowers.dividedPowers W).dpow (k + 1) a) =
      (T.dividedPowers.dividedPowers W).dpow k a • dpDerivationHom T Y f W a :=
  sheafApp_dpow T Y f W.unop k a ha

/-- The square-zero coordinate of a positive divided power in the first-order thickening. -/
private theorem sqZeroExtSnd_dpow_succ (W : (Opens ↑T.scheme)ᵒᵖ) (k : ℕ)
    {x : ↑((firstOrderThickeningPresheaf T Y f).obj W)}
    (hx : x ∈ firstOrderThickeningIdeal T Y f W) :
    sqZeroExtSnd ((firstOrderThickeningDividedPowers T Y f W).dpow (k + 1) x) =
      (T.dividedPowers.dividedPowers W).dpow k (sqZeroExtFst x) • sqZeroExtSnd x :=
  (congrArg sqZeroExtSnd (firstOrderThickeningDividedPowers_dpow_succ T Y f W k hx)).trans
    (sqZeroExtSnd_mk _ _)

/-- **The sections of the sheaf of jets.**  A jet over an open is a divided power differential
together with a divided power two-form; the two coordinates are kept in a structure so that the
twisted module structure of `Crystalline.DpJet.instModule` does not compete with the
componentwise one on the product. -/
public structure DpJet (W : (Opens ↑T.scheme)ᵒᵖ) where
  /-- The two coordinates of a jet. -/
  coords : ↑((dpDifferentialsModules T Y f).obj W) ×
    ↑((dpSecondExteriorModules T Y f).obj W)

section Coords

variable {T Y f}

/-- A jet is its pair of coordinates. -/
public def DpJet.equiv (W : (Opens ↑T.scheme)ᵒᵖ) :
    DpJet T Y f W ≃ ↑((dpDifferentialsModules T Y f).obj W) ×
      ↑((dpSecondExteriorModules T Y f).obj W) where
  toFun := DpJet.coords
  invFun := DpJet.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

/-- The jets form an additive group, transported from the product of their coordinates. -/
public instance (W : (Opens ↑T.scheme)ᵒᵖ) : AddCommGroup (DpJet T Y f W) :=
  Equiv.addCommGroup (DpJet.equiv W)

/-- The jet with the given two coordinates. -/
public def dpJetMk {W : (Opens ↑T.scheme)ᵒᵖ} (ω : ↑((dpDifferentialsModules T Y f).obj W))
    (η : ↑((dpSecondExteriorModules T Y f).obj W)) : DpJet T Y f W := ⟨(ω, η)⟩

/-- The differential coordinate of a jet. -/
public def dpJetFst {W : (Opens ↑T.scheme)ᵒᵖ} (x : DpJet T Y f W) :
    ↑((dpDifferentialsModules T Y f).obj W) := x.coords.1

/-- The two-form coordinate of a jet. -/
public def dpJetSnd {W : (Opens ↑T.scheme)ᵒᵖ} (x : DpJet T Y f W) :
    ↑((dpSecondExteriorModules T Y f).obj W) := x.coords.2

/-- The differential coordinate of `dpJetMk ω η` is `ω`. -/
@[simp] public theorem dpJetFst_mk {W : (Opens ↑T.scheme)ᵒᵖ}
    (ω : ↑((dpDifferentialsModules T Y f).obj W))
    (η : ↑((dpSecondExteriorModules T Y f).obj W)) :
    dpJetFst (dpJetMk ω η) = ω := rfl

/-- The two-form coordinate of `dpJetMk ω η` is `η`. -/
@[simp] public theorem dpJetSnd_mk {W : (Opens ↑T.scheme)ᵒᵖ}
    (ω : ↑((dpDifferentialsModules T Y f).obj W))
    (η : ↑((dpSecondExteriorModules T Y f).obj W)) :
    dpJetSnd (dpJetMk ω η) = η := rfl

/-- Two jets with the same coordinates are equal. -/
public theorem dpJet_ext {W : (Opens ↑T.scheme)ᵒᵖ} {x y : DpJet T Y f W}
    (h₁ : dpJetFst x = dpJetFst y) (h₂ : dpJetSnd x = dpJetSnd y) : x = y :=
  (DpJet.equiv W).injective (Prod.ext h₁ h₂)

/-- The differential coordinate is additive. -/
@[simp] public theorem dpJetFst_add {W : (Opens ↑T.scheme)ᵒᵖ} (x y : DpJet T Y f W) :
    dpJetFst (x + y) = dpJetFst x + dpJetFst y := rfl

/-- The two-form coordinate is additive. -/
@[simp] public theorem dpJetSnd_add {W : (Opens ↑T.scheme)ᵒᵖ} (x y : DpJet T Y f W) :
    dpJetSnd (x + y) = dpJetSnd x + dpJetSnd y := rfl

/-- The differential coordinate of the zero jet is zero. -/
@[simp] public theorem dpJetFst_zero {W : (Opens ↑T.scheme)ᵒᵖ} :
    dpJetFst (0 : DpJet T Y f W) = 0 := rfl

/-- The two-form coordinate of the zero jet is zero. -/
@[simp] public theorem dpJetSnd_zero {W : (Opens ↑T.scheme)ᵒᵖ} :
    dpJetSnd (0 : DpJet T Y f W) = 0 := rfl

/-- **The twisted scalar multiplication on jets**, shifted in the two-form coordinate by the
exterior product of the differential of the scalar with the differential coordinate. -/
public instance (W : (Opens ↑T.scheme)ᵒᵖ) :
    SMul ↑(T.scheme.sheaf.obj.obj W) (DpJet T Y f W) :=
  ⟨fun a x => dpJetMk (a • dpJetFst x)
    (a • dpJetSnd x +
      bilinearApp (dpWedge T Y f) W (dpDerivationHom T Y f W a) (dpJetFst x))⟩

/-- The twisted scalar multiplication is the ordinary one on the differential coordinate. -/
@[simp] public theorem dpJetFst_smul {W : (Opens ↑T.scheme)ᵒᵖ}
    (a : ↑(T.scheme.sheaf.obj.obj W)) (x : DpJet T Y f W) :
    dpJetFst (a • x) = a • dpJetFst x := rfl

/-- The twisted scalar multiplication on the two-form coordinate: `a • (ω, η)` has two-form
coordinate `a • η + (d a) ∧ ω`. -/
@[simp] public theorem dpJetSnd_smul {W : (Opens ↑T.scheme)ᵒᵖ}
    (a : ↑(T.scheme.sheaf.obj.obj W)) (x : DpJet T Y f W) :
    dpJetSnd (a • x) = a • dpJetSnd x +
      bilinearApp (dpWedge T Y f) W (dpDerivationHom T Y f W a) (dpJetFst x) := rfl

/-- **The jets are a module for the twisted multiplication**: associativity is the Leibniz rule
for the universal divided power derivation and unitality is `d 1 = 0`. -/
public instance (W : (Opens ↑T.scheme)ᵒᵖ) :
    Module ↑(T.scheme.sheaf.obj.obj W) (DpJet T Y f W) where
  one_smul x := by
    refine dpJet_ext (one_smul _ _) ?_
    rw [dpJetSnd_smul, one_smul, show dpDerivationHom T Y f W 1 = 0 from
      sheafApp_one T Y f W.unop, bilinearApp_zero_left, add_zero]
  mul_smul a b x := by
    refine dpJet_ext (mul_smul _ _ _) ?_
    simp only [dpJetSnd_smul, dpJetFst_smul, dpDerivationHom_mul, bilinearApp_add_left,
      bilinearApp_smul_left, bilinearApp_smul_right, smul_add, mul_smul]
    abel
  smul_zero a := by
    refine dpJet_ext (smul_zero _) ?_
    rw [dpJetSnd_smul, dpJetFst_zero, dpJetSnd_zero, smul_zero, bilinearApp_zero_right, add_zero]
  smul_add a x y := by
    refine dpJet_ext (smul_add _ _ _) ?_
    simp only [dpJetSnd_smul, dpJetFst_add, dpJetSnd_add, smul_add, bilinearApp_add_right]
    abel
  add_smul a b x := by
    refine dpJet_ext (add_smul _ _ _) ?_
    simp only [dpJetSnd_smul, dpJetSnd_add, add_smul, map_add, LinearMap.add_apply]
    abel
  zero_smul x := by
    refine dpJet_ext (zero_smul _ _) ?_
    rw [dpJetSnd_smul, map_zero, bilinearApp_zero_left, zero_smul, add_zero, dpJetSnd_zero]

/-- **The restriction map on jets**: restrict both coordinates. -/
public def dpJetRestrict {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W') :
    DpJet T Y f W →+ DpJet T Y f W' :=
  AddMonoidHom.mk'
    (fun x => dpJetMk ((dpDifferentialsModules T Y f).map i (dpJetFst x))
      ((dpSecondExteriorModules T Y f).map i (dpJetSnd x)))
    (fun _ _ => dpJet_ext (map_add _ _ _) (map_add _ _ _))

/-- Restricting a jet restricts its differential coordinate. -/
@[simp] public theorem dpJetFst_restrict {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W')
    (x : DpJet T Y f W) :
    dpJetFst (dpJetRestrict i x) = (dpDifferentialsModules T Y f).map i (dpJetFst x) := rfl

/-- Restricting a jet restricts its two-form coordinate. -/
@[simp] public theorem dpJetSnd_restrict {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W')
    (x : DpJet T Y f W) :
    dpJetSnd (dpJetRestrict i x) = (dpSecondExteriorModules T Y f).map i (dpJetSnd x) := rfl

/-- **The restriction maps of the jets are semilinear** for the twisted multiplication, because
the universal divided power derivation and the exterior product both commute with restriction. -/
public theorem dpJetRestrict_smul {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W')
    (a : ↑(T.scheme.sheaf.obj.obj W)) (x : DpJet T Y f W) :
    dpJetRestrict i (a • x) = (T.scheme.sheaf.obj.map i).hom a • dpJetRestrict i x := by
  refine dpJet_ext ?_ ?_
  · exact (dpDifferentialsModules T Y f).map_smul i a (dpJetFst x)
  · rw [dpJetSnd_restrict, dpJetSnd_smul, dpJetSnd_smul, dpJetFst_restrict, map_add,
      show (dpSecondExteriorModules T Y f).map i (a • dpJetSnd x) =
          (T.scheme.sheaf.obj.map i).hom a • (dpSecondExteriorModules T Y f).map i (dpJetSnd x)
        from (dpSecondExteriorModules T Y f).map_smul i a (dpJetSnd x),
      show (dpSecondExteriorModules T Y f).map i
            (bilinearApp (dpWedge T Y f) W (dpDerivationHom T Y f W a) (dpJetFst x)) =
          bilinearApp (dpWedge T Y f) W'
            ((dpDifferentialsModules T Y f).map i (dpDerivationHom T Y f W a))
            ((dpDifferentialsModules T Y f).map i (dpJetFst x))
        from (dpWedge T Y f).naturality i _ _,
      dpDerivationHom_naturality]
    rfl

end Coords

/-- The jets as a presheaf of abelian groups. -/
public def dpJetAbPresheaf : (Opens ↑T.scheme)ᵒᵖ ⥤ Ab.{u} where
  obj W := AddCommGrpCat.of (DpJet T Y f W)
  map i := AddCommGrpCat.ofHom (dpJetRestrict i)
  map_id W := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => dpJet_ext ?_ ?_)
    · exact PresheafOfModules.map_id_apply (dpDifferentialsModules T Y f) _ _
    · exact PresheafOfModules.map_id_apply (dpSecondExteriorModules T Y f) _ _
  map_comp i j := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => dpJet_ext ?_ ?_)
    · exact map_comp_apply _ i j _
    · exact map_comp_apply _ i j _

/-- The twisted module structure on the sections of the presheaf of jets, named so that instance
resolution finds it through the definition of `Crystalline.dpJetAbPresheaf`. -/
public instance dpJetAbModule (W : (Opens ↑T.scheme)ᵒᵖ) :
    Module (dpSectionRing T W) ↑((dpJetAbPresheaf T Y f).obj W) :=
  inferInstanceAs (Module ↑(T.scheme.sheaf.obj.obj W) (DpJet T Y f W))

/-- **The jets as a presheaf of `𝒪_T`-modules.** -/
public def dpJetModules :
    PresheafOfModules.{u} (T.scheme.sheaf.obj ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.ofPresheaf (dpJetAbPresheaf T Y f)
    (fun _ _ i a x => dpJetRestrict_smul i a x)

/-- **The jets are a sheaf**, because additively they are the product of the two sheaves
`Ω_{T/Y,δ}` and `Ω²_{T/Y,δ}`: a compatible family of jets glues coordinatewise. -/
public theorem isSheaf_dpJetAbPresheaf : TopCat.Presheaf.IsSheaf (dpJetAbPresheaf T Y f) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have h₁ : TopCat.Presheaf.IsCompatible (dpDifferentialsModules T Y f).presheaf U
      (fun i => dpJetFst (sf i)) := fun i j => congrArg dpJetFst (hsf i j)
  have h₂ : TopCat.Presheaf.IsCompatible (dpSecondExteriorModules T Y f).presheaf U
      (fun i => dpJetSnd (sf i)) := fun i j => congrArg dpJetSnd (hsf i j)
  obtain ⟨ω, hω, hωU⟩ := (dpDifferentialsSheaf T Y f).isSheaf.isSheafUniqueGluing U _ h₁
  obtain ⟨η, hη, hηU⟩ := (dpSecondExteriorPower T Y f).isSheaf.isSheafUniqueGluing U _ h₂
  refine ⟨dpJetMk ω η, fun i => dpJet_ext ?_ ?_, ?_⟩
  · exact (congrArg ((dpDifferentialsModules T Y f).map (Opens.leSupr U i).op)
      (dpJetFst_mk ω η)).trans (hω i)
  · exact (congrArg ((dpSecondExteriorModules T Y f).map (Opens.leSupr U i).op)
      (dpJetSnd_mk ω η)).trans (hη i)
  · intro s hs
    refine dpJet_ext ?_ ?_
    · exact (hωU _ fun i => congrArg dpJetFst (hs i)).trans (dpJetFst_mk ω η).symm
    · exact (hηU _ fun i => congrArg dpJetSnd (hs i)).trans (dpJetSnd_mk ω η).symm

/-- **The sheaf of jets `Ω_{T/Y,δ} ⊕ Ω²_{T/Y,δ}`**, with the twisted `𝒪_T`-module structure. -/
public def dpJetSheaf : T.scheme.Modules :=
  ⟨dpJetModules T Y f, isSheaf_dpJetAbPresheaf T Y f⟩

/-! ### The divided power derivation into the jets -/

/-- **The derivation `a ↦ (d a, 0)` into the jets.** -/
public def dpJetTheta (W : (Opens ↑T.scheme)ᵒᵖ) (a : ↑(T.scheme.sheaf.obj.obj W)) :
    DpJet T Y f W :=
  dpJetMk (dpDerivationHom T Y f W a) 0

/-- The differential coordinate of `(d a, 0)` is `d a`. -/
@[simp] public theorem dpJetFst_theta (W : (Opens ↑T.scheme)ᵒᵖ)
    (a : ↑(T.scheme.sheaf.obj.obj W)) :
    dpJetFst (dpJetTheta T Y f W a) = dpDerivationHom T Y f W a := rfl

/-- The two-form coordinate of `(d a, 0)` is zero. -/
@[simp] public theorem dpJetSnd_theta (W : (Opens ↑T.scheme)ᵒᵖ)
    (a : ↑(T.scheme.sheaf.obj.obj W)) : dpJetSnd (dpJetTheta T Y f W a) = 0 := rfl

/-- The derivation into the jets is additive. -/
public theorem dpJetTheta_add (W : (Opens ↑T.scheme)ᵒᵖ) (a b : ↑(T.scheme.sheaf.obj.obj W)) :
    dpJetTheta T Y f W (a + b) = dpJetTheta T Y f W a + dpJetTheta T Y f W b :=
  dpJet_ext (map_add _ _ _) (add_zero _).symm

/-- **The Leibniz rule for the derivation into the jets**, for the twisted multiplication: the
two-form coordinates cancel because the exterior product is antisymmetric. -/
public theorem dpJetTheta_mul (W : (Opens ↑T.scheme)ᵒᵖ) (a b : ↑(T.scheme.sheaf.obj.obj W)) :
    dpJetTheta T Y f W (a * b) = a • dpJetTheta T Y f W b + b • dpJetTheta T Y f W a := by
  refine dpJet_ext (dpDerivationHom_mul T Y f W a b) ?_
  simp only [dpJetSnd_add, dpJetSnd_smul, dpJetSnd_theta, dpJetFst_theta, smul_zero, zero_add]
  exact (dpWedge_add_swap T Y f W _ _).symm

/-- The derivation into the jets commutes with restriction. -/
public theorem dpJetTheta_naturality {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W')
    (a : ↑(T.scheme.sheaf.obj.obj W)) :
    dpJetRestrict i (dpJetTheta T Y f W a) =
      dpJetTheta T Y f W' ((T.scheme.sheaf.obj.map i).hom a) :=
  dpJet_ext (dpDerivationHom_naturality T Y f i a) (map_zero _)

/-- The derivation into the jets kills the sections coming from the base. -/
public theorem dpJetTheta_base (W : T.scheme.Opens) {a : Γ(T.scheme, W)}
    (ha : a ∈ baseSections T Y f W) : dpJetTheta T Y f (op W) a = 0 :=
  dpJet_ext (sheafApp_base T Y f W ha) rfl

/-- **The exterior product of the differential of a divided power of a section with the
differential of the section vanishes**: in degree zero because `d 1 = 0`, and in positive degree
because the divided power chain rule makes it a multiple of `(d a) ∧ (d a)`. -/
public theorem dpWedge_dpow_self (W : (Opens ↑T.scheme)ᵒᵖ) (n : ℕ)
    {a : ↑(T.scheme.sheaf.obj.obj W)} (ha : a ∈ sectionIdeal T.scheme.sheaf T.ideal W) :
    bilinearApp (dpWedge T Y f) W
        (dpDerivationHom T Y f W ((T.dividedPowers.dividedPowers W).dpow n a))
        (dpDerivationHom T Y f W a) = 0 := by
  match n with
  | 0 =>
      rw [(T.dividedPowers.dividedPowers W).dpow_zero ha,
        show dpDerivationHom T Y f W 1 = 0 from sheafApp_one T Y f W.unop,
        bilinearApp_zero_left]
  | k + 1 =>
      rw [dpDerivationHom_dpow_succ T Y f W k ha, bilinearApp_smul_left, bilinearApp_apply,
        dpWedge_self, smul_zero]

/-- **The divided power chain rule for the derivation into the jets.** -/
public theorem dpJetTheta_dpow (W : (Opens ↑T.scheme)ᵒᵖ) (n : ℕ)
    (a : ↑(T.scheme.sheaf.obj.obj W)) (ha : a ∈ sectionIdeal T.scheme.sheaf T.ideal W) :
    dpJetTheta T Y f W ((T.dividedPowers.dividedPowers W).dpow (n + 1) a) =
      (T.dividedPowers.dividedPowers W).dpow n a • dpJetTheta T Y f W a := by
  refine dpJet_ext ?_ ?_
  · rw [dpJetFst_theta, dpJetFst_smul, dpJetFst_theta]
    exact dpDerivationHom_dpow_succ T Y f W n ha
  · rw [dpJetSnd_theta, dpJetSnd_smul, dpJetSnd_theta, dpJetFst_theta, smul_zero, zero_add,
      dpWedge_dpow_self T Y f W n ha]

/-- **The derivation into the jets as a divided power derivation of `𝒪_T` over `Y`.** -/
public def dpJetDerivation : DividedPowerSchemeDerivation T Y f (dpJetSheaf T Y f) where
  app W a := dpJetTheta T Y f (op W) a
  naturality i x := dpJetTheta_naturality T Y f i.op x
  dividedPowerDerivation W V h :=
    { toDerivation :=
        Derivation.mk'
          (AddMonoidHom.toIntLinearMap
            (AddMonoidHom.mk' (fun a => dpJetTheta T Y f (op W) a)
              (dpJetTheta_add T Y f (op W))))
          (dpJetTheta_mul T Y f (op W))
      map_ringHom' a := dpJetTheta_base T Y f W (appLE_mem_baseSections T Y f W V h a)
      map_dpow' n hn x hx := by
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        exact dpJetTheta_dpow T Y f (op W) k x hx }
  dividedPowerDerivation_apply _ _ _ _ := rfl

/-! ### The de Rham differential on the sheaf of divided power differentials -/

/-- The differential coordinate of a jet, as a linear map of the sections. -/
public def dpJetFstLin (W : (Opens ↑T.scheme)ᵒᵖ) :
    ↑((dpJetModules T Y f).obj W) →ₗ[dpSectionRing T W]
      ↑((dpDifferentialsModules T Y f).obj W) where
  toFun x := dpJetFst x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The differential coordinate, as a morphism of presheaves of modules. -/
public def dpJetFstPresheafHom : dpJetModules T Y f ⟶ dpDifferentialsModules T Y f where
  app W := ModuleCat.homEquiv.symm (dpJetFstLin T Y f W)
  naturality _ := rfl

/-- **The projection of the jets onto `Ω_{T/Y,δ}`**, as a morphism of sheaves of modules.  It is
linear for the twisted multiplication because the twist only affects the two-form coordinate. -/
public def dpJetFstHom : dpJetSheaf T Y f ⟶ dpDifferentialsSheaf T Y f :=
  ⟨dpJetFstPresheafHom T Y f⟩

/-- On sections, the projection of the jets onto `Ω_{T/Y,δ}` is the differential coordinate. -/
@[simp] public theorem dpJetFstHom_val_app (W : (Opens ↑T.scheme)ᵒᵖ) (x : DpJet T Y f W) :
    (dpJetFstHom T Y f).val.app W x = dpJetFst x := rfl

/-- **The factorisation of the derivation into the jets through `Ω_{T/Y,δ}`**, supplied by the
universal property of the universal divided power derivation. -/
public def dpJetLift : dpDifferentialsSheaf T Y f ⟶ dpJetSheaf T Y f :=
  (universalDPSchemeDerivation_isUniversal T Y f (dpJetSheaf T Y f)
    (dpJetDerivation T Y f)).choose

/-- The factorisation sends an exact differential `d a` to the jet `(d a, 0)`. -/
public theorem dpJetLift_val_app_d (W : (Opens ↑T.scheme)ᵒᵖ)
    (a : ↑(T.scheme.sheaf.obj.obj W)) :
    (dpJetLift T Y f).val.app W (dpDerivationHom T Y f W a) = dpJetTheta T Y f W a :=
  (universalDPSchemeDerivation_isUniversal T Y f (dpJetSheaf T Y f)
    (dpJetDerivation T Y f)).choose_spec.1 W.unop a

/-- **The factorisation is the only morphism of sheaves of modules carrying every exact
differential `d a` to the jet `(d a, 0)`**, by the uniqueness half of the universal property.
This is the sense in which `Crystalline.dpDeRham` is *the* de Rham differential. -/
public theorem dpJetLift_unique (φ : dpDifferentialsSheaf T Y f ⟶ dpJetSheaf T Y f)
    (hφ : ∀ (W : T.scheme.Opens) (a : Γ(T.scheme, W)),
      φ.app W (sheafApp T Y f W a) = dpJetTheta T Y f (op W) a) :
    φ = dpJetLift T Y f :=
  (universalDPSchemeDerivation_isUniversal T Y f (dpJetSheaf T Y f)
    (dpJetDerivation T Y f)).choose_spec.2 φ hφ

/-- **The factorisation is a section of the projection onto `Ω_{T/Y,δ}`**: the two maps
`Ω_{T/Y,δ} → Ω_{T/Y,δ}` obtained from it and from the identity agree on every exact differential,
so they agree by the uniqueness half of the universal property. -/
public theorem dpJetLift_comp_fstHom :
    dpJetLift T Y f ≫ dpJetFstHom T Y f = 𝟙 (dpDifferentialsSheaf T Y f) := by
  obtain ⟨φ, -, huniq⟩ := universalDPSchemeDerivation_isUniversal T Y f
    (dpDifferentialsSheaf T Y f) (universalDPSchemeDerivation T Y f)
  refine (huniq _ ?_).trans (huniq _ ?_).symm
  · intro W x
    exact congrArg dpJetFst (dpJetLift_val_app_d T Y f (op W) x)
  · intro W x
    rfl

/-- The factorisation is a section of the projection: the differential coordinate of the jet
attached to `ω` is `ω`. -/
public theorem dpJetFst_lift (W : (Opens ↑T.scheme)ᵒᵖ)
    (ω : ↑((dpDifferentialsModules T Y f).obj W)) :
    dpJetFst ((dpJetLift T Y f).val.app W ω) = ω :=
  congrArg (fun φ : dpDifferentialsSheaf T Y f ⟶ dpDifferentialsSheaf T Y f => φ.val.app W ω)
    (dpJetLift_comp_fstHom T Y f)

/-- **The degree-one divided power de Rham differential `d : Ω_{T/Y,δ} → Ω²_{T/Y,δ}` on
sections**: the two-form coordinate of the factorisation of the derivation into the jets. -/
public def dpDeRham (W : (Opens ↑T.scheme)ᵒᵖ)
    (ω : ↑((dpDifferentialsModules T Y f).obj W)) :
    ↑((dpSecondExteriorModules T Y f).obj W) :=
  dpJetSnd ((dpJetLift T Y f).val.app W ω)

/-- The factorisation of the derivation into the jets is `ω ↦ (ω, d ω)`. -/
public theorem dpJetLift_apply (W : (Opens ↑T.scheme)ᵒᵖ)
    (ω : ↑((dpDifferentialsModules T Y f).obj W)) :
    (dpJetLift T Y f).val.app W ω = dpJetMk ω (dpDeRham T Y f W ω) :=
  dpJet_ext (dpJetFst_lift T Y f W ω) rfl

/-- **The de Rham differential is additive.** -/
public theorem dpDeRham_add (W : (Opens ↑T.scheme)ᵒᵖ)
    (ω ω' : ↑((dpDifferentialsModules T Y f).obj W)) :
    dpDeRham T Y f W (ω + ω') = dpDeRham T Y f W ω + dpDeRham T Y f W ω' :=
  congrArg dpJetSnd (map_add ((dpJetLift T Y f).val.app W).hom ω ω')

/-- **The de Rham differential sends zero to zero.** -/
@[simp] public theorem dpDeRham_zero (W : (Opens ↑T.scheme)ᵒᵖ) : dpDeRham T Y f W 0 = 0 :=
  congrArg dpJetSnd (map_zero ((dpJetLift T Y f).val.app W).hom)

/-- **The Leibniz rule for the de Rham differential**: `d (a ω) = a (d ω) + (d a) ∧ ω`. -/
public theorem dpDeRham_smul (W : (Opens ↑T.scheme)ᵒᵖ) (a : ↑(T.scheme.sheaf.obj.obj W))
    (ω : ↑((dpDifferentialsModules T Y f).obj W)) :
    dpDeRham T Y f W (a • ω) = a • dpDeRham T Y f W ω +
      bilinearApp (dpWedge T Y f) W (dpDerivationHom T Y f W a) ω := by
  have hsmul := ((dpJetLift T Y f).val.app W).hom.map_smul
  have h2 : dpDeRham T Y f W (a • ω) =
      a • dpDeRham T Y f W ω + bilinearApp (dpWedge T Y f) W (dpDerivationHom T Y f W a)
        (dpJetFst ((dpJetLift T Y f).val.app W ω)) :=
    congrArg dpJetSnd (hsmul a ω)
  rw [dpJetFst_lift] at h2
  exact h2

/-- **The de Rham differential kills every exact differential**, `d (d a) = 0`. -/
public theorem dpDeRham_d (W : (Opens ↑T.scheme)ᵒᵖ) (a : ↑(T.scheme.sheaf.obj.obj W)) :
    dpDeRham T Y f W (dpDerivationHom T Y f W a) = 0 :=
  congrArg dpJetSnd (dpJetLift_val_app_d T Y f W a)

/-- **The de Rham differential commutes with restriction.** -/
public theorem dpDeRham_naturality {W W' : (Opens ↑T.scheme)ᵒᵖ} (i : W ⟶ W')
    (ω : ↑((dpDifferentialsModules T Y f).obj W)) :
    (dpSecondExteriorModules T Y f).map i (dpDeRham T Y f W ω) =
      dpDeRham T Y f W' ((dpDifferentialsModules T Y f).map i ω) :=
  (congrArg dpJetSnd (PresheafOfModules.naturality_apply (dpJetLift T Y f).val i ω)).symm

/-- **The divided power form of the Leibniz rule**:
`d (δ_{k+1}(a) ω) = δ_{k+1}(a) (d ω) + δ_k(a) ((d a) ∧ ω)`, the identity that the divided power
compatibility of `q₁₂` rests on. -/
public theorem dpDeRham_dpow_smul (W : (Opens ↑T.scheme)ᵒᵖ) (k : ℕ)
    {a : ↑(T.scheme.sheaf.obj.obj W)} (ha : a ∈ sectionIdeal T.scheme.sheaf T.ideal W)
    (ω : ↑((dpDifferentialsModules T Y f).obj W)) :
    dpDeRham T Y f W ((T.dividedPowers.dividedPowers W).dpow (k + 1) a • ω) =
      (T.dividedPowers.dividedPowers W).dpow (k + 1) a • dpDeRham T Y f W ω +
        (T.dividedPowers.dividedPowers W).dpow k a •
          bilinearApp (dpWedge T Y f) W (dpDerivationHom T Y f W a) ω := by
  rw [dpDeRham_smul, dpDerivationHom_dpow_succ T Y f W k ha, bilinearApp_smul_left]

/-! ### The third map out of `𝒪_{T'}` -/

/-- The differential of the function coordinate of a section of `𝒪_{T'}`, as an additive map. -/
public def firstOrderFstDerivationHom (W : (Opens ↑T.scheme)ᵒᵖ) :
    ↑((firstOrderThickeningPresheaf T Y f).obj W) →+
      ↑((dpDifferentialsModules T Y f).obj W) :=
  AddMonoidHom.mk' (fun x => dpDerivationHom T Y f W (sqZeroExtFst x))
    (fun x y => (congrArg (dpDerivationHom T Y f W) (sqZeroExtFst_add x y)).trans
      (map_add (dpDerivationHom T Y f W) _ _))

/-- The de Rham differential of the differential coordinate of a section of `𝒪_{T'}`, as an
additive map. -/
public def firstOrderSndDeRhamHom (W : (Opens ↑T.scheme)ᵒᵖ) :
    ↑((firstOrderThickeningPresheaf T Y f).obj W) →+
      ↑((dpSecondExteriorModules T Y f).obj W) :=
  AddMonoidHom.mk' (fun x => dpDeRham T Y f W (sqZeroExtSnd x))
    (fun x y => (congrArg (dpDeRham T Y f W) (sqZeroExtSnd_add x y)).trans
      (dpDeRham_add T Y f W _ _))

/-- **The map `q₁₂ : 𝒪_{T'} → 𝒪_{T''}`**, `(f, ω) ↦ (f, d f, ω, d ω)`.  It is multiplicative
because the de Rham differential obeys the Leibniz rule
`d (f η + g ω) = f (d η) + g (d ω) + (d f) ∧ η + (d g) ∧ ω`, which is exactly the correction term
of the second-order multiplication. -/
@[stacks 07J3 "the map q₁₂"]
public def secondOrderThickeningQ₁₂ :
    firstOrderThickeningPresheaf T Y f ⟶ secondOrderThickeningPresheaf T Y f :=
  secondOrderExtLiftTopPresheafHom (dpWedge T Y f) (firstOrderThickeningProj T Y f)
    (firstOrderFstDerivationHom T Y f) (firstOrderSndHom T Y f)
    (firstOrderSndDeRhamHom T Y f)
    (fun W x y => (congrArg (dpDerivationHom T Y f W) (sqZeroExtFst_mul x y)).trans
      (dpDerivationHom_mul T Y f W (sqZeroExtFst x) (sqZeroExtFst y)))
    (fun _ x y => sqZeroExtSnd_mul x y)
    (fun W x y => by
      change dpDeRham T Y f W (sqZeroExtSnd (x * y)) =
        sqZeroExtFst x • dpDeRham T Y f W (sqZeroExtSnd y) +
          sqZeroExtFst y • dpDeRham T Y f W (sqZeroExtSnd x) +
          bilinearApp (dpWedge T Y f) W (dpDerivationHom T Y f W (sqZeroExtFst x))
            (sqZeroExtSnd y) +
          bilinearApp (dpWedge T Y f) W (dpDerivationHom T Y f W (sqZeroExtFst y))
            (sqZeroExtSnd x)
      rw [show sqZeroExtSnd (x * y) =
            sqZeroExtFst x • sqZeroExtSnd y + sqZeroExtFst y • sqZeroExtSnd x from
          sqZeroExtSnd_mul x y, dpDeRham_add, dpDeRham_smul, dpDeRham_smul]
      abel)
    (fun i x => (dpDerivationHom_naturality T Y f i (sqZeroExtFst x)).trans
      (congrArg (dpDerivationHom T Y f _) (sqZeroExtFst_map i x).symm))
    (fun i x => (sqZeroExtSnd_map i x).symm)
    (fun i x => (dpDeRham_naturality T Y f i (sqZeroExtSnd x)).trans
      (congrArg (dpDeRham T Y f _) (sqZeroExtSnd_map i x).symm))

/-- The underlying coordinate of `q₁₂ x` is the underlying coordinate of `x`. -/
@[simp] public theorem secondOrderThickeningQ₁₂_fst (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : ↑((firstOrderThickeningPresheaf T Y f).obj W)) :
    secondOrderExtFst (((secondOrderThickeningQ₁₂ T Y f).app W).hom x) = sqZeroExtFst x := rfl

/-- The left coordinate of `q₁₂ x` is the differential of the underlying coordinate of `x`. -/
@[simp] public theorem secondOrderThickeningQ₁₂_left (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : ↑((firstOrderThickeningPresheaf T Y f).obj W)) :
    secondOrderExtLeft (((secondOrderThickeningQ₁₂ T Y f).app W).hom x) =
      dpDerivationHom T Y f W (sqZeroExtFst x) := rfl

/-- The right coordinate of `q₁₂ x` is the square-zero coordinate of `x`. -/
@[simp] public theorem secondOrderThickeningQ₁₂_right (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : ↑((firstOrderThickeningPresheaf T Y f).obj W)) :
    secondOrderExtRight (((secondOrderThickeningQ₁₂ T Y f).app W).hom x) = sqZeroExtSnd x := rfl

/-- The top coordinate of `q₁₂ x` is the de Rham differential of the square-zero coordinate of
`x`. -/
@[simp] public theorem secondOrderThickeningQ₁₂_top (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : ↑((firstOrderThickeningPresheaf T Y f).obj W)) :
    secondOrderExtTop (((secondOrderThickeningQ₁₂ T Y f).app W).hom x) =
      dpDeRham T Y f W (sqZeroExtSnd x) := rfl

/-- **`q₁₂` is compatible with the divided power structures on `J'` and `J''`**, because the
universal divided power derivation obeys the divided power chain rule and the de Rham
differential obeys its divided power Leibniz rule
`d (δ_{k+1}(f) ω) = δ_{k+1}(f) (d ω) + δ_k(f) ((d f) ∧ ω)`. -/
@[stacks 07J3 "q₁₂ is compatible with the divided powers"]
public theorem secondOrderThickeningQ₁₂_isDPMorphism (W : (Opens ↑T.scheme)ᵒᵖ) :
    DividedPowers.IsDPMorphism (firstOrderThickeningDividedPowers T Y f W)
      (secondOrderThickeningDividedPowers T Y f W)
      (((secondOrderThickeningQ₁₂ T Y f).app W).hom) := by
  refine isDPMorphism_secondOrderExt_of_graph_top (dpWedge T Y f) W
    (T.dividedPowers.dividedPowers W) (firstOrderThickeningDividedPowers T Y f W) _
    (firstOrderThickeningProj_isDPMorphism T Y f W) ?_ ?_ ?_
  · intro k x hx
    have h : sqZeroExtFst ((firstOrderThickeningDividedPowers T Y f W).dpow (k + 1) x) =
        (T.dividedPowers.dividedPowers W).dpow (k + 1) (sqZeroExtFst x) :=
      (congrArg sqZeroExtFst
        (firstOrderThickeningDividedPowers_dpow_succ T Y f W k hx)).trans (sqZeroExtFst_mk _ _)
    change dpDerivationHom T Y f W
      (sqZeroExtFst ((firstOrderThickeningDividedPowers T Y f W).dpow (k + 1) x)) = _
    rw [h]
    exact dpDerivationHom_dpow_succ T Y f W k hx
  · intro k x hx
    exact sqZeroExtSnd_dpow_succ T Y f W k hx
  · intro k x hx
    change dpDeRham T Y f W
      (sqZeroExtSnd ((firstOrderThickeningDividedPowers T Y f W).dpow (k + 2) x)) = _
    rw [sqZeroExtSnd_dpow_succ T Y f W (k + 1) hx]
    exact dpDeRham_dpow_smul T Y f W k hx (sqZeroExtSnd x)

/-- **`q₁ = q₁₂ ∘ p₀`**, the two-form coordinate because the de Rham differential of the zero
differential vanishes. -/
@[stacks 07J3 "q₁ = q₁₂ ∘ p₀"]
public theorem secondOrderThickeningQ₁_eq_Q₁₂_comp_P₀ :
    firstOrderThickeningP₀ T Y f ≫ secondOrderThickeningQ₁₂ T Y f =
      secondOrderThickeningQ₁ T Y f :=
  NatTrans.ext (funext fun W => CommRingCat.hom_ext (RingHom.ext fun _ =>
    secondOrderExt_ext rfl rfl rfl (dpDeRham_zero T Y f W)))

/-- **`q₂ = q₁₂ ∘ p₁`**, the two-form coordinate because the de Rham differential kills every
exact differential. -/
@[stacks 07J3 "q₂ = q₁₂ ∘ p₁"]
public theorem secondOrderThickeningQ₂_eq_Q₁₂_comp_P₁ :
    firstOrderThickeningP₁ T Y f ≫ secondOrderThickeningQ₁₂ T Y f =
      secondOrderThickeningQ₂ T Y f :=
  NatTrans.ext (funext fun W => CommRingCat.hom_ext (RingHom.ext fun a =>
    secondOrderExt_ext rfl rfl rfl (dpDeRham_d T Y f W a)))

end Crystalline

end
