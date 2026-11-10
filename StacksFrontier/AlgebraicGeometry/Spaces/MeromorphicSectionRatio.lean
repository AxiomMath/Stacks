module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardWeilDivisorClassIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceRationalFunctionsMeromorphic

/-!
# The ratio of two regular meromorphic sections of an invertible module

Let `X` be a locally Noetherian integral algebraic space over a scheme `S` and let `ℒ` be an
invertible `𝒪_X`-module. Two regular meromorphic sections `s`, `s'` of `ℒ` differ by a **unique
invertible global meromorphic function**:

`s = g · s'` with `g ∈ Γ(X, 𝒦_X)^*`.

This is the first assertion of Stacks 0EPT — the algebraic-space analogue of Stacks 02SH — read
through the identification `R(X) = Γ(X, 𝒦_X)` of Stacks 0ENA, which on such an `X` makes
`Γ(X, 𝒦_X)` the function field and in particular a field.

The argument is the source's. The trivialisation `𝒦_X ≅ 𝒦_X(ℒ)` that Stacks 0EPQ produces turns
a meromorphic section of `ℒ` into a global meromorphic function: the global sections of `𝒦_X`
read as a `𝒦_X`-module are the multiples of the unit section, so `s = a · t` and `s' = b · t`
for one and the same `t`, the image of the unit section, and `a`, `b` global meromorphic
functions. Regularity makes `a` and `b` nonzero — a zero meromorphic section is not regular, the
ring of global meromorphic functions being nontrivial — hence invertible, `Γ(X, 𝒦_X)` being a
field; and `g = a b⁻¹`. Uniqueness is regularity of `s'` again: multiplication by a regular
section is injective on every étale chart, hence on global meromorphic functions.

## Main results

* `AlgebraicGeometry.Space.existsUnique_smul_meromorphicUnitSection`: a global section of `𝒦_X`
  read as a `𝒦_X`-module is a unique global meromorphic function times the unit section.
* `AlgebraicGeometry.Space.nonempty_iso_meromorphicUnitModule_of_isTrivialAtCodimensionZeroPoints`:
  the trivialisation `𝒦_X ≅ 𝒦_X(ℒ)` of Stacks 0EPQ, stated on its own.
* `AlgebraicGeometry.Space.existsUnique_units_smul_eq_of_isRegularMeromorphicSection`: **the
  first assertion of Stacks 0EPT**, two regular meromorphic sections of an invertible module
  differ by a unique invertible global meromorphic function.

## Implementation notes

The ring of global meromorphic functions is spelled `RingCat.sectionsSubring` of the ring sheaf
of the meromorphic ringed site rather than `AlgebraicGeometry.Space.MeromorphicFunction`, as in
`StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClassRescaling.lean`: the two are the
same subring of the same product, but only the first spelling makes instance search find the
module structure on the meromorphic sections. That spelling carries only a `Ring` instance — the
ambient product is a product of objects of `RingCat` — so commutativity is taken from the field
structure, `IsField.mul_comm`, rather than from a `CommRing` instance.

The trivialisation is extracted from the proof of
`AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_of_isTrivialAtCodimensionZeroPoints`,
which builds it and immediately consumes it; that proof is
`AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_of_nonempty_iso` applied to the
statement proved here.

## References

* [Stacks Project, Tag 02SH](https://stacks.math.columbia.edu/tag/02SH)
* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0ENE](https://stacks.math.columbia.edu/tag/0ENE)
* [Stacks Project, Tag 0EPQ](https://stacks.math.columbia.edu/tag/0EPQ)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- **Every global section of `𝒦_X`, read as a `𝒦_X`-module, is a global meromorphic function
times the unit section**, and that meromorphic function is unique. -/
theorem existsUnique_smul_meromorphicUnitSection
    (σ : (meromorphicUnitModule B S hS X hX).sections) :
    ∃! a : ↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)),
      a • meromorphicUnitSection B S hS X hX = σ := by
  have hone : ∀ (V : (SmallEtale B S hS X)ᵒᵖ)
      (r : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O).obj.obj V),
      r • (meromorphicUnitSection B S hS X hX).eval V = ULift.up r :=
    fun _ r => congrArg ULift.up (mul_one r)
  refine ⟨⟨fun V => (σ.eval V).down, ?_⟩, ?_, ?_⟩
  · intro V W f
    exact congrArg ULift.down (σ.property f)
  · refine Subtype.ext (funext fun V => ?_)
    exact (hone V _).trans (ULift.up_down _)
  · intro b hb
    refine Subtype.ext (funext fun V => ?_)
    exact congrArg ULift.down
      ((hone V (b.1 V)).symm.trans (congrFun (congrArg Subtype.val hb) V))

/-- **The trivialisation `𝒦_X ≅ 𝒦_X(ℒ)` of Stacks 0EPQ**, on an algebraic space satisfying
conditions (a), (b) and (c) of Stacks 0ENA. This is the isomorphism that the proof of
`AlgebraicGeometry.Space.exists_isRegularMeromorphicSection_of_isTrivialAtCodimensionZeroPoints`
builds and then consumes; stated on its own because the ratio of two regular meromorphic
sections is read through it. -/
theorem nonempty_iso_meromorphicUnitModule_of_isTrivialAtCodimensionZeroPoints
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS),
      localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X)
    (hmono : HasMonomorphicCodimensionZeroPoints B S hS X)
    (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) L) :
    Nonempty (meromorphicUnitModule B S hS X hX ≅
      meromorphicSectionSheaf.{u, u} B S hS X hX L) := by
  obtain ⟨P⟩ := exists_codimensionZeroPresentation B S hS hX hfin hmono
  have hgenL : IsTrivialAtCodimensionZeroPoints hX P L := fun x hx =>
    P.nonempty_iso_unit_of_isInvertibleModule x hx _
      (modulePullbackInvertible (P.genericMorphism hx hX) L hL)
  have hτ : (η : CodimensionZeroPresentation.CodimensionZeroPoints B S hS X) →
      P.genericPointPullback (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) η.2 L ≅
        SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS (P.specStalkSpace η.2).1 (P.specStalkSpace η.2).2).O) :=
    fun η => (hgenL η.1 η.2).some
  have hMinv : AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS))
      (structureRingSheaf B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS)).property L :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL
  exact P.nonempty_uliftUnit_iso_meromorphicSectionSheaf
    (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) L hτ hwa hfin hMinv

variable (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

include hInt hN in
/-- **Stacks 0EPT, the first conclusion; the algebraic-space analogue of Stacks 02SH.** On a
locally Noetherian integral algebraic space over a scheme `S`, two regular meromorphic sections
`s`, `s'` of an invertible `𝒪_X`-module differ by a unique **invertible** global meromorphic
function: `s = g · s'` with `g ∈ Γ(X, 𝒦_X)^*`. Since `R(X) = Γ(X, 𝒦_X)` by the third conclusion
of Stacks 0ENA, this says that the ratio `s / s'` lies in `R(X)^*`.

The trivialisation `𝒦_X ≅ 𝒦_X(ℒ)` of Stacks 0EPQ writes both sections as multiples of one
section `t`, the coefficients being global meromorphic functions; they are nonzero by
regularity, hence invertible because `Γ(X, 𝒦_X)` is the function field; and uniqueness is
injectivity of multiplication by the regular section `s'`. -/
@[stacks 0EPT "the first conclusion, that the ratio s/s' of two regular meromorphic sections of \
an invertible module is invertible, read in Γ(X, 𝒦_X) -- which is R(X) by the third conclusion \
of Stacks 0ENA; the ratio is also unique"]
theorem existsUnique_units_smul_eq_of_isRegularMeromorphicSection
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (s s' : MeromorphicSection.{u, u} B S hS X hX L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X hX L s)
    (hs' : IsRegularMeromorphicSection.{u, u} B S hS X hX L s') :
    ∃! g : (↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)))ˣ,
      s = (g : ↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj))) •
        s' := by
  -- the three conditions of Stacks 0ENA on such an `X`
  have hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS),
      localRingDimension B S hS z = 0 := fun _ hz => by
    rwa [weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero B S hS ⟨X, hX⟩
      hInt.hasEtaleLocalProperty_isReduced] at hz
  have hfin := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX hN
  have hmono := IsDecentWithFinitelyManyComponents.hasMonomorphicCodimensionZeroPoints B S hS
    ⟨hInt.isDecentSpace, hInt.finite_irreducibleComponents⟩
  obtain ⟨e⟩ := nonempty_iso_meromorphicUnitModule_of_isTrivialAtCodimensionZeroPoints B S hS hX
    hwa hfin hmono L hL
  obtain ⟨eR, -⟩ := exists_ringEquiv_rationalFunctions_meromorphicFunction
    (X := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) hwa hfin hmono
  -- `Γ(X, 𝒦_X) = R(X)` is a field, so a nonzero global meromorphic function is invertible
  have hfieldK : IsField (↥(RingCat.sectionsSubring
      ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj))) :=
    MulEquiv.isField (isField_rationalFunctions B S hS hX hInt) eR.symm.toMulEquiv
  -- sections of `𝒦_X(ℒ)` are multiples of the image of the unit meromorphic function
  have hlin : ∀ (a : ↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)))
      (x : (meromorphicUnitModule B S hS X hX).sections),
      SheafOfModules.sectionsMap e.hom (a • x) = a • SheafOfModules.sectionsMap e.hom x :=
    fun a x => ((Stacks.Cohomology.SiteModules.globalSectionsFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O)).map
        e.hom).hom.map_smul a x
  have hround : ∀ x : MeromorphicSection.{u, u} B S hS X hX L,
      SheafOfModules.sectionsMap e.hom (SheafOfModules.sectionsMap e.inv x) = x := fun x =>
    Subtype.ext (funext fun V =>
      congrArg (fun φ : meromorphicSectionSheaf.{u, u} B S hS X hX L ⟶
          meromorphicSectionSheaf.{u, u} B S hS X hX L =>
        PresheafOfModules.Hom.app φ.val V (x.eval V)) e.inv_hom_id)
  -- a regular meromorphic section is nonzero, the ring of global meromorphic functions being
  -- the function field and so nontrivial
  have hnezero : ∀ x : MeromorphicSection.{u, u} B S hS X hX L,
      IsRegularMeromorphicSection.{u, u} B S hS X hX L x → x ≠ 0 := by
    intro x hx hx0
    have h1 : (1 : ↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj))) =
        0 := by
      refine Subtype.ext (funext fun W => hx W.unop ?_)
      change (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X hX).O).obj.obj W) • x.eval W =
        (0 : (Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X hX).O).obj.obj W) • x.eval W
      rw [hx0]
      simp
    obtain ⟨p, q, hpq⟩ := hfieldK.exists_pair_ne
    exact hpq (by rw [← one_mul p, ← one_mul q, h1, zero_mul, zero_mul])
  -- a regular meromorphic section is a unit multiple of the image of the unit section
  have hunitmul : ∀ x : MeromorphicSection.{u, u} B S hS X hX L,
      IsRegularMeromorphicSection.{u, u} B S hS X hX L x →
      ∃ a : ↥(RingCat.sectionsSubring
        ((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X hX).O).obj)),
        IsUnit a ∧
          x = a • SheafOfModules.sectionsMap e.hom (meromorphicUnitSection B S hS X hX) := by
    intro x hx
    obtain ⟨a, ha, -⟩ := existsUnique_smul_meromorphicUnitSection B S hS hX
      (SheafOfModules.sectionsMap e.inv x)
    have hxa : x = a • SheafOfModules.sectionsMap e.hom (meromorphicUnitSection B S hS X hX) := by
      rw [← hlin, ha, hround]
    refine ⟨a, ?_, hxa⟩
    obtain ⟨z, hz⟩ := hfieldK.mul_inv_cancel (a := a)
      fun h => hnezero x hx (by rw [hxa, h, zero_smul])
    exact ⟨⟨a, z, hz, (hfieldK.mul_comm z a).trans hz⟩, rfl⟩
  obtain ⟨-, ⟨ua, rfl⟩, hsa⟩ := hunitmul s hs
  obtain ⟨-, ⟨ub, rfl⟩, hsb⟩ := hunitmul s' hs'
  have hmain : s = ↑(ua * ub⁻¹) • s' := by
    rw [hsa, hsb, Units.smul_def, smul_smul, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  exact ⟨ua * ub⁻¹, hmain, fun h hh => Units.ext <| Subtype.ext <| funext fun W =>
    hs' W.unop (congrFun (congrArg Subtype.val (hh.symm.trans hmain)) W)⟩

end AlgebraicGeometry.Space

end
