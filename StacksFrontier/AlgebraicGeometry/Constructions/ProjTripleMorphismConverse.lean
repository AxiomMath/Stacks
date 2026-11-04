module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleUnitSection
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleVeroneseMorphism

/-!
# Clause (4) implies clause (1) of Tag 01NB

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `X = Proj(A)` and `Y` a scheme. A triple `(d, L, ψ)`
over `Y` classifies a morphism `Y ⟶ X` by [Stacks, Tag 01N8]. [Stacks, Tag 01NB] asserts that for
two triples `(d, L, ψ)` and `(d', L', ψ')` the four conditions

1. at `n = lcm(d, d')`, with `n = ad = a'd'`, there is an isomorphism
   `β : L^{⊗ a} ≅ (L')^{⊗ a'}` with `β ∘ ψ|_{A^{(n)}} = ψ'|_{A^{(n)}}`;
2. the same at `n = dd'`;
3. the same for some positive `n = ad = a'd'`;
4. the two classified morphisms `Y ⟶ X` are equal

are equivalent. The implications (1) ⇒ (2) ⇒ (3) are proved in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjTripleEquivalence.lean` and (1), (2), (3) ⇒ (4)
in `StacksFrontier/AlgebraicGeometry/Constructions/ProjTripleVeroneseMorphism.lean`. **This file
proves (4) ⇒ (1)**, which closes the cycle.

## The argument

Two triples of one and the same weight `d` with the same classified morphism `φ` carry, by the
uniqueness of [Stacks, Tag 01N8], isomorphisms `α : φ⁎𝒪_X(d) ≅ L` and `α' : φ⁎𝒪_X(d) ≅ L'` over
that same `φ`, so `β := α⁻¹ ∘ α'` is an isomorphism `L ≅ L'`. That `β` matches `ψ` with `ψ'`
degreewise, which is proved in three steps and uses no tensor power of `α`:

* in degree `1` the degree-one clause of
  `Stacks.AlgebraicGeometry.MorphismToProjUniversal.IsCompatible` holds for both pairs with one
  and the same section of `φ⁎𝒪_X(d)` on the left, because the two pairs have the same first
  component, and `β` was built to cancel the two `α`'s;
* in degree `0` the two values are both the unit section of `𝒪_Y`, which for a triple is a
  consequence of the generation condition
  (`Stacks.AlgebraicGeometry.ProjTripleUnitSection.toFun_zero_eq_unitGlobal`) and not an axiom;
  by `Stacks.AlgebraicGeometry.ProjTripleClassifying.natTensorPowCongr_pow` the two previous
  steps give the degree-`m` square on the powers `ψ(f)^m` of a trivializing section;
* in degree `m` the degree-`m` clause of `IsCompatible` is the source's local identity
  `ψ(a)|_V = φ^♯(a/f^n) · ψ(f)^n|_V`, and it holds for both triples over
  `V = Y_{ψ(f)} = φ^{-1}(D₊(f)) = Y_{ψ'(f)}` **with the same scalar**, again because the two
  pairs have the same first component. Since `β^{⊗ m}` is a morphism of `𝒪_Y`-modules it carries
  one identity to the other, so the two global sections `β^{⊗ m}(ψ(a))` and `ψ'(a)` of
  `(L')^{⊗ m}` agree over a cover of `Y`, hence are equal
  (`Stacks.Algebraization.eq_zero_of_affine_cover`).

For two triples of *different* weights, the Veronese restrictions at the weights `a = n/d` and
`a' = n/d'` have the common weight `n = lcm(d, d')` and classify the same morphisms as the
triples themselves
(`Stacks.AlgebraicGeometry.ProjTripleVeroneseMorphism.classifyingMorphism_veroneseRestrict`), so
the equal-weight case applies to them and produces exactly the data of clause (1).

## Main results

* `Stacks.AlgebraicGeometry.ProjTripleMorphismConverse.sectionsEquiv_of_sameMorphism`: two graded
  maps of one weight whose classified morphisms agree are strictly equivalent — the converse of
  `Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom_eq_of_sectionsEquiv`.
* `Stacks.AlgebraicGeometry.ProjTripleMorphismConverse.agreeAtLcm_of_sameMorphism`: **clause (4)
  implies clause (1) of [Stacks, Tag 01NB]**, the exact converse of
  `Stacks.AlgebraicGeometry.ProjTripleVeroneseMorphism.sameMorphism_of_agreeAtLcm`.

## Implementation notes

**Why no tensor power of `α` is needed.** The route the source suggests builds `β` out of the two
isomorphisms `α : φ⁎𝒪_X(d) ≅ L` and `α' : φ⁎𝒪_X(d') ≅ L'` as
`L^{⊗ a} ≅ φ⁎𝒪_X(n) ≅ (L')^{⊗ a'}`, and verifying the agreement condition for it needs the
tensor-power square `α^{⊗ m}(ψ^d_φ(x)) = ψ(x)` in every degree `m`, which `IsCompatible` asserts
only in degree one. Passing to the Veronese restrictions *first* removes the need: at the common
weight `n` the two `α`'s have one and the same source `φ⁎𝒪_X(n)`, so `β` is their composite and
only the degree-one square enters.

**Why the degreewise squares are stated for an arbitrary family.** `zero_pow_of_isoFamily`,
`one_of_isoFamily`, `pow_of_isCompatible_of_isoFamily` and `toFun_of_pow_of_isoFamily` ask only
for a degreewise family `c n : L^{⊗ n} ≅ (L')^{⊗ n}` of isomorphisms of `𝒪_Y`-modules, with a
multiplicativity and the degree-zero and degree-one values where those enter; the four named
`natTensorPowCongr_*` statements are their instances at the tensor powers of `β`. The generality
is what a strict equivalence of quadruples of Section 01NS consumes: there the comparison is the
degreewise family of an isomorphism of Laurent algebras read through
`Stacks.AlgebraicGeometry.CoherentMulSections.powCompare`, which is not given as a tensor power
of anything and is not known to agree with one. See
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineQuadrupleConverse.lean`.

**Which spelling the statement is in.** Clause (1) is stated here in the degreewise
`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections` spelling of `ψ`, the one the
classifying construction of [Stacks, Tag 01N8] consumes; clauses (1)–(3) of
`ProjTripleEquivalence.lean` are stated for an invertible sheaf on a ringed site. The
implementation notes of
`StacksFrontier/AlgebraicGeometry/Constructions/ProjTripleClassifyingMorphism.lean` record why the
three spellings of `ψ` this development carries have no multiplicative bridge, so an implication
relating a clause to clause (4) can only be stated in this one.

## References

* [Stacks Project, Tag 01NB](https://stacks.math.columbia.edu/tag/01NB)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.MorphismToProjUniversal
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjSectionsUnique (Pair)
open Stacks.AlgebraicGeometry.ProjTripleClassifying
open Stacks.AlgebraicGeometry.ProjTripleStructureMorphism (unitGlobal pow_zero_eq_unitGlobal)
open Stacks.AlgebraicGeometry.ProjTripleUnitSection (toFun_zero_eq_unitGlobal)
open Stacks.AlgebraicGeometry.ProjTripleVeroneseMorphism (classifyingMorphism_veroneseRestrict)
open Stacks.AmplePullbackPart1 (natTensorPowCongr)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop resTop_app)

universe u w

namespace Stacks.AlgebraicGeometry.ProjTripleMorphismConverse

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### Two global sections agreeing over a cover -/

/-- **Two global sections of a sheaf of modules that agree over each member of an open cover are
equal.** This is the separatedness of a sheaf of modules, in the shape
`Stacks.Algebraization.eq_zero_of_affine_cover` provides it, applied to the difference. -/
theorem eq_of_resTop_eq_of_cover {Y : Scheme.{u}} (M : Y.Modules) {s t : Γ(M, ⊤)} {J : Type*}
    (U : J → Y.Opens) (hU : iSup U = ⊤) (h : ∀ j, resTop M s (U j) = resTop M t (U j)) :
    s = t := by
  refine sub_eq_zero.mp (Stacks.Algebraization.eq_zero_of_affine_cover _ U hU fun B j hBV hBU => ?_)
  have e := fun x => Stacks.TensorPowerTrivialize.res_resTop M x (homOfLE hBU)
  have e3 : ∀ x : Γ(M, ⊤), M.val.map (homOfLE hBV).op x = resTop M x (B : Y.Opens) := fun _ => rfl
  rw [e3, ← resTopHom_apply, map_sub]
  refine sub_eq_zero_of_eq ?_
  rw [resTopHom_apply, resTopHom_apply, ← e, ← e, h j]

/-! ### The degreewise squares for the composite of the two trivializations -/

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : Scheme.{u}} {d : ℕ} {L L' : Y.Modules}
  [Stacks.Ample.IsInvertibleModule Y L] [Stacks.Ample.IsInvertibleModule Y L']

/-- **The degree-zero square, for the zeroth power of a trivializing section, for an arbitrary
degreewise family of comparisons.** Both values are the unit section of `L^{⊗ 0} = 𝒪_Y =
(L')^{⊗ 0}`, which is a consequence of the generation condition
(`Stacks.AlgebraicGeometry.ProjTripleUnitSection.toFun_zero_eq_unitGlobal`), so all that is
asked of the family is that its degree-zero component preserve that section. -/
theorem zero_pow_of_isoFamily {ψ : VeroneseSections 𝒜 d L} {ψ' : VeroneseSections 𝒜 d L'}
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤)
    (hgen' : ⨆ f : 𝒜 d, nonvanishingOpen Y L' (psiSection 𝒜 ψ' f) = ⊤)
    (c : ∀ n : ℕ, natTensorPow L n ≅ natTensorPow L' n)
    (c0 : (c 0).hom.app ⊤ (unitGlobal L) = unitGlobal L') {g : A} (hg : g ∈ 𝒜 d) :
    (c 0).hom.app ⊤ (ψ.pow hg 0) = ψ'.pow hg 0 := by
  rw [pow_zero_eq_unitGlobal 𝒜 ψ (toFun_zero_eq_unitGlobal 𝒜 ψ hgen) hg,
    pow_zero_eq_unitGlobal 𝒜 ψ' (toFun_zero_eq_unitGlobal 𝒜 ψ' hgen') hg]
  exact c0

/-- **The degree-zero square, for the zeroth power of a trivializing section.** This is
`zero_pow_of_isoFamily` for the family of tensor powers of `β`, whose degree-zero component is
the identity of the monoidal unit. -/
theorem natTensorPowCongr_zero_pow {ψ : VeroneseSections 𝒜 d L} {ψ' : VeroneseSections 𝒜 d L'}
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤)
    (hgen' : ⨆ f : 𝒜 d, nonvanishingOpen Y L' (psiSection 𝒜 ψ' f) = ⊤)
    (β : L ≅ L') {g : A} (hg : g ∈ 𝒜 d) :
    (natTensorPowCongr β 0).hom.app ⊤ (ψ.pow hg 0) = ψ'.pow hg 0 :=
  zero_pow_of_isoFamily 𝒜 hgen hgen' (natTensorPowCongr β) rfl hg

omit [Stacks.Ample.IsInvertibleModule Y L] [Stacks.Ample.IsInvertibleModule Y L'] in
/-- **The degree-one square for `β = α⁻¹ ∘ α'`, for an arbitrary degreewise family of
comparisons.** The degree-one clause of
`Stacks.AlgebraicGeometry.MorphismToProjUniversal.IsCompatible` holds for the two pairs `(φ, α)`
and `(φ, α')` with one and the same section of `φ⁎𝒪_X(d)` on the left, since the two pairs have
the same first component; `β` cancels the two `α`'s, and the left unitor is injective on
sections. Of the family only the degree-one compatibility `hc₁` with `β` is used, which is the
hypothesis `Stacks.AlgebraicGeometry.ProjTripleClassifying.isCompatible_of_isoFamily` asks for
as well. -/
theorem one_of_isoFamily {ψ : VeroneseSections 𝒜 d L} {ψ' : VeroneseSections 𝒜 d L'}
    {φ : Y ⟶ (degreeOpen 𝒜 d).toScheme} {α : pullbackTwist 𝒜 φ (d : ℤ) ≅ L}
    {α' : pullbackTwist 𝒜 φ (d : ℤ) ≅ L'}
    (c : ∀ n : ℕ, natTensorPow L n ≅ natTensorPow L' n)
    (hc₁ : ∀ y : Γ(natTensorPow L 1, ⊤),
      (unitorPow L').hom.app ⊤ ((c 1).hom.app ⊤ y)
        = (α.symm ≪≫ α').hom.app ⊤ ((unitorPow L).hom.app ⊤ y))
    (hp : IsCompatible 𝒜 ψ ⟨φ, α⟩) (hp' : IsCompatible 𝒜 ψ' ⟨φ, α'⟩) (x : 𝒜 (1 * d)) :
    (c 1).hom.app ⊤ (ψ.toFun 1 x) = ψ'.toFun 1 x := by
  have hcancel : ∀ z : Γ(pullbackTwist 𝒜 φ (d : ℤ), ⊤),
      (α.symm ≪≫ α').hom.app ⊤ (α.hom.app ⊤ z) = α'.hom.app ⊤ z := fun z => by
    have hcomp : α.hom ≫ (α.symm ≪≫ α').hom = α'.hom := by
      rw [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
    have h := congrArg (fun u : pullbackTwist 𝒜 φ (d : ℤ) ⟶ L' => u.app ⊤ z) hcomp
    simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply] at h
    exact h
  have hkey : (α.symm ≪≫ α').hom.app ⊤ ((unitorPow L).hom.app ⊤ (ψ.toFun 1 x))
      = (unitorPow L').hom.app ⊤ (ψ'.toFun 1 x) := by
    rw [← hp.1 x, ← hp'.1 x]
    exact hcancel _
  have hinj : Function.Injective
      fun z : Γ(natTensorPow L' 1, ⊤) => (unitorPow L').hom.app ⊤ z := by
    intro z z' hzz'
    have h := congrArg (fun w => (unitorPow L').inv.app ⊤ w) hzz'
    simpa [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app] using h
  exact hinj ((hc₁ (ψ.toFun 1 x)).trans hkey)

omit [Ample.IsInvertibleModule Y L] [Ample.IsInvertibleModule Y L'] in
/-- **The degree-one square for `β = α⁻¹ ∘ α'`.** This is `one_of_isoFamily` for the family of
tensor powers of `β`, whose degree-one compatibility is the naturality of the left unitor. -/
theorem natTensorPowCongr_one {ψ : VeroneseSections 𝒜 d L} {ψ' : VeroneseSections 𝒜 d L'}
    {φ : Y ⟶ (degreeOpen 𝒜 d).toScheme} {α : pullbackTwist 𝒜 φ (d : ℤ) ≅ L}
    {α' : pullbackTwist 𝒜 φ (d : ℤ) ≅ L'}
    (hp : IsCompatible 𝒜 ψ ⟨φ, α⟩) (hp' : IsCompatible 𝒜 ψ' ⟨φ, α'⟩) (x : 𝒜 (1 * d)) :
    (natTensorPowCongr (α.symm ≪≫ α') 1).hom.app ⊤ (ψ.toFun 1 x) = ψ'.toFun 1 x :=
  one_of_isoFamily 𝒜 (natTensorPowCongr (α.symm ≪≫ α'))
    (unitorPow_hom_app_natTensorPowCongr (α.symm ≪≫ α')) hp hp' x

/-- **The degree-`n` square for `β = α⁻¹ ∘ α'`, on the powers of a trivializing section, for an
arbitrary multiplicative degreewise family of comparisons.** This is
`Stacks.AlgebraicGeometry.ProjTripleClassifying.pow_of_isoFamily` fed with the degree-zero and
degree-one squares of `zero_pow_of_isoFamily` and `one_of_isoFamily`. -/
theorem pow_of_isCompatible_of_isoFamily {ψ : VeroneseSections 𝒜 d L}
    {ψ' : VeroneseSections 𝒜 d L'}
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤)
    (hgen' : ⨆ f : 𝒜 d, nonvanishingOpen Y L' (psiSection 𝒜 ψ' f) = ⊤)
    {φ : Y ⟶ (degreeOpen 𝒜 d).toScheme} {α : pullbackTwist 𝒜 φ (d : ℤ) ≅ L}
    {α' : pullbackTwist 𝒜 φ (d : ℤ) ≅ L'}
    (c : ∀ n : ℕ, natTensorPow L n ≅ natTensorPow L' n)
    (hmul : ∀ (p q : ℕ) (s : Γ(natTensorPow L p, ⊤)) (t : Γ(natTensorPow L q, ⊤)),
      (c (p + q)).hom.app ⊤ (mulSections L s t)
        = mulSections L' ((c p).hom.app ⊤ s) ((c q).hom.app ⊤ t))
    (c0 : (c 0).hom.app ⊤ (unitGlobal L) = unitGlobal L')
    (hc₁ : ∀ y : Γ(natTensorPow L 1, ⊤),
      (unitorPow L').hom.app ⊤ ((c 1).hom.app ⊤ y)
        = (α.symm ≪≫ α').hom.app ⊤ ((unitorPow L).hom.app ⊤ y))
    (hp : IsCompatible 𝒜 ψ ⟨φ, α⟩) (hp' : IsCompatible 𝒜 ψ' ⟨φ, α'⟩) (n : ℕ) {g : A}
    (hg : g ∈ 𝒜 d) :
    (c n).hom.app ⊤ (ψ.pow hg n) = ψ'.pow hg n := by
  refine pow_of_isoFamily 𝒜 c hmul hg (zero_pow_of_isoFamily 𝒜 hgen hgen' c c0 hg) ?_ n
  have hg1 : g ∈ 𝒜 (1 * d) := by simpa using hg
  have h := one_of_isoFamily 𝒜 c hc₁ hp hp' ⟨g, hg1⟩
  rwa [ψ.toFun_eq_pow hg 1 ⟨g, hg1⟩ (pow_one g).symm,
    ψ'.toFun_eq_pow hg 1 ⟨g, hg1⟩ (pow_one g).symm] at h

/-- **The degree-`n` square for `β = α⁻¹ ∘ α'`, on the powers of a trivializing section.** This is
`pow_of_isCompatible_of_isoFamily` for the family of tensor powers of `β`. -/
theorem natTensorPowCongr_pow_of_isCompatible {ψ : VeroneseSections 𝒜 d L}
    {ψ' : VeroneseSections 𝒜 d L'}
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤)
    (hgen' : ⨆ f : 𝒜 d, nonvanishingOpen Y L' (psiSection 𝒜 ψ' f) = ⊤)
    {φ : Y ⟶ (degreeOpen 𝒜 d).toScheme} {α : pullbackTwist 𝒜 φ (d : ℤ) ≅ L}
    {α' : pullbackTwist 𝒜 φ (d : ℤ) ≅ L'}
    (hp : IsCompatible 𝒜 ψ ⟨φ, α⟩) (hp' : IsCompatible 𝒜 ψ' ⟨φ, α'⟩) (n : ℕ) {g : A}
    (hg : g ∈ 𝒜 d) :
    (natTensorPowCongr (α.symm ≪≫ α') n).hom.app ⊤ (ψ.pow hg n) = ψ'.pow hg n :=
  pow_of_isCompatible_of_isoFamily 𝒜 hgen hgen' (natTensorPowCongr (α.symm ≪≫ α'))
    (mulSections_natTensorPowCongr (α.symm ≪≫ α')) rfl
    (unitorPow_hom_app_natTensorPowCongr (α.symm ≪≫ α')) hp hp' n hg

omit [Stacks.Ample.IsInvertibleModule Y L'] in
/-- **From the squares on the powers of the trivializing sections to the square in degree `n` on
every homogeneous element, for an arbitrary degreewise family of comparisons.** The degree-`n`
clause of `Stacks.AlgebraicGeometry.MorphismToProjUniversal.IsCompatible` is the local identity
`ψ(a)|_V = φ^♯(a/f^n) · ψ(f)^n|_V`; the two pairs have the same first component, so the preimage
`φ^{-1}(D₊(f))` is both `Y_{ψ(f)}` and `Y_{ψ'(f)}` (`preimage_basicOpen_eq`) and the scalar
`φ^♯(a/f^n)` is one and the same. Applying `c n`, a morphism of `𝒪_Y`-modules, carries the
identity for `ψ` to the identity for `ψ'`, so the two sections agree over each `Y_{ψ(f)}`; those
cover `Y`.

Nothing is used of the family beyond each `c n` being an isomorphism of `𝒪_Y`-modules: it
commutes with restriction and is linear on sections, which is the whole of the argument. -/
theorem toFun_of_pow_of_isoFamily {ψ : VeroneseSections 𝒜 d L}
    {ψ' : VeroneseSections 𝒜 d L'}
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤)
    {φ : Y ⟶ (degreeOpen 𝒜 d).toScheme} {α : pullbackTwist 𝒜 φ (d : ℤ) ≅ L}
    {α' : pullbackTwist 𝒜 φ (d : ℤ) ≅ L'}
    (hp : IsCompatible 𝒜 ψ ⟨φ, α⟩) (hp' : IsCompatible 𝒜 ψ' ⟨φ, α'⟩)
    (c : ∀ n : ℕ, natTensorPow L n ≅ natTensorPow L' n) (n : ℕ)
    (hpow : ∀ g : 𝒜 d, (c n).hom.app ⊤ (ψ.pow g.2 n) = ψ'.pow g.2 n)
    (a : 𝒜 (n * d)) :
    (c n).hom.app ⊤ (ψ.toFun n a) = ψ'.toFun n a := by
  refine eq_of_resTop_eq_of_cover (natTensorPow L' n)
    (fun f : 𝒜 d => nonvanishingOpen Y L (psiSection 𝒜 ψ f)) hgen fun f => ?_
  have hV : nonvanishingOpen Y L (psiSection 𝒜 ψ f)
      ≤ toProj 𝒜 φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A) :=
    (preimage_basicOpen_eq 𝒜 hp f).ge
  have hmem : (a : A) ∈ 𝒜 (n • d) := by simp [smul_eq_mul]
  have h := hp.2 f _ hV n (a : A) hmem a rfl
  have h' := hp'.2 f _ hV n (a : A) hmem a rfl
  rw [resTop_app, h, Scheme.Modules.Hom.app_smul, ← resTop_app, hpow f, ← h']

omit [Stacks.Ample.IsInvertibleModule Y L'] in
/-- **From the squares on the powers of the trivializing sections to the square in degree `n` on
every homogeneous element.** This is `toFun_of_pow_of_isoFamily` for the family of tensor powers
of `β`. -/
theorem natTensorPowCongr_toFun_of_pow {ψ : VeroneseSections 𝒜 d L}
    {ψ' : VeroneseSections 𝒜 d L'}
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤)
    {φ : Y ⟶ (degreeOpen 𝒜 d).toScheme} {α : pullbackTwist 𝒜 φ (d : ℤ) ≅ L}
    {α' : pullbackTwist 𝒜 φ (d : ℤ) ≅ L'}
    (hp : IsCompatible 𝒜 ψ ⟨φ, α⟩) (hp' : IsCompatible 𝒜 ψ' ⟨φ, α'⟩) (β : L ≅ L') (n : ℕ)
    (hpow : ∀ g : 𝒜 d, (natTensorPowCongr β n).hom.app ⊤ (ψ.pow g.2 n) = ψ'.pow g.2 n)
    (a : 𝒜 (n * d)) :
    (natTensorPowCongr β n).hom.app ⊤ (ψ.toFun n a) = ψ'.toFun n a :=
  toFun_of_pow_of_isoFamily 𝒜 hgen hp hp' (natTensorPowCongr β) n hpow a

/-! ### Strict equivalence from equality of the classified morphisms -/

/-- **Two graded maps of one weight carried by two compatible pairs with the same first component
are strictly equivalent**, with `β = α⁻¹ ∘ α'`. -/
theorem sectionsEquiv_of_isCompatible {ψ : VeroneseSections 𝒜 d L}
    {ψ' : VeroneseSections 𝒜 d L'}
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤)
    (hgen' : ⨆ f : 𝒜 d, nonvanishingOpen Y L' (psiSection 𝒜 ψ' f) = ⊤)
    {φ : Y ⟶ (degreeOpen 𝒜 d).toScheme} {α : pullbackTwist 𝒜 φ (d : ℤ) ≅ L}
    {α' : pullbackTwist 𝒜 φ (d : ℤ) ≅ L'}
    (hp : IsCompatible 𝒜 ψ ⟨φ, α⟩) (hp' : IsCompatible 𝒜 ψ' ⟨φ, α'⟩) :
    SectionsEquiv 𝒜 ψ ψ' :=
  ⟨α.symm ≪≫ α', fun n x => natTensorPowCongr_toFun_of_pow 𝒜 hgen hp hp' _ n
    (fun g => natTensorPowCongr_pow_of_isCompatible 𝒜 hgen hgen' hp hp' n g.2) x⟩

/-- `sectionsEquiv_of_isCompatible` for two unbundled pairs whose first components are equal. -/
theorem sectionsEquiv_of_fst_eq {ψ : VeroneseSections 𝒜 d L} {ψ' : VeroneseSections 𝒜 d L'}
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤)
    (hgen' : ⨆ f : 𝒜 d, nonvanishingOpen Y L' (psiSection 𝒜 ψ' f) = ⊤)
    {p : Pair 𝒜 L d} {p' : Pair 𝒜 L' d} (hp : IsCompatible 𝒜 ψ p)
    (hp' : IsCompatible 𝒜 ψ' p') (hfst : p.1 = p'.1) :
    SectionsEquiv 𝒜 ψ ψ' := by
  obtain ⟨φ, α⟩ := p
  obtain ⟨φ', α'⟩ := p'
  obtain rfl : φ = φ' := hfst
  exact sectionsEquiv_of_isCompatible 𝒜 hgen hgen' hp hp'

/-- **Two graded maps of one weight that classify the same morphism `Y ⟶ Proj(A)` are strictly
equivalent**: the converse of
`Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom_eq_of_sectionsEquiv`.

The open immersion `U_d ⟶ Proj(A)` is a monomorphism, so the two morphisms `Y ⟶ U_d` of [Stacks,
Tag 01N8] are equal, and then `sectionsEquiv_of_fst_eq` applies to the two chosen pairs. -/
theorem sectionsEquiv_of_sameMorphism (hd : 0 < d) {ψ : VeroneseSections 𝒜 d L}
    {ψ' : VeroneseSections 𝒜 d L'}
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤)
    (hgen' : ⨆ f : 𝒜 d, nonvanishingOpen Y L' (psiSection 𝒜 ψ' f) = ⊤)
    (h : toProj 𝒜 (classifyingHom 𝒜 hd ψ hgen) = toProj 𝒜 (classifyingHom 𝒜 hd ψ' hgen')) :
    SectionsEquiv 𝒜 ψ ψ' :=
  sectionsEquiv_of_fst_eq 𝒜 hgen hgen' (isCompatible_classifyingPair 𝒜 hd ψ hgen)
    (isCompatible_classifyingPair 𝒜 hd ψ' hgen')
    ((cancel_mono ((degreeOpen 𝒜 d).ι)).mp h)

/-! ### Clause (4) implies clause (1) -/

/-- **Two triples of one and the same weight that classify the same morphism are carried into one
another by an isomorphism `β`.** This is the exact converse of
`Stacks.AlgebraicGeometry.ProjTripleVeroneseMorphism.classifyingMorphism_eq_of_agree`, with the
two weights only *equal* rather than syntactically identical and with the degreewise condition
stated for the two readings of one homogeneous element. -/
theorem agree_of_sameMorphism_of_deg_eq (t t' : Triple 𝒜 Y) (hdeg : t.deg = t'.deg)
    (h : SameMorphism 𝒜 t t') :
    ∃ β : t.module ≅ t'.module, ∀ (m : ℕ) (x : 𝒜 (m * t.deg)) (x' : 𝒜 (m * t'.deg)),
      (x : A) = (x' : A) →
      (natTensorPowCongr β m).hom.app ⊤ (t.psi.toFun m x) = t'.psi.toFun m x' := by
  obtain ⟨e, he, M, hM, ψ, hgen⟩ := t
  obtain ⟨e', he', M', hM', ψ', hgen'⟩ := t'
  obtain rfl : e = e' := hdeg
  have := hM
  have := hM'
  obtain ⟨β, hβ⟩ := sectionsEquiv_of_sameMorphism 𝒜 he hgen hgen' h
  refine ⟨β, fun m x x' hxx' => ?_⟩
  obtain rfl : x = x' := Subtype.ext hxx'
  exact hβ m x

/-- **Stacks Tag 01NB, clause (4) implies clause (1).** Let `(d, L, ψ)` and `(d', L', ψ')` be
triples over `Y` for the graded ring `A` which classify **the same morphism** `Y ⟶ Proj(A)`. Put
`n = lcm(d, d')`, `a = n/d` and `a' = n/d'`. Then there is an isomorphism
`β : L^{⊗ a} ≅ (L')^{⊗ a'}` such that `β ∘ ψ|_{A^{(n)}}` and `ψ'|_{A^{(n)}}` agree as graded ring
maps `A^{(n)} → Γ_*(Y, (L')^{⊗ a'})` — in degree `m` that `β^{⊗ m}` carries the value of
`ψ|_{A^{(n)}}` on a homogeneous element of degree `mn` to the value of `ψ'|_{A^{(n)}}` on it.

The two Veronese restrictions classify the same morphisms as the triples themselves
(`classifyingMorphism_veroneseRestrict`) and have the common weight `n`, so
`agree_of_sameMorphism_of_deg_eq` applies to them. This is the exact converse of
`Stacks.AlgebraicGeometry.ProjTripleVeroneseMorphism.sameMorphism_of_agreeAtLcm`, and with it the
four conditions of the tag form a cycle. -/
theorem agreeAtLcm_of_sameMorphism (t t' : Triple 𝒜 Y) (h : SameMorphism 𝒜 t t') :
    ∃ β : natTensorPow t.module (Nat.lcm t.deg t'.deg / t.deg) ≅
        natTensorPow t'.module (Nat.lcm t.deg t'.deg / t'.deg),
      ∀ (m : ℕ) (x : 𝒜 (m * (Nat.lcm t.deg t'.deg / t.deg * t.deg)))
        (x' : 𝒜 (m * (Nat.lcm t.deg t'.deg / t'.deg * t'.deg))), (x : A) = (x' : A) →
      (natTensorPowCongr β m).hom.app ⊤
          ((ProjVeroneseRestrict.veroneseRestrict 𝒜 t.psi
            (Nat.lcm t.deg t'.deg / t.deg)).toFun m x)
        = (ProjVeroneseRestrict.veroneseRestrict 𝒜 t'.psi
            (Nat.lcm t.deg t'.deg / t'.deg)).toFun m x' := by
  have hlcm : 0 < Nat.lcm t.deg t'.deg := Nat.lcm_pos t.deg_pos t'.deg_pos
  have ha : 0 < Nat.lcm t.deg t'.deg / t.deg :=
    Nat.div_pos (Nat.le_of_dvd hlcm (Nat.dvd_lcm_left t.deg t'.deg)) t.deg_pos
  have ha' : 0 < Nat.lcm t.deg t'.deg / t'.deg :=
    Nat.div_pos (Nat.le_of_dvd hlcm (Nat.dvd_lcm_right t.deg t'.deg)) t'.deg_pos
  have hn : Nat.lcm t.deg t'.deg / t.deg * t.deg
      = Nat.lcm t.deg t'.deg / t'.deg * t'.deg := by
    rw [Nat.div_mul_cancel (Nat.dvd_lcm_left t.deg t'.deg),
      Nat.div_mul_cancel (Nat.dvd_lcm_right t.deg t'.deg)]
  have hsame : SameMorphism 𝒜 (t.veroneseRestrict _ ha) (t'.veroneseRestrict _ ha') :=
    ((classifyingMorphism_veroneseRestrict 𝒜 t _ ha).trans h).trans
      (classifyingMorphism_veroneseRestrict 𝒜 t' _ ha').symm
  exact agree_of_sameMorphism_of_deg_eq 𝒜 _ _ hn hsame

/-- **Clauses (1) and (4) of [Stacks, Tag 01NB] are equivalent.** The two directions are
`agreeAtLcm_of_sameMorphism` and
`Stacks.AlgebraicGeometry.ProjTripleVeroneseMorphism.sameMorphism_of_agreeAtLcm`; that this
`Iff` elaborates is the check that the condition the one produces is the condition the other
consumes, so no clause string is attached to it. -/
theorem sameMorphism_iff_agreeAtLcm (t t' : Triple 𝒜 Y) :
    SameMorphism 𝒜 t t' ↔
      ∃ β : natTensorPow t.module (Nat.lcm t.deg t'.deg / t.deg) ≅
          natTensorPow t'.module (Nat.lcm t.deg t'.deg / t'.deg),
        ∀ (m : ℕ) (x : 𝒜 (m * (Nat.lcm t.deg t'.deg / t.deg * t.deg)))
          (x' : 𝒜 (m * (Nat.lcm t.deg t'.deg / t'.deg * t'.deg))), (x : A) = (x' : A) →
        (natTensorPowCongr β m).hom.app ⊤
            ((ProjVeroneseRestrict.veroneseRestrict 𝒜 t.psi
              (Nat.lcm t.deg t'.deg / t.deg)).toFun m x)
          = (ProjVeroneseRestrict.veroneseRestrict 𝒜 t'.psi
              (Nat.lcm t.deg t'.deg / t'.deg)).toFun m x' :=
  ⟨agreeAtLcm_of_sameMorphism 𝒜 t t', fun ⟨β, hβ⟩ =>
    ProjTripleVeroneseMorphism.sameMorphism_of_agreeAtLcm 𝒜 t t' β hβ⟩

end Stacks.AlgebraicGeometry.ProjTripleMorphismConverse

end
