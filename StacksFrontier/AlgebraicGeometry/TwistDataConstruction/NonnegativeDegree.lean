module

public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.DegreeOne
public import StacksFrontier.AlgebraicGeometry.TwistRigidityDegreeOne.Basic

/-!
# The twists of a relative projective spectrum in the nonnegative degrees

Let `S` be a scheme and `A` a commutative, nonnegatively graded, quasi-coherent graded
`𝒪_S`-algebra whose graded ring of sections over every affine open `U` of the base has, at every
point of `Proj Γ(U, A)`, a nonvanishing element of degree one — which holds whenever that ring is
generated in degree one over its degree-zero part, and so for the symmetric algebra of a
quasi-coherent module. This file proves that Tag 01NO's comparison of the twists on the charts of
two nested affine opens satisfies the nested cocycle condition
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle` **in every degree coming from a
natural number**, and not only in degree one. Consequently the degree-`N` twists of the charts
glue, for every `N : ℕ`, to an invertible quasi-coherent module `𝒪(N)` on the relative
projective spectrum, and for `A = Sym(E)` to the twists `𝒪_{𝐏(E)}(N)` of a projective bundle.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistDataConstruction.gluedTwistNatCast`: **the twist `𝒪(N)` on a
  relative projective spectrum**, for a graded algebra generated in degree one over every affine
  open of the base, together with `gluedTwistNatCastChartIso`, its identification with the
  absolute twist `𝒪(N)` on every affine chart.
* `Stacks.AlgebraicGeometry.TwistDataConstruction.twistNatCast`: **the twist
  `𝒪_{𝐏(E)}(N)`** on the projective bundle of a quasi-coherent module.

## Main results

* `Stacks.AlgebraicGeometry.TwistDataConstruction.eq_id`, `eq_id_of_generates` and `eq_id_res`:
  **rigidity of the twists in a nonnegative degree, with no multiplicativity hypothesis** — in
  absolute form, relative to a graded ring homomorphism, and for a nested pair of affine opens of
  the base of a quasi-coherent graded algebra.
* `Stacks.AlgebraicGeometry.TwistDataConstruction.legEndoChart_eq_id`: Tag 01NO's comparison for
  the outer pair of a chain of three affine opens, cancelled against the two comparisons through
  the middle chart, is the identity on the twist of every nonnegative degree.
* `Stacks.AlgebraicGeometry.TwistDataConstruction.isNestedCocycle_natCast` and
  `isNestedCocycle_natCast_of_adjoin`: **the nested cocycle in every nonnegative degree.**
* `Stacks.AlgebraicGeometry.TwistDataConstruction.isInvertibleModule_gluedTwistNatCast`,
  `isQuasicoherent_of_chartIso` and `isQuasicoherent_gluedTwistNatCast`: the glued twists are
  invertible and quasi-coherent.
* `Stacks.AlgebraicGeometry.TwistDataConstruction.twistNatCast_one`: in degree one the twist is
  the degree-one twist of Tag 01VM.

## The route

Tag 01MS trivializes `𝒪(N)` over the standard open `D₊(f)` of a homogeneous `f` of degree one by
multiplication by the section whose value at every point is the fraction `f ^ N / 1` — which is
the restriction of the global section that the homogeneous element `f ^ N` of degree `N`
determines. A family of endomorphisms of the twists is `𝒪`-linear on the sections over every
open, being a family of morphisms of sheaves of modules, so near a point where such an `f` does
not vanish it is the identity on `𝒪(N)` as soon as it fixes that one global section. Pointwise
generation makes the hypothesis relative: a degree-one element becomes an image of the graded ring
homomorphism after multiplication by a nonvanishing degree-zero image, and the `N`-th power of an
image is the image of an `N`-th power. No product of two sections of two twists occurs anywhere,
which is why no multiplicativity hypothesis is needed.

Applied to the three-leg endomorphism obtained by cancelling Tag 01NO's comparison for a chain
`W ⊆ W' ⊆ U` of affine opens of the base against the two comparisons through the chart of `W'`,
whose action on the homogeneous global sections of restricted elements is known in every degree,
this gives the cocycle; the glueing it feeds is the per-degree construction of
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.gluedTwist`.

## Why the nonnegative degrees only

For `n < 0` the trivialization of `𝒪(n)` over `D₊(f)` has the free generator `1 / f ^ (-n)`,
whose values are not the constant fractions `c / 1` of a homogeneous global section, and no
homogeneous global section of `𝒪(n)` exists to replace it. The family which is the identity in
every nonnegative degree and multiplication by a global unit in the negative ones fixes every
homogeneous global section and is `𝒪`-linear, so rigidity in a negative degree is false without
a multiplicative input. The input that closes the negative degrees is
`Stacks.AlgebraicGeometry.TwistRigidityDS.IsDegreeSectionMultiplicative` for Tag 01NO's
comparison — the commutation of the comparison with multiplication by one homogeneous section,
which is a morphism `𝒪(n) ⟶ 𝒪(K + n)` of sheaves of modules and involves no tensor product.

## What is not done here

**No `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` is constructed**, and nothing here
constructs the `algebra` field of one. That field is a sheaf of `ℤ`-graded algebras on the
relative projective spectrum: its pieces in the **negative** degrees are not constructed, for the
reason above, and neither its multiplication nor its unit is constructed in any degree — a
product on the glued pieces is well defined only once Tag 01NO's comparison is known to carry the
canonical product of absolute twist sections to the canonical product, which is not proved. The
homogeneous-section map `ψ` of a twist datum and its chart description
`Stacks.AlgebraicGeometry.Tag01NRPsiCompat.PsiChart` are not constructed either.

No `stacks` attribute is attached to any declaration below. Tag 01NR's existence assertion is
earned only by a complete twist datum; Tag 01O4's invertibility assertion is registered at
`Stacks.AlgebraicGeometry.TwistMapsInvertible.relativeProjTwists_isInvertible`, and the twists in
the nonnegative degrees alone are not a covering set for either.

## References

* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTrivialization
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.TwistDataConstruction

universe u u' w w' v

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local implicit_reducible]
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- A power of a homogeneous element of degree one is homogeneous of the degree of the
exponent. -/
public theorem pow_mem_one {R : Type u} {σ : Type w} [CommRing R] [SetLike σ R]
    [AddSubgroupClass σ R] (𝒜 : ℕ → σ) [GradedRing 𝒜] {g : R} (hg : g ∈ 𝒜 1) (N : ℕ) :
    g ^ N ∈ 𝒜 N := by
  simpa using SetLike.pow_mem_graded N hg

section Rigidity

variable {R : Type u} {σ : Type w} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {f : R}

/-- The value of the trivializing section of `𝒪(n d)` on `D₊(f)` at a nonnegative index `n = N`
is the fraction `f ^ N / 1`: the numerator is `f ^ N` and the denominator `f ^ 0 = 1`. -/
public theorem trivializingFun_natCast (N : ℕ) {W : Opens (ProjectiveSpectrum.top 𝒜)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒜 f) (x : W) :
    trivializingFun 𝒜 (N : ℤ) hW x =
      LocalizedModule.mk (f ^ N) (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
  LocalizedModule.mk_eq.mpr ⟨1, by simp⟩

variable {α : ∀ n : ℤ, twistingSheaf 𝒜 n ⟶ twistingSheaf 𝒜 n}

/-- **A family of twist endomorphisms fixing the global section of `f ^ N` is the identity on the
sections of `𝒪(N)` over every open of `D₊(f)`**, for `f` homogeneous of degree one.

Tag 01MS trivializes `𝒪(N)` over `D₊(f)` by multiplication by the section whose value is
`f ^ N / 1`, so a section there is a multiple of that one section, which the hypothesis fixes;
the family is `𝒪`-linear, being a family of morphisms of sheaves of modules. -/
public theorem app_eq_self_of_le_basicOpen {m : ℤ} {N : ℕ}
    (hm : (N : ℤ) * ((1 : ℕ) : ℤ) = m) (hf : f ∈ 𝒜 1) (hfN : f ^ N ∈ 𝒜 N)
    (hfix : (α (N : ℤ)).val.app (op ⊤) (degreeSection 𝒜 N ⟨f ^ N, hfN⟩) =
      degreeSection 𝒜 N ⟨f ^ N, hfN⟩)
    {W : Opens (ProjectiveSpectrum.top 𝒜)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (t : (twistingSheaf 𝒜 m).val.obj (op W)) :
    (α m).val.app (op W) t = t := by
  subst hm
  have hgen : (α ((N : ℤ) * ((1 : ℕ) : ℤ))).val.app (op W)
      (trivializingSection 𝒜 hf (N : ℤ) hW) = trivializingSection 𝒜 hf (N : ℤ) hW :=
    RelativeTwistRigidity.app_eq_self_of_values_mkOne' (α := α) (N := N) (by simp) hfN hfix W
      (trivializingSection 𝒜 hf (N : ℤ) hW) fun y => trivializingFun_natCast N hW y
  obtain ⟨r, hr⟩ := (bijective_trivializingHom 𝒜 hf (N : ℤ) hW).surjective t
  have hrs : r • trivializingSection 𝒜 hf (N : ℤ) hW = t := hr
  exact (congrArg ((α ((N : ℤ) * ((1 : ℕ) : ℤ))).val.app (op W)) hrs.symm).trans
    ((((α ((N : ℤ) * ((1 : ℕ) : ℤ))).val.app (op W)).hom.map_smul r _).trans
      ((congrArg (fun z : (twistingSheaf 𝒜 ((N : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op W) => r • z)
        hgen).trans hrs))

/-- **Rigidity in a nonnegative degree on sections, with no multiplicativity hypothesis.** If at
every point of `Proj 𝒜` there is a homogeneous element of degree one which does not vanish there
and whose `N`-th power has a fixed global section, then the family is the identity on the
sections of `𝒪(N)` over every open.

The element may be chosen anew at each point, which is what makes the hypothesis reachable. -/
public theorem app_eq_self (N : ℕ)
    (hpt : ∀ x : ProjectiveSpectrum.top 𝒜, ∃ (g : R) (hg : g ∈ 𝒜 1),
      g ∉ x.asHomogeneousIdeal ∧
      (α (N : ℤ)).val.app (op ⊤) (degreeSection 𝒜 N ⟨g ^ N, pow_mem_one 𝒜 hg N⟩) =
        degreeSection 𝒜 N ⟨g ^ N, pow_mem_one 𝒜 hg N⟩)
    (V : Opens (ProjectiveSpectrum.top 𝒜))
    (t : (twistingSheaf 𝒜 (N : ℤ)).val.obj (op V)) :
    (α (N : ℤ)).val.app (op V) t = t := by
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨g, hg, hnv, hfixg⟩ := hpt x.1
  have hmem : x.1 ∈ V ⊓ ProjectiveSpectrum.basicOpen 𝒜 g := ⟨x.2, hnv⟩
  have hle : V ⊓ ProjectiveSpectrum.basicOpen 𝒜 g ≤ V := inf_le_left
  have hlocal := app_eq_self_of_le_basicOpen (α := α) (by simp) hg (pow_mem_one 𝒜 hg N) hfixg
    (inf_le_right : V ⊓ ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 g)
    ((twistingSheaf 𝒜 (N : ℤ)).val.map (homOfLE hle).op t)
  calc ((α (N : ℤ)).val.app (op V) t).1 x
      = ((twistingSheaf 𝒜 (N : ℤ)).val.map (homOfLE hle).op
          ((α (N : ℤ)).val.app (op V) t)).1 ⟨x.1, hmem⟩ := rfl
    _ = ((α (N : ℤ)).val.app (op (V ⊓ ProjectiveSpectrum.basicOpen 𝒜 g))
          ((twistingSheaf 𝒜 (N : ℤ)).val.map (homOfLE hle).op t)).1 ⟨x.1, hmem⟩ :=
          TwistRigidity.twist_val_congr 𝒜
            (PresheafOfModules.naturality_apply (α (N : ℤ)).val (homOfLE hle).op t).symm _
    _ = ((twistingSheaf 𝒜 (N : ℤ)).val.map (homOfLE hle).op t).1 ⟨x.1, hmem⟩ :=
          TwistRigidity.twist_val_congr 𝒜 hlocal _
    _ = t.1 x := rfl

/-- **Rigidity in a nonnegative degree, with no multiplicativity hypothesis.** A family of
endomorphisms of the graded twists on `Proj 𝒜` is the identity in degree `N` as soon as, at every
point, some degree-one element nonvanishing there has the global section of its `N`-th power
fixed. -/
public theorem eq_id (N : ℕ)
    (hpt : ∀ x : ProjectiveSpectrum.top 𝒜, ∃ (g : R) (hg : g ∈ 𝒜 1),
      g ∉ x.asHomogeneousIdeal ∧
      (α (N : ℤ)).val.app (op ⊤) (degreeSection 𝒜 N ⟨g ^ N, pow_mem_one 𝒜 hg N⟩) =
        degreeSection 𝒜 N ⟨g ^ N, pow_mem_one 𝒜 hg N⟩) :
    α (N : ℤ) = 𝟙 (twistingSheaf 𝒜 (N : ℤ)) :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun t => app_eq_self N hpt V.unop t))

section Res

variable {R' : Type u'} {σ' : Type w'} [CommRing R'] [SetLike σ' R'] [AddSubgroupClass σ' R']
  {ℬ : ℕ → σ'} [GradedRing ℬ]

/-- **Rigidity in a nonnegative degree, relative to a graded ring homomorphism, with no
multiplicativity hypothesis.** The family need only fix the global sections attached to the
images of `ψ : ℬ →+*ᵍ 𝒜`; what is assumed of `𝒜` itself is that at every point of `Proj 𝒜` some
element of degree one does not vanish.

A degree-one `a` nonvanishing at `x` becomes, after multiplication by a degree-zero image of `ψ`
nonvanishing at `x`, an image of `ψ` of degree one; its `N`-th power is then the image of the
`N`-th power of the preimage, so its global section is fixed. -/
public theorem eq_id_of_generates (N : ℕ) {ψ : ℬ →+*ᵍ 𝒜}
    (hdeg : ∀ x : ProjectiveSpectrum 𝒜, ∃ a : 𝒜 1, (a : R) ∉ x.asHomogeneousIdeal)
    (hgen : RelativeTwistRigidity.Generates ψ)
    (hfix : RelativeTwistRigidity.FixesResDegreeSections ψ α) :
    α (N : ℤ) = 𝟙 (twistingSheaf 𝒜 (N : ℤ)) := by
  refine eq_id N fun x => ?_
  obtain ⟨a, ha⟩ := hdeg x
  obtain ⟨d, c, hnvd, heq⟩ := hgen 1 a x
  have hmemg : (a : R) * ψ (d : R') ∈ 𝒜 1 := heq ▸ ψ.map_mem c.2
  exact ⟨(a : R) * ψ (d : R'), hmemg,
    Submonoid.mul_mem (Ideal.primeCompl x.asHomogeneousIdeal.toIdeal) ha hnvd,
    RelativeTwistRigidity.fixes_of_eq_res hfix N ⟨(c : R') ^ N, pow_mem_one ℬ c.2 N⟩
      ⟨((a : R) * ψ (d : R')) ^ N, pow_mem_one 𝒜 hmemg N⟩
      ((congrArg (· ^ N) heq).trans (map_pow ψ (c : R') N).symm)⟩

end Res

section Nested

variable {X : Scheme.{v}} (A : SheafGradedAlgebra X) (U V : X.Opens) (h : U ≤ V)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V)

include hU hV

/-- **Relative rigidity in a nonnegative degree for a nested pair of affine opens, with no
multiplicativity hypothesis.** A family of endomorphisms of the twists on `Proj Γ(U, A)` which
fixes the global sections attached to the restrictions of the homogeneous elements over a larger
affine open is the identity in every degree coming from a natural number, provided the graded ring
of sections over `U` has, at every point of its `Proj`, a nonvanishing element of degree one. -/
public theorem eq_id_res (N : ℕ)
    {α : ∀ n : ℤ, twistingSheaf (A.grading U) n ⟶ twistingSheaf (A.grading U) n}
    (hdeg : ∀ x : ProjectiveSpectrum (A.grading U),
      ∃ a : (A.grading U) 1, (a : A.sectionRing U) ∉ x.asHomogeneousIdeal)
    (hfix : RelativeTwistRigidity.FixesResDegreeSections (A.res h) α) :
    α (N : ℤ) = 𝟙 (twistingSheaf (A.grading U) (N : ℤ)) :=
  eq_id_of_generates N hdeg (RelativeTwistRigidity.generates_res A U V h hU hV) hfix

end Nested

end Rigidity

section Cocycle

open Stacks.AlgebraicGeometry.ChartCocycleRigidity
open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.AlgebraicGeometry.NestedCocycleReduction
open Stacks.AlgebraicGeometry.NestedCocycleTail
open Stacks.AlgebraicGeometry.RelativeProj

attribute [local implicit_reducible] AlgebraicGeometry.Proj

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- **Rigidity in a nonnegative degree for the endomorphism obtained by cancelling three
comparisons.** Let three open immersions out of and into the chart of an affine open `W` of the
base satisfy `p₁ ≫ p₂ = p₃`, and let three comparisons identify the restriction of each outer
module with the next one in, the two inner targets being the twists on that chart. If the
resulting endomorphism fixes, in every degree, the homogeneous global section attached to the
restriction to `W` of a homogeneous element over a larger affine open `U`, then it is the identity
in every degree coming from a natural number, provided the graded ring of sections over `W` has a
nonvanishing degree-one element at every point of its `Proj`. -/
public theorem eq_id_res_legEndo (W U : S.Opens) (h : W ≤ U) (hW : IsAffineOpen W)
    (hU : IsAffineOpen U) (N : ℕ)
    {Y Z : Scheme.{u}} (p₁ : AlgebraicGeometry.Proj (A.grading W) ⟶ Z) (p₂ : Z ⟶ Y)
    (p₃ : AlgebraicGeometry.Proj (A.grading W) ⟶ Y)
    [IsOpenImmersion p₁] [IsOpenImmersion p₂] [IsOpenImmersion p₃] (hp : p₁ ≫ p₂ = p₃)
    {M : ℤ → Y.Modules} {Q : ℤ → Z.Modules}
    (e₂ : ∀ n : ℤ, (Scheme.Modules.restrictFunctor p₂).obj (M n) ≅ Q n)
    (e₁ : ∀ n : ℤ, (Scheme.Modules.restrictFunctor p₁).obj (Q n) ≅ twistingSheaf (A.grading W) n)
    (e₃ : ∀ n : ℤ, (Scheme.Modules.restrictFunctor p₃).obj (M n) ≅ twistingSheaf (A.grading W) n)
    (hdeg : ∀ x : ProjectiveSpectrum (A.grading W),
      ∃ a : (A.grading W) 1, (a : A.sectionRing W) ∉ x.asHomogeneousIdeal)
    (hfix : ∀ (k : ℕ) (c : (A.grading U) k),
      (legEndo p₁ p₂ p₃ hp (e₂ (k : ℤ)) (e₁ (k : ℤ)) (e₃ (k : ℤ))).val.app (op ⊤)
          (degreeSection (A.grading W) k ⟨A.res h c, (A.res h).map_mem c.2⟩) =
        degreeSection (A.grading W) k ⟨A.res h c, (A.res h).map_mem c.2⟩) :
    legEndo p₁ p₂ p₃ hp (e₂ (N : ℤ)) (e₁ (N : ℤ)) (e₃ (N : ℤ)) =
      𝟙 (twistingSheaf (A.grading W) (N : ℤ)) :=
  eq_id_res A W U h hW hU N
    (α := fun n => legEndo p₁ p₂ p₃ hp (e₂ n) (e₁ n) (e₃ n)) hdeg hfix

/-- **Tag 01NO's comparison for the outer pair of a chain of affine opens, cancelled against the
two comparisons through the middle chart, is the identity on the twist of any nonnegative
degree.** The one hypothesis is that at every point of `Proj Γ(W, A)` some degree-one element does
not vanish. -/
public theorem legEndoChart_eq_id (W W' U : S.Opens) (hWW' : W ≤ W') (hW'U : W' ≤ U)
    (hWU : W ≤ U) (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hU : IsAffineOpen U)
    (hdeg : ∀ x : ProjectiveSpectrum (A.grading W),
      ∃ a : (A.grading W) 1, (a : A.sectionRing W) ∉ x.asHomogeneousIdeal) (N : ℕ) :
    legEndo (projInclusionMap A W W' hWW' hW hW')
        (projInclusionMap A W' U hW'U hW' hU) (projInclusionMap A W U hWU hW hU)
        (RelativeProjTwistGlue.projInclusionMap_comp A W W' U hWW' hW'U hW hW' hU)
        (restrictTwistIso A W' U hW'U hW' hU (N : ℤ))
        (restrictTwistIso A W W' hWW' hW hW' (N : ℤ))
        (restrictTwistIso A W U hWU hW hU (N : ℤ)) =
      𝟙 (twistingSheaf (A.grading W) (N : ℤ)) :=
  eq_id_res_legEndo A W U hWU hW hU N (projInclusionMap A W W' hWW' hW hW')
    (projInclusionMap A W' U hW'U hW' hU) (projInclusionMap A W U hWU hW hU)
    (RelativeProjTwistGlue.projInclusionMap_comp A W W' U hWW' hW'U hW hW' hU)
    (restrictTwistIso A W' U hW'U hW' hU) (restrictTwistIso A W W' hWW' hW hW')
    (restrictTwistIso A W U hWU hW hU) hdeg
    (legEndoChart_val_app_top A W W' U hWW' hW'U hWU hW hW' hU)

/-- **The nested cocycle of Tag 01NO's twist comparison in every nonnegative degree.** For every
chain of affine opens of the base and every open of the relative projective spectrum inside the
inverse images of the two smaller ones, the pushed-forward twist comparison for the outer pair is
the composite of the two comparisons through the middle chart.

The hypothesis is that the graded ring of sections over every affine open of the base has, at
every point of its `Proj`, a nonvanishing element of degree one. -/
public theorem isNestedCocycle_natCast
    (hdeg : ∀ (W : S.Opens), IsAffineOpen W → ∀ x : ProjectiveSpectrum (A.grading W),
      ∃ a : (A.grading W) 1, (a : A.sectionRing W) ∉ x.asHomogeneousIdeal) (N : ℕ) :
    IsNestedCocycle A (N : ℤ) := by
  intro W W' U hWW' hW'U hWU hW hW' hU V hV hV'
  refine isComposite_of_eval (cmpNested A W' U hW'U hW' hU (N : ℤ))
      (cmpNested A W W' hWW' hW hW' (N : ℤ)) (cmpNested A W U hWU hW hU (N : ℤ)) V hV hV' _ _ _
      (cmpNested_app_val A W' U hW'U hW' hU (N : ℤ) V hV')
      (cmpNested_app_val A W W' hWW' hW hW' (N : ℤ) V hV)
      (cmpNested_app_val A W U hWU hW hU (N : ℤ) V hV) ?_
  exact isEvalComposite_of_legEndo_eq_id (projInclusionMap A W W' hWW' hW hW')
    (projInclusionMap A W' U hW'U hW' hU) (projInclusionMap A W U hWU hW hU)
    (RelativeProjTwistGlue.projInclusionMap_comp A W W' U hWW' hW'U hW hW' hU)
    (restrictTwistIso A W' U hW'U hW' hU (N : ℤ))
    (restrictTwistIso A W W' hWW' hW hW' (N : ℤ))
    (restrictTwistIso A W U hWU hW hU (N : ℤ))
    (legEndoChart_eq_id A W W' U hWW' hW'U hWU hW hW' hU (hdeg W hW) N)
    (homOfLE (image_preimage_le_preimage A W W' hWW' hW hW' V))
    (homOfLE (image_preimage_le_preimage A W' U hW'U hW' hU V))
    (homOfLE (image_preimage_le_preimage A W U hWU hW hU V))

end Cocycle

section Glued

open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwistQcoh
open Stacks.Tag01VMVeryAmple

attribute [local implicit_reducible] AlgebraicGeometry.Proj

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)
  (hgen : ∀ U : S.Opens, IsAffineOpen U →
    Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)

include hgen

/-- **The nested cocycle in every nonnegative degree for a graded algebra generated in degree
one over every affine open of the base.** Generation supplies, at every point of every chart, a
nonvanishing element of degree one. -/
public theorem isNestedCocycle_natCast_of_adjoin (N : ℕ) : IsNestedCocycle A (N : ℤ) :=
  isNestedCocycle_natCast A
    (fun U hU => TwistRigidityDegreeOne.exists_degreeOne_notMem_of_adjoin_eq_top
      (hgen U hU)) N

/-- **The twist `𝒪(N)` on the relative projective spectrum**, for every natural number `N`: the
degree-`N` twists of the affine charts, glued along Tag 01NO's comparisons. -/
public def gluedTwistNatCast (N : ℕ) : (relativeProj A).scheme.Modules :=
  gluedTwist A (N : ℤ) (isNestedCocycle_natCast_of_adjoin A hgen N)

/-- **The chart identification of `𝒪(N)`**: over each affine open `U` of the base it restricts
along the chart to the absolute twist `𝒪(N)` of `Proj Γ(U, A)`. -/
public def gluedTwistNatCastChartIso (N : ℕ) (U : S.Opens) (hU : IsAffineOpen U) :
    Scheme.Modules.restrict (gluedTwistNatCast A hgen N) ((relativeProj A).chart U hU) ≅
      twistingSheaf (A.grading U) (N : ℤ) :=
  gluedChartIso A (N : ℤ) (isNestedCocycle_natCast_of_adjoin A hgen N) U hU

/-- **`𝒪(N)` is an invertible `𝒪`-module** for every natural number `N`: it is the absolute
twist `𝒪(N)` on each chart, and the graded section ring over each affine open of the base is
generated in degree one. -/
public theorem isInvertibleModule_gluedTwistNatCast (N : ℕ) :
    Stacks.Ample.IsInvertibleModule (relativeProj A).scheme (gluedTwistNatCast A hgen N) :=
  isInvertibleModule_of_chartIso (gluedTwistNatCast A hgen N) (N : ℤ)
    (gluedTwistNatCastChartIso A hgen N) hgen

omit hgen in
/-- **Quasi-coherence of a glued twist is free from its chart identifications.** A module on a
relative projective spectrum which restricts on every affine chart to the absolute twist that
chart carries is quasi-coherent. -/
public theorem isQuasicoherent_of_chartIso (M : (relativeProj A).scheme.Modules) (n : ℤ)
    (e : ∀ (U : S.Opens) (hU : IsAffineOpen U),
      Scheme.Modules.restrict M ((relativeProj A).chart U hU) ≅ twistingSheaf (A.grading U) n) :
    M.IsQuasicoherent := by
  refine Stacks.Modules.isQuasicoherent_of_restrict M
    (fun U : S.affineOpens => (relativeProj A).toBase ⁻¹ᵁ (U.1 : S.Opens))
    (RelativeProjTwistGlue.iSup_toBase_preimage_eq_top (relativeProj A)) ?_
  rintro ⟨U, hU⟩
  have : IsOpenImmersion ((relativeProj A).chart U hU) :=
    RelativeProjTwistGlue.isOpenImmersion_chart (relativeProj A) U hU
  have hqc := Stacks.Descent.isQuasicoherent_of_iso
    (X := AlgebraicGeometry.Proj (A.grading U)) (e U hU).symm
    (inferInstance : (twistingSheaf (A.grading U) n).IsQuasicoherent)
  have hqc' : (Scheme.Modules.restrict (Scheme.Modules.restrict M
      ((relativeProj A).chart U hU)) (chartIsoPreimage (A := A) U hU).hom).IsQuasicoherent :=
    inferInstance
  exact Stacks.Descent.isQuasicoherent_of_iso
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.restrictIsoOfIsoOver
      (X := (relativeProj A).scheme) (Y := AlgebraicGeometry.Proj (A.grading U))
      M ((relativeProj A).chart U hU) ((relativeProj A).toBase ⁻¹ᵁ U)
      (chartIsoPreimage (A := A) U hU) (chartIsoPreimage_hom_comp U hU)) hqc'

/-- **The twist `𝒪(N)` is quasi-coherent**, for every natural number `N`. -/
public theorem isQuasicoherent_gluedTwistNatCast (N : ℕ) :
    (gluedTwistNatCast A hgen N).IsQuasicoherent :=
  isQuasicoherent_of_chartIso A (gluedTwistNatCast A hgen N) (N : ℤ)
    (gluedTwistNatCastChartIso A hgen N)

end Glued

section Bundle

open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.Tag01VMRelativeVeryAmple
open Stacks.Tag01VMVeryAmple

attribute [local implicit_reducible] AlgebraicGeometry.Proj

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]

/-- **The twist `𝒪_{𝐏(E)}(N)` on the projective bundle of a quasi-coherent module**, for every
natural number `N`: the degree-`N` twists of the affine charts of `Proj_S(Sym(E))`, glued along
Tag 01NO's comparisons. -/
public def twistNatCast (N : ℕ) : (relativeProj (symAlgebra E)).scheme.Modules :=
  gluedTwistNatCast (symAlgebra E) (adjoin_symAlgebra_eq_top E) N

/-- In degree one the twist is the degree-one twist `𝒪_{𝐏(E)}(1)`. -/
public theorem twistNatCast_one : twistNatCast E 1 = twistOne E := rfl

/-- **`𝒪_{𝐏(E)}(N)` is an invertible `𝒪_{𝐏(E)}`-module**, for every natural number `N`. -/
public theorem isInvertibleModule_twistNatCast (N : ℕ) :
    Stacks.Ample.IsInvertibleModule (relativeProj (symAlgebra E)).scheme (twistNatCast E N) :=
  isInvertibleModule_gluedTwistNatCast (symAlgebra E) (adjoin_symAlgebra_eq_top E) N

/-- **`𝒪_{𝐏(E)}(N)` is quasi-coherent**, for every natural number `N`. -/
public theorem isQuasicoherent_twistNatCast (N : ℕ) : (twistNatCast E N).IsQuasicoherent :=
  isQuasicoherent_gluedTwistNatCast (symAlgebra E) (adjoin_symAlgebra_eq_top E) N

end Bundle

end Stacks.AlgebraicGeometry.TwistDataConstruction

end
