module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModuleGraded
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceQuasicoherentModule
public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.ProjTwistRestriction

/-!
# Multiplication by a homogeneous scalar and the trivializing sections of the twists

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring, `X = Proj 𝒮`, let `f ∈ 𝒮 d` and `g ∈ 𝒮 e` be
homogeneous, and let `ℱ` be an **arbitrary** sheaf of `𝒪_X`-modules. On an open
`W ⊆ D₊(f) ∩ D₊(g)` the two trivializations behind
`Stacks.AlgebraicGeometry.ProjTwistRestriction.mulTrivSection` are available at once: a section
`t` of `ℱ` over `W` has the two images `t ⊗ f ^ n` in `Γ(W, ℱ(nd))` and `t ⊗ g ^ m` in
`Γ(W, ℱ(me))`. This file proves that whenever the two trivializing sections are related by a
homogeneous scalar, `g ^ m = f ^ n c`, the morphism

`ℱ(nd) ⟶ ℱ(me)`

of multiplication by `c` carries the first image to the second. Dividing back, the map

`Γ(W, ℱ(nd)) → Γ(W, ℱ)`, `t ⊗ f ^ n ↦ t`

is unchanged when the numerator is multiplied by `c` and the denominator `f ^ n` is replaced by
`g ^ m`: the division does not depend on which denominator is used.

## Which multiplication, and why

Two morphisms in this library deserve the name "multiplication on the twists of `ℱ`".

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafMultiplicationMap`, Tag 03GJ's
  `𝒪(n) ⊗ ℱ(m) ⟶ ℱ(n + m)`, assembled from the associator and the braiding of the sheafified
  tensor product. Nothing in the library computes it on a pure tensor of sections.
* Multiplication by a **fixed** homogeneous scalar `c ∈ 𝒮 i`, namely `𝟙_ℱ` tensored with the
  morphism `𝒪(n) ⟶ 𝒪(k)` of twisting sheaves that `c` induces. This is
  `Stacks.AlgebraicGeometry.ProjTwistedSections.twistSheafScalarMap`, and it is the morphism
  whose global sections carry the `S`-action on `⨁_{n ∈ ℤ} Γ(X, ℱ(n))` and on
  `⨁_{d ≥ 0} Γ(X, ℱ(d))`; the second is spelled
  `Stacks.AlgebraicGeometry.ProjTwistSectionModule.twistMul`, built from
  `Stacks.AlgebraicGeometry.ProjTwistSectionModule.homogeneousMul`, and
  `homogeneousMul_eq_twistScalarSheafMap` below identifies the two spellings of the underlying
  morphism of twisting sheaves.

The law proved here is for the second, and that is the one a comparison map out of the sheaf
associated to a graded module of twisted sections needs: a degree-zero fraction `x / f ^ n` has
many representatives, two of them differ by exactly a multiplication by a homogeneous scalar of
the kind above, and so the law is the well-definedness of `x / f ^ n ↦ x|_{D₊(f)} / f ^ n`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistRestriction.twistScalarSheafMap_trivializingSection`:
  multiplication by `c` carries the trivializing section `f ^ n` of `𝒪(nd)` to the trivializing
  section `g ^ m` of `𝒪(me)`, when `g ^ m = f ^ n c`.
* `Stacks.AlgebraicGeometry.ProjTwistRestriction.twistSheafScalarMap_mulTrivSection`: **the same
  after tensoring with `ℱ`** — multiplication by `c` carries `t ⊗ f ^ n` to `t ⊗ g ^ m`.
* `Stacks.AlgebraicGeometry.ProjTwistRestriction.twistSheafScalarMap_mulTrivSection_pow`: the
  case `g = f`, `c = f ^ k`: **multiplying by `f ^ n` and then by `f ^ k` is multiplying by
  `f ^ (n + k)`**, the additivity in the exponent.
* `Stacks.AlgebraicGeometry.ProjTwistRestriction.eq_of_mulTrivSection_twistSheafScalarMap`:
  **division by the trivializing section does not depend on the denominator** — dividing by
  `g ^ m` after multiplying by `c` gives the same section of `ℱ` as dividing by `f ^ n`.
* `Stacks.AlgebraicGeometry.ProjTwistRestriction.twistScalarSheafMap_pow_trivializingSection`:
  the law for `g = f` and `c = f ^ m` **at an arbitrary integer exponent `n`** — multiplication
  by `f ^ m` carries the trivializing section `f ^ n` of `𝒪(nd)` to the trivializing section
  `f ^ (n + m)` of `𝒪((n + m)d)`.
* `Stacks.AlgebraicGeometry.ProjTwistRestriction`
  `.bijective_twistScalarSheafMap_app_of_trivializingSection`: a morphism of twisting sheaves
  carrying a trivializing section to a trivializing section is **bijective on the sections over
  every open inside `D₊(f)`**.
* `Stacks.AlgebraicGeometry.ProjTwistRestriction.bijective_twistScalarSheafMap_pow_app`:
  **multiplication by `f ^ m` is invertible on `D₊(f)`, as a morphism of twisting sheaves**, for
  every integer twist.
* `Stacks.AlgebraicGeometry.ProjTwistRestriction.twistSheafScalarMap_mulTrivSection_pow_int` and
  `…bijective_twistSheafScalarMap_pow_app`: the same **on the twists of an arbitrary sheaf of
  modules `ℱ`** — multiplication by `f ^ m` carries `t ⊗ f ^ n` to `t ⊗ f ^ (n + m)` and is
  bijective on `Γ(W, ℱ(nd))` for every `W ⊆ D₊(f)` and every integer `n`.

## Implementation notes

In the statements comparing two different trivializing elements `f` and `g` the exponents `n`
and `m` are natural numbers, while the trivializing sections
`Stacks.AlgebraicGeometry.ProjTrivialization.trivializingSection` are defined for an arbitrary
integer exponent. Natural exponents are what those statements need — a degree-zero fraction of a
graded module has for denominator a genuine power of `f` — and they are what makes the relation
`g ^ m = f ^ n c` an equation in `S` rather than in a localization: at a natural exponent the
trivializing section is the fraction `f ^ n / 1`, so the identity to check at a point is the
given one.

**The one-element case is stated at an integer exponent instead.** With `g = f` and `c = f ^ m`
there is no relation in `S` to be had — `f ^ (n + m) = f ^ n · f ^ m` is an identity of genuine
fractions once `n < 0` — and the comparison happens inside the local ring, where both sides are
`Localization.mk` of a power of `f` over a power of `f`. The whole content is then the single
`ℕ`-equation between the four `Int.toNat` exponents, which `omega` closes from `n + m = j`; no
ring normalization can do it, which is why `mk_pow_eq_mk_pow` is separated out. The integer
exponent is not a generalisation for its own sake: a consumer twisting down by `c` from an
unrestricted twist `q : ℤ` lands on `q - c`, which is negative for small `q`.

The degrees of the source and the target twist are carried as the products `(n : ℤ) * d` and
`(m : ℤ) * e`, and the degree of the scalar enters only through the hypothesis
`(i : ℤ) + (n : ℤ) * d = (m : ℤ) * e`, which is a proposition; so no transport along an equality
of degrees occurs anywhere below.

`map_mul_mk` is needed because the fibres of a twisting sheaf are written as a `Localization` of
the local ring while the morphism induced on the associated sheaves acts by
`LocalizedModule.map`: the two descriptions of a fraction are definitionally equal, but
`LocalizedModule.map_mk` does not match the first syntactically.

**Division is phrased as a uniqueness statement, not through the isomorphism of sheaves.** The
isomorphism `ℱ(nd)|_{D₊(f)} ≅ ℱ|_{D₊(f)}` of
`Stacks.AlgebraicGeometry.ProjTwistRestriction.twistRestrictIso` is the natural way to say
"divide by `f ^ n`", but it lives on the localized site at `D₊(f)`, where the ring of sections has
a spelling of its own; using it in the same statement as the multiplication morphism, which lives
on the ringed space `Proj 𝒮`, makes the elaborator reconcile three descriptions of that ring at
once and exhausts the heartbeat budget at `whnf`. The uniqueness form below mentions only
`mulTrivSection` and its injectivity, and says the same thing.

## References

* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 03GJ](https://stacks.math.columbia.edu/tag/03GJ)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)

## What is not done

**No `@[stacks]` attribute is attached.** Nothing here states a clause of a tag: the triviality
and the invertibility of `𝒪(nd)` on `D₊(f)` are Tag 01MS and are tagged in
`StacksFrontier/AlgebraicGeometry/ProjTrivialization/Basic.lean`, and the statements below are an
input to a comparison map that is not constructed here.

**The local comparison is built elsewhere, from the law proved here.** For the ℕ-graded module
`⨁_{d ≥ 0} Γ(X, ℱ(d))` of Tag 03GM it is
`Stacks.AlgebraicGeometry.ProjTwistLocalComparison.chartHom`, whose compatibility with
restriction `chartHom_restrict` is the use the law below is stated for: the homogeneous `c` and
the exponent `m` with `g ^ m = f ^ n c`, together with the degree of `c`, come from
`ProjectiveSpectrum.exists_pow_eq_mul_of_basicOpen_le_degree`, which needs no hypothesis beyond
the containment of the two standard opens. The `Γ(D₊(f), 𝒪)`-linearity of the chart map is
obtained there by transferring the semilinearity of
`Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree` along the surjection
`AlgebraicGeometry.Proj.awayToSection`.

**Tag 0B5I's comparison is still not built**, its module being the ℤ-graded
`⨁_{n ∈ ℤ} Γ(X, ℱ(n))` rather than the ℕ-graded one.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection
  tensorSheafMap_app_toTensorSheafSection)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap twistSheafScalarMap)
open Stacks.AlgebraicGeometry.ProjTrivialization (trivializingSection trivializingFun
  projRingSheaf)
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.ProjTwistRestriction

universe u w

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

variable {f g : S} {d e : ℕ}

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### Two elementary facts about fractions -/

/-- Localizing multiplication by a ring element and evaluating on a fraction multiplies the
numerator. The fraction is written as `Localization.mk`, the spelling in which the fibres of a
twisting sheaf are given. -/
theorem map_mul_mk {T : Submonoid S} (a u : S) (v : T) :
    LocalizedModule.map T (LinearMap.mul S S a) (Localization.mk u v) =
      Localization.mk (a * u) v := by
  change LocalizedModule.map T (LinearMap.mul S S a) (LocalizedModule.mk u v) = _
  rw [LocalizedModule.map_mk]
  rfl

/-- Two fractions with equal numerators and equal denominators are equal. The denominators are
given as elements of the submonoid together with their membership, which is the form the
trivializing sections produce. -/
private theorem mk_eq_mk_of_eq {T : Submonoid S} (a b u v : S) (hu : u ∈ T) (hv : v ∈ T)
    (hab : a = b) (huv : u = v) :
    Localization.mk a (⟨u, hu⟩ : T) = Localization.mk b ⟨v, hv⟩ := by
  subst hab huv
  rfl

/-- A power of a homogeneous element of degree `d` is homogeneous of degree `k * d`. -/
theorem pow_mem_degree (hf : f ∈ 𝒮 d) (k : ℕ) : f ^ k ∈ 𝒮 (k * d) := by
  simpa [smul_eq_mul] using SetLike.pow_mem_graded k hf

/-! ### The two spellings of multiplication on the twisting sheaves -/

/-- Multiplication by a homogeneous scalar on the twisting sheaves has two names in this
library and they are the same morphism: both are the associated-sheaf image of multiplication by
that scalar, and the two hypotheses on the degrees are propositions. -/
theorem homogeneousMul_eq_twistScalarSheafMap {i : ℕ} {a : S} (ha : a ∈ 𝒮 i) (n k : ℤ)
    (hk : (i : ℤ) + n = k) :
    Stacks.AlgebraicGeometry.ProjTwistSectionModule.homogeneousMul 𝒮 ha n k (by rw [← hk]) =
      twistScalarSheafMap 𝒮 i n k hk ⟨a, ha⟩ := rfl

/-! ### Multiplication by a scalar relating two trivializing sections -/

/-- **Multiplication by a homogeneous `c` with `g ^ m = f ^ n c` carries the trivializing section
`f ^ n` of `𝒪(nd)` to the trivializing section `g ^ m` of `𝒪(me)`**, on every open contained in
both standard opens.

At a point of that open the two sections are the fractions `f ^ n / 1` and `g ^ m / 1`, so this
is the given relation read in the local ring. -/
theorem twistScalarSheafMap_trivializingSection
    (hf : f ∈ 𝒮 d) (hg : g ∈ 𝒮 e) {i : ℕ} {c : S} (hc : c ∈ 𝒮 i) (n m : ℕ)
    (hgm : g ^ m = f ^ n * c)
    (hdeg : (i : ℤ) + (n : ℤ) * d = (m : ℤ) * e)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hWf : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (hWg : W ≤ ProjectiveSpectrum.basicOpen 𝒮 g) :
    (twistScalarSheafMap 𝒮 i ((n : ℤ) * d) ((m : ℤ) * e) hdeg ⟨c, hc⟩).val.app (op W)
        (trivializingSection 𝒮 hf (n : ℤ) hWf) =
      trivializingSection 𝒮 hg (m : ℤ) hWg := by
  have hn : ((n : ℤ)).toNat = n := by omega
  have hn' : (-(n : ℤ)).toNat = 0 := by omega
  have hm : ((m : ℤ)).toNat = m := by omega
  have hm' : (-(m : ℤ)).toNat = 0 := by omega
  apply Subtype.ext
  funext x
  change LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl
      (LinearMap.mul S S c) (trivializingFun 𝒮 (n : ℤ) hWf x) = _
  rw [trivializingFun, map_mul_mk]
  refine mk_eq_mk_of_eq _ _ _ _ _ _ ?_ ?_
  · rw [hn, hm, hgm]
    exact mul_comm c (f ^ n)
  · rw [hn', hm', pow_zero, pow_zero]

/-! ### The same law on the twists of an arbitrary sheaf of modules -/

/-- If a morphism of twisting sheaves carries the trivializing section `f ^ n` to `g ^ m`, then
tensoring it with `𝟙_ℱ` carries `t ⊗ f ^ n` to `t ⊗ g ^ m`. -/
private theorem twistSheafScalarMap_mulTrivSection_of_trivializingSection
    (hf : f ∈ 𝒮 d) (hg : g ∈ 𝒮 e) {i : ℕ} (a : 𝒮 i) (n m : ℤ)
    (hdeg : (i : ℤ) + n * d = m * e)
    (F : SheafOfModules.{u} (projRingSheaf 𝒮))
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hWf : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (hWg : W ≤ ProjectiveSpectrum.basicOpen 𝒮 g)
    (h : (twistScalarSheafMap 𝒮 i (n * d) (m * e) hdeg a).val.app (op W)
        (trivializingSection 𝒮 hf n hWf) = trivializingSection 𝒮 hg m hWg)
    (t : F.val.obj (op W)) :
    (twistSheafScalarMap 𝒮 F i (n * d) (m * e) hdeg a).val.app (op W)
        (mulTrivSection 𝒮 hf n F hWf t) = mulTrivSection 𝒮 hg m F hWg t := by
  refine Eq.trans (tensorSheafMap_app_toTensorSheafSection
      (AlgebraicGeometry.Proj 𝒮).toRingedSpace F (twistingSheaf 𝒮 (n * d)) F
      (twistingSheaf 𝒮 (m * e)) (𝟙 F) _ W t (trivializingSection 𝒮 hf n hWf)) ?_
  exact congrArg (fun y => toTensorSheafSection (AlgebraicGeometry.Proj 𝒮).toRingedSpace F
      (twistingSheaf 𝒮 (m * e)) (op W)
      (t ⊗ₜ[(AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf.obj (op W)] y)) h

/-- A map `g` with `g (φ x) = ψ x` for bijections `φ`, `ψ` is bijective. -/
private theorem bijective_of_apply_eq {X A B : Type*} {φ : X → A} {ψ : X → B} {g : A → B}
    (hφ : Function.Bijective φ) (hψ : Function.Bijective ψ) (h : ∀ x, g (φ x) = ψ x) :
    Function.Bijective g :=
  (Function.Bijective.of_comp_iff g hφ).1 (by rwa [show g ∘ φ = ψ from funext h])

/-- **Multiplication by a homogeneous `c` with `g ^ m = f ^ n c` carries `t ⊗ f ^ n` to
`t ⊗ g ^ m`**, for every section `t` of an arbitrary sheaf of modules `ℱ` over an open contained
in `D₊(f)` and in `D₊(g)`. -/
theorem twistSheafScalarMap_mulTrivSection
    (hf : f ∈ 𝒮 d) (hg : g ∈ 𝒮 e) {i : ℕ} {c : S} (hc : c ∈ 𝒮 i) (n m : ℕ)
    (hgm : g ^ m = f ^ n * c)
    (hdeg : (i : ℤ) + (n : ℤ) * d = (m : ℤ) * e)
    (F : SheafOfModules.{u} (projRingSheaf 𝒮))
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hWf : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (hWg : W ≤ ProjectiveSpectrum.basicOpen 𝒮 g)
    (t : F.val.obj (op W)) :
    (twistSheafScalarMap 𝒮 F i ((n : ℤ) * d) ((m : ℤ) * e) hdeg ⟨c, hc⟩).val.app (op W)
        (mulTrivSection 𝒮 hf (n : ℤ) F hWf t) =
      mulTrivSection 𝒮 hg (m : ℤ) F hWg t := by
  exact twistSheafScalarMap_mulTrivSection_of_trivializingSection 𝒮 hf hg ⟨c, hc⟩ n m hdeg F
    hWf hWg (twistScalarSheafMap_trivializingSection 𝒮 hf hg hc n m hgm hdeg hWf hWg) t

/-- **Multiplying by `f ^ n` and then by `f ^ k` is multiplying by `f ^ (n + k)`**: the
additivity in the exponent of multiplication by the trivializing section, for an arbitrary sheaf
of modules `ℱ` and an open `W ⊆ D₊(f)`. -/
theorem twistSheafScalarMap_mulTrivSection_pow (hf : f ∈ 𝒮 d) (n k : ℕ)
    (F : SheafOfModules.{u} (projRingSheaf 𝒮))
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (t : F.val.obj (op W)) :
    (twistSheafScalarMap 𝒮 F (k * d) ((n : ℤ) * d) (((n + k : ℕ) : ℤ) * d)
          (by push_cast; ring) ⟨f ^ k, pow_mem_degree 𝒮 hf k⟩).val.app (op W)
        (mulTrivSection 𝒮 hf (n : ℤ) F hW t) =
      mulTrivSection 𝒮 hf ((n + k : ℕ) : ℤ) F hW t :=
  twistSheafScalarMap_mulTrivSection 𝒮 hf hf (pow_mem_degree 𝒮 hf k) n (n + k)
    (pow_add f n k) (by push_cast; ring) F hW hW t

/-! ### Division by the trivializing section is independent of the denominator -/

/-- **Division by the trivializing section does not depend on the denominator.** Let
`g ^ m = f ^ n c` with `c` homogeneous, let `y` be a section of `ℱ(nd)` over
`W ⊆ D₊(f) ∩ D₊(g)`, and let `t` divide `y` by `f ^ n`, in the sense that `t ⊗ f ^ n = y`. If
`t'` divides the image of `y` under multiplication by `c` by `g ^ m`, that is
`t' ⊗ g ^ m = c y`, then `t = t'`.

Each of the two divisions exists and is unique by
`Stacks.AlgebraicGeometry.ProjTwistRestriction.bijective_mulTrivSection`, and
`Stacks.AlgebraicGeometry.ProjTwistRestriction.twistRestrictIso_hom_val_app_mulTrivSection`
exhibits the isomorphism `ℱ(nd)|_{D₊(f)} ≅ ℱ|_{D₊(f)}` as one way of performing it; so this is
the statement that the section of `ℱ` read off a degree-zero fraction depends on the fraction and
not on the representative. -/
theorem eq_of_mulTrivSection_twistSheafScalarMap
    (hf : f ∈ 𝒮 d) (hg : g ∈ 𝒮 e) {i : ℕ} {c : S} (hc : c ∈ 𝒮 i) (n m : ℕ)
    (hgm : g ^ m = f ^ n * c)
    (hdeg : (i : ℤ) + (n : ℤ) * d = (m : ℤ) * e)
    (F : SheafOfModules.{u} (projRingSheaf 𝒮))
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hWf : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (hWg : W ≤ ProjectiveSpectrum.basicOpen 𝒮 g)
    {y : (twistSheafOfModules 𝒮 F ((n : ℤ) * d)).val.obj (op W)}
    {t t' : F.val.obj (op W)}
    (ht : mulTrivSection 𝒮 hf (n : ℤ) F hWf t = y)
    (ht' : mulTrivSection 𝒮 hg (m : ℤ) F hWg t' =
      (twistSheafScalarMap 𝒮 F i ((n : ℤ) * d) ((m : ℤ) * e) hdeg ⟨c, hc⟩).val.app (op W) y) :
    t = t' := by
  refine (bijective_mulTrivSection 𝒮 hg (m : ℤ) F hWg).1 ?_
  rw [← twistSheafScalarMap_mulTrivSection 𝒮 hf hg hc n m hgm hdeg F hWf hWg t, ht, ht']

/-! ### Multiplication by a power of `f` is invertible on the sections over `D₊(f)` -/

/-- Two fractions whose numerator and denominator are powers of the same element are equal as
soon as the two exponent sums agree. The exponents produced below are `Int.toNat`s, which no
ring normalization reconciles; the single `ℕ`-equation `p + v = q + u` is what `omega` closes
from the integer relation between the twists. -/
private theorem mk_pow_eq_mk_pow {T : Submonoid S} (p q u v : ℕ) (hu : f ^ u ∈ T)
    (hv : f ^ v ∈ T) (h : p + v = q + u) :
    Localization.mk (f ^ p) (⟨f ^ u, hu⟩ : T) = Localization.mk (f ^ q) ⟨f ^ v, hv⟩ := by
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
  simp only [← pow_add]
  exact congrArg (f ^ ·) (by omega)

/-- **Multiplication by `f ^ m` carries the trivializing section `f ^ n` of `𝒪(nd)` to the
trivializing section `f ^ (n + m)` of `𝒪((n + m)d)`**, for an **arbitrary integer** `n`.

This is the integer-exponent form of
`Stacks.AlgebraicGeometry.ProjTwistRestriction.twistScalarSheafMap_trivializingSection`, which
asks for natural exponents because it compares two different trivializing elements `f` and `g`
through a relation `g ^ m = f ^ n c` in `S`. Here there is only one trivializing element, so the
comparison happens entirely inside the local ring, where the trivializing value of a negative
exponent is a genuine fraction `f ^ 0 / f ^ (-n)`; the exponent bookkeeping is the `ℕ`-equation
of `mk_pow_eq_mk_pow`. The integer exponent is what a consumer twisting down by `c` from an
unrestricted twist `q : ℤ` needs, `q - c` being negative for small `q`. -/
theorem twistScalarSheafMap_pow_trivializingSection (hf : f ∈ 𝒮 d) (m : ℕ) (n j : ℤ)
    (hj : n + (m : ℤ) = j) (hdeg : ((m * d : ℕ) : ℤ) + n * d = j * d)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    (twistScalarSheafMap 𝒮 (m * d) (n * d) (j * d) hdeg
          ⟨f ^ m, pow_mem_degree 𝒮 hf m⟩).val.app (op W)
        (trivializingSection 𝒮 hf n hW) = trivializingSection 𝒮 hf j hW := by
  apply Subtype.ext
  funext x
  change LocalizedModule.map x.1.asHomogeneousIdeal.toIdeal.primeCompl
      (LinearMap.mul S S (f ^ m)) (trivializingFun 𝒮 n hW x) = _
  rw [trivializingFun, map_mul_mk, ← pow_add]
  exact mk_pow_eq_mk_pow (T := x.1.asHomogeneousIdeal.toIdeal.primeCompl)
    (m + n.toNat) j.toNat (-n).toNat (-j).toNat
    (x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hW x.2) _)
    (x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hW x.2) _) (by omega)

/-- **A morphism of twisting sheaves carrying a trivializing section to a trivializing section is
bijective on the sections over every open inside `D₊(f)`.**

Multiplication by the trivializing section is a bijection `Γ(W, 𝒪) → Γ(W, 𝒪(nd))` on such an
open — `Stacks.AlgebraicGeometry.ProjTrivialization.bijective_trivializingHom`, which is
[Stacks, Tag 01MS] — and the morphism is a module map, so it is conjugate to the identity of
`Γ(W, 𝒪)` by the two bijections. Nothing about the scalar beyond the displayed hypothesis is
used, which is why this is stated for an arbitrary homogeneous `a`. -/
theorem bijective_twistScalarSheafMap_app_of_trivializingSection (hf : f ∈ 𝒮 d) {i : ℕ} {a : S}
    (ha : a ∈ 𝒮 i) (n j : ℤ) (hdeg : (i : ℤ) + n * d = j * d)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (h : (twistScalarSheafMap 𝒮 i (n * d) (j * d) hdeg ⟨a, ha⟩).val.app (op W)
        (trivializingSection 𝒮 hf n hW) = trivializingSection 𝒮 hf j hW) :
    Function.Bijective
      ((twistScalarSheafMap 𝒮 i (n * d) (j * d) hdeg ⟨a, ha⟩).val.app (op W)) := by
  refine bijective_of_apply_eq
    (Stacks.AlgebraicGeometry.ProjTrivialization.bijective_trivializingHom 𝒮 hf n hW)
    (Stacks.AlgebraicGeometry.ProjTrivialization.bijective_trivializingHom 𝒮 hf j hW) fun r => ?_
  exact (map_smul (ConcreteCategory.hom
    ((twistScalarSheafMap 𝒮 i (n * d) (j * d) hdeg ⟨a, ha⟩).val.app (op W))) r
      (trivializingSection 𝒮 hf n hW)).trans (congrArg (r • ·) h)

/-- **Multiplication by `f ^ m` is invertible on `D₊(f)`, as a morphism of twisting sheaves**: the
map `Γ(W, 𝒪(nd)) → Γ(W, 𝒪((n + m)d))` it induces is bijective for every open `W ⊆ D₊(f)` and
every **integer** `n`.

This is the local invertibility the cohomological clauses of [Stacks, Tag 0GAA] consume at
`f = b⁽¹⁾` and `m = c`: there twisting down `c` steps followed by multiplication by `(b⁽¹⁾)^c` is
multiplication by `b ^ c ∈ I^c`
(`Stacks.Blowup.twistDownMap_comp_twistScalarSheafMap_reesDegOnePow`), which [Stacks, Tag 0GA8]
annihilates, so on `D₊(b⁽¹⁾)` the twisted-down map itself is zero. The twist `n` has to be
allowed to be negative because the twist `q` of that argument is unrestricted. -/
theorem bijective_twistScalarSheafMap_pow_app (hf : f ∈ 𝒮 d) (m : ℕ) (n j : ℤ)
    (hj : n + (m : ℤ) = j) (hdeg : ((m * d : ℕ) : ℤ) + n * d = j * d)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    Function.Bijective ((twistScalarSheafMap 𝒮 (m * d) (n * d) (j * d) hdeg
      ⟨f ^ m, pow_mem_degree 𝒮 hf m⟩).val.app (op W)) :=
  bijective_twistScalarSheafMap_app_of_trivializingSection 𝒮 hf
    (pow_mem_degree 𝒮 hf m) n j hdeg hW
    (twistScalarSheafMap_pow_trivializingSection 𝒮 hf m n j hj hdeg hW)

/-! ### The same on the twists of an arbitrary sheaf of modules -/

/-- **Multiplication by `f ^ m` carries `t ⊗ f ^ n` to `t ⊗ f ^ (n + m)`**, for an **arbitrary
integer** `n` and an arbitrary sheaf of modules `ℱ`.

This is the integer-exponent form of
`Stacks.AlgebraicGeometry.ProjTwistRestriction.twistSheafScalarMap_mulTrivSection_pow`, obtained
from `twistScalarSheafMap_pow_trivializingSection` by the same two steps: the morphism is
`𝟙_ℱ` tensored with the morphism of twisting sheaves, so its value on a pure tensor is the
tensor of the two values. -/
theorem twistSheafScalarMap_mulTrivSection_pow_int (hf : f ∈ 𝒮 d) (m : ℕ) (n j : ℤ)
    (hj : n + (m : ℤ) = j) (hdeg : ((m * d : ℕ) : ℤ) + n * d = j * d)
    (F : SheafOfModules.{u} (projRingSheaf 𝒮))
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (t : F.val.obj (op W)) :
    (twistSheafScalarMap 𝒮 F (m * d) (n * d) (j * d) hdeg
          ⟨f ^ m, pow_mem_degree 𝒮 hf m⟩).val.app (op W)
        (mulTrivSection 𝒮 hf n F hW t) = mulTrivSection 𝒮 hf j F hW t := by
  exact twistSheafScalarMap_mulTrivSection_of_trivializingSection 𝒮 hf hf _ n j hdeg F hW hW
    (twistScalarSheafMap_pow_trivializingSection 𝒮 hf m n j hj hdeg hW) t

/-- **Multiplication by `f ^ m` is invertible on `D₊(f)` on the twists of an arbitrary sheaf of
modules**: for every sheaf of `𝒪_{Proj 𝒮}`-modules `ℱ`, every open `W ⊆ D₊(f)` and every
*integer* `n`, the map `Γ(W, ℱ(nd)) → Γ(W, ℱ((n + m)d))` induced by `f ^ m` is bijective.

Multiplication by the trivializing section is a bijection `Γ(W, ℱ) → Γ(W, ℱ(nd))` on such an open
by `Stacks.AlgebraicGeometry.ProjTwistRestriction.bijective_mulTrivSection`, and
`twistSheafScalarMap_mulTrivSection_pow_int` says that the morphism conjugates the one at `n`
into the one at `n + m`. -/
theorem bijective_twistSheafScalarMap_pow_app (hf : f ∈ 𝒮 d) (m : ℕ) (n j : ℤ)
    (hj : n + (m : ℤ) = j) (hdeg : ((m * d : ℕ) : ℤ) + n * d = j * d)
    (F : SheafOfModules.{u} (projRingSheaf 𝒮))
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    Function.Bijective ((twistSheafScalarMap 𝒮 F (m * d) (n * d) (j * d) hdeg
      ⟨f ^ m, pow_mem_degree 𝒮 hf m⟩).val.app (op W)) := by
  exact bijective_of_apply_eq (bijective_mulTrivSection 𝒮 hf n F hW)
    (bijective_mulTrivSection 𝒮 hf j F hW)
    (twistSheafScalarMap_mulTrivSection_pow_int 𝒮 hf m n j hj hdeg F hW)

end Stacks.AlgebraicGeometry.ProjTwistRestriction

end
