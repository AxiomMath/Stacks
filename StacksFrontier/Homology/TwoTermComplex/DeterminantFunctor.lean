module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Finiteness.Prod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.TwoTermComplex.DeterminantLine

/-!
# The determinant functor on perfect complexes of Tor-amplitude `[-1, 0]`

Let `R` be a commutative ring. Consider the perfect objects of the derived category of
`R`-modules whose Tor-amplitude lies in `[-1, 0]`, with only isomorphisms as morphisms. Such an
object has a two-term presentation by finite projective modules, and the determinant line of
that presentation depends on it only up to canonical isomorphism, because two presentations are
compared by degreewise-surjective quasi-isomorphisms. This produces a determinant functor to
invertible modules and their isomorphisms, together with a canonical element `δ` of the
determinant line of every rank-zero object, natural under every isomorphism.

## Main definitions

* `TwoTermDeterminant.PerfectTwoTermComplex`: the category of perfect derived objects of
  Tor-amplitude in `[-1, 0]`.
* `TwoTermDeterminant.InvertibleModule`: the category of invertible modules.
* `TwoTermDeterminant.TwoTermPresentation`: a presentation by a finite projective complex in
  degrees `-1` and `0`, with `TwoTermDeterminant.TwoTermPresentation.IsRankZero` and
  `TwoTermDeterminant.IsRankZero` recording the rank-zero condition.
* `TwoTermDeterminant.det`: the determinant functor.
* `TwoTermDeterminant.delta`: the canonical element of the determinant of a rank-zero object.
* `TwoTermDeterminant.detPresentationIso`: the comparison between the determinant of an object
  and the determinant line of a two-term presentation of it.

## Main results

* `TwoTermDeterminant.exists_determinantFunctor_natural_delta`: the determinant functor exists,
  is computed on a presentation by the determinant line of its two terms, and comes with the
  canonical element on rank-zero objects, natural under isomorphisms.
* `TwoTermDeterminant.det_map_delta`: the determinant functor carries the canonical element of a
  rank-zero object to that of any isomorphic object.
* `TwoTermDeterminant.detPresentationIso_delta` and
  `TwoTermDeterminant.detPresentationIso_det_map`: the comparison with a two-term presentation
  matches the canonical elements, and turns the determinant of an isomorphism represented by a
  degreewise-surjective quasi-isomorphism into its canonical determinant equivalence.

## Implementation notes

Both categories are cores of full subcategories, of the derived category and of the module
category respectively, which is how "only isomorphisms as morphisms" is expressed. The functor is
characterized by comparison isomorphisms with every finite-projective two-term presentation
rather than constructed from a chosen one, so that no choice enters the statement.

## References

* [Stacks Project, Tag 0FJM](https://stacks.math.columbia.edu/tag/0FJM)
* [Knudsen--Mumford, *The projectivity of the moduli space of stable curves, I*][determinant]
-/

namespace TwoTermDeterminant

/-! ### The determinant functor and its canonical element -/

section

universe u

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

@[expose] public section

/-- The property of being a perfect derived object of Tor-amplitude in `[-1, 0]`.

Tor amplitude in `[a, b]` is recorded as the existence of a bounded flat representative in those
degrees, `StacksDraft.Perfect.HasFlatRepresentative`; the two are equivalent by
[stacks 0654]. This is the form that needs no bespoke certified derived tensor product as data,
and it is what [stacks 0658] consumes. -/
public def perfectTwoTermComplexProperty (R : Type u) [CommRing R] :
    ObjectProperty (DerivedCategory (ModuleCat.{u} R)) := fun K =>
  StacksDraft.Perfect.IsPerfect K ∧
    StacksDraft.Perfect.HasFlatRepresentative.{u, u} K (-1) 0

/-- The category of perfect derived objects of Tor-amplitude in `[-1, 0]`. -/
public abbrev PerfectTwoTermComplex (R : Type u) [CommRing R] :=
  (perfectTwoTermComplexProperty R).FullSubcategory

/-- The property of an `R`-module being invertible. -/
public def invertibleModuleProperty (R : Type u) [CommRing R] :
    ObjectProperty (ModuleCat.{u} R) := fun M => Module.Invertible R M

/-- The category of invertible `R`-modules. -/
public abbrev InvertibleModule (R : Type u) [CommRing R] :=
  (invertibleModuleProperty R).FullSubcategory

/-- A presentation of a derived object by a complex of finite projective modules concentrated
in degrees `-1` and `0`. -/
public structure TwoTermPresentation {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) where
  /-- The presenting complex. -/
  complex : CochainComplex (ModuleCat.{u} R) ℤ
  /-- Every term of the presenting complex is finite. -/
  finite : ∀ i : ℤ, Module.Finite R (complex.X i)
  /-- Every term of the presenting complex is projective. -/
  projective : ∀ i : ℤ, Module.Projective R (complex.X i)
  /-- The presenting complex vanishes below degree `-1`. -/
  strictlyGE : complex.IsStrictlyGE (-1)
  /-- The presenting complex vanishes above degree `0`. -/
  strictlyLE : complex.IsStrictlyLE 0
  /-- The presentation represents the given derived object. -/
  iso : K ≅ DerivedCategory.Q.obj complex

namespace TwoTermPresentation

/-- A two-term presentation has rank zero when its terms in degrees `-1` and `0` have equal
rank at every prime. -/
public def IsRankZero {R : Type u} [CommRing R]
    {K : DerivedCategory (ModuleCat.{u} R)} (P : TwoTermPresentation K) : Prop :=
  letI := P.finite (-1)
  letI := P.projective (-1)
  letI := P.finite 0
  letI := P.projective 0
  TwoTermComplex.IsRankZero (P.complex.d (-1) 0).hom

/-- The morphism of concrete two-term complexes underlying a morphism between two-term
presentations. -/
public def hom {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L) (f : P.complex ⟶ Q.complex) :
    TwoTermComplex.Hom (P.complex.d (-1) 0).hom (Q.complex.d (-1) 0).hom where
  neg := (f.f (-1)).hom
  zero := (f.f 0).hom
  comm := by
    ext x
    exact (ConcreteCategory.congr_hom (f.comm (-1) 0) x).symm

end TwoTermPresentation

/-- A perfect derived object of Tor-amplitude in `[-1, 0]` has rank zero when it admits a
rank-zero finite-projective two-term presentation. -/
public def IsRankZero {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  ∃ P : TwoTermPresentation K, P.IsRankZero

end

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

/-- Every perfect derived object of Tor-amplitude in `[-1, 0]` has a finite-projective two-term
presentation. -/
public theorem nonempty_twoTermPresentation {R : Type u} [CommRing R]
    (K : PerfectTwoTermComplex R) : Nonempty (TwoTermPresentation K.obj) := by
  obtain ⟨hp, _⟩ :=
    (StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension K.obj).1.mp
      K.property.1
  obtain ⟨E, hE, hge, hle, ⟨e⟩⟩ :=
    (StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension K.obj).2 (-1) 0 hp
      K.property.2
  exact ⟨⟨E, fun i => (hE i).1, fun i => (hE i).2, hge, hle, e⟩⟩

private theorem exists_chainMap_of_isKProjective {R : Type u} [CommRing R]
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsKProjective]
    (a : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ f : K ⟶ L, DerivedCategory.Q.map f = a := by
  let e := DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)
  obtain ⟨f, hf⟩ := (CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient _ _).obj L)).surjective
      (e.hom.app K ≫ a ≫ e.inv.app L)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
  refine ⟨f, ?_⟩
  have hn := e.hom.naturality f
  dsimp at hn
  rw [hf] at hn
  simpa using hn.symm

private theorem nonempty_homotopy_of_Q_map_eq {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} [K.IsKProjective]
    (f g : K ⟶ L) (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Nonempty (Homotopy f g) := by
  refine ⟨HomotopyCategory.homotopyOfEq f g ?_⟩
  apply (CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient _ _).obj L)).injective
  let e := DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)
  apply (cancel_mono (e.hom.app L)).mp
  show ((HomotopyCategory.quotient _ _ ⋙ DerivedCategory.Qh).map f) ≫ e.hom.app L =
    ((HomotopyCategory.quotient _ _ ⋙ DerivedCategory.Qh).map g) ≫ e.hom.app L
  rw [e.hom.naturality, e.hom.naturality, h]

private theorem isKProjective_presentation {R : Type u} [CommRing R]
    {K : DerivedCategory (ModuleCat.{u} R)} (P : TwoTermPresentation K) :
    P.complex.IsKProjective := by
  let := P.strictlyLE
  let (i : ℤ) : Module.Projective R (P.complex.X i) := P.projective i
  exact CochainComplex.isKProjective_of_projective P.complex 0

private theorem homotopy_components {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    [K.IsStrictlyLE 0] [L.IsStrictlyGE (-1)]
    {f g : K ⟶ L} (h : Homotopy f g) :
    (f.f (-1)).hom = (g.f (-1)).hom + (h.hom 0 (-1)).hom.comp (K.d (-1) 0).hom ∧
      (f.f 0).hom = (g.f 0).hom + (L.d (-1) 0).hom.comp (h.hom 0 (-1)).hom := by
  have hn := h.comm (-1)
  have hz := h.comm 0
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by decide),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (-2) (-1) by decide),
    (L.isZero_of_isStrictlyGE (-1) (-2)).eq_of_tgt (h.hom (-1) (-2)) 0,
    zero_comp, add_zero] at hn
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by decide),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by decide),
    (K.isZero_of_isStrictlyLE 0 1).eq_of_tgt (K.d 0 1) 0,
    zero_comp, zero_add] at hz
  constructor
  · simpa only [ModuleCat.hom_add, ModuleCat.hom_comp, add_comm] using congrArg ModuleCat.Hom.hom hn
  · simpa only [ModuleCat.hom_add, ModuleCat.hom_comp, add_comm] using congrArg ModuleCat.Hom.hom hz

private theorem cohomology_maps_eq_of_homotopy {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L)
    {f g : P.complex ⟶ Q.complex} (h : Homotopy f g) :
    (P.hom Q f).hMinus = (P.hom Q g).hMinus ∧
      (P.hom Q f).hZero = (P.hom Q g).hZero := by
  let := P.strictlyLE
  let := Q.strictlyGE
  obtain ⟨hn, hz⟩ := homotopy_components h
  constructor
  · ext x
    show (f.f (-1)).hom x = (g.f (-1)).hom x
    rw [hn]
    simp only [LinearMap.add_apply, LinearMap.comp_apply]
    rw [show (P.complex.d (-1) 0).hom x = 0 from x.property, map_zero, add_zero]
  · ext x
    show Submodule.Quotient.mk ((f.f 0).hom x) =
      (Submodule.Quotient.mk ((g.f 0).hom x) : _ ⧸ (Q.complex.d (-1) 0).hom.range)
    rw [Submodule.Quotient.eq, hz]
    exact ⟨(h.hom 0 (-1)).hom x, by simp⟩

private theorem twoTerm_quasiIso_of_homotopyEquiv {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L)
    (e : HomotopyEquiv P.complex Q.complex) : (P.hom Q e.hom).IsQuasiIso := by
  have hp := cohomology_maps_eq_of_homotopy P P e.homotopyHomInvId
  have hq := cohomology_maps_eq_of_homotopy Q Q e.homotopyInvHomId
  have hpn : Function.LeftInverse (Q.hom P e.inv).hMinus (P.hom Q e.hom).hMinus :=
    fun x => DFunLike.congr_fun hp.1 x
  have hqn : Function.RightInverse (Q.hom P e.inv).hMinus (P.hom Q e.hom).hMinus :=
    fun x => DFunLike.congr_fun hq.1 x
  have hpz : Function.LeftInverse (Q.hom P e.inv).hZero (P.hom Q e.hom).hZero := by
    intro x
    show ((Q.hom P e.inv).hZero.comp (P.hom Q e.hom).hZero) x = x
    have hc : (Q.hom P e.inv).hZero.comp (P.hom Q e.hom).hZero =
        (P.hom P (e.hom ≫ e.inv)).hZero := by ext x; rfl
    rw [hc, hp.2]
    have hi : (P.hom P (𝟙 P.complex)).hZero = LinearMap.id := by ext x; rfl
    rw [hi, LinearMap.id_apply]
  have hqz : Function.RightInverse (Q.hom P e.inv).hZero (P.hom Q e.hom).hZero := by
    intro x
    show ((P.hom Q e.hom).hZero.comp (Q.hom P e.inv).hZero) x = x
    have hc : (P.hom Q e.hom).hZero.comp (Q.hom P e.inv).hZero =
        (Q.hom Q (e.inv ≫ e.hom)).hZero := by ext x; rfl
    rw [hc, hq.2]
    have hi : (Q.hom Q (𝟙 Q.complex)).hZero = LinearMap.id := by ext x; rfl
    rw [hi, LinearMap.id_apply]
  exact ⟨⟨hpn.injective, hqn.surjective⟩, ⟨hpz.injective, hqz.surjective⟩⟩

private theorem twoTerm_quasiIso_of_isIso_Q_map {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L)
    (f : P.complex ⟶ Q.complex) [IsIso (DerivedCategory.Q.map f)] :
    (P.hom Q f).IsQuasiIso := by
  let := isKProjective_presentation P
  let := isKProjective_presentation Q
  have hq := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} R) f).mp inferInstance
  obtain ⟨e, rfl⟩ := (CochainComplex.IsKProjective.quasiIso_iff f).mp hq
  exact twoTerm_quasiIso_of_homotopyEquiv P Q e

/-- The determinant line of a two-term presentation: the determinant line of its differential
from degree `-1` to degree `0`. -/
public noncomputable abbrev presentationDeterminant {R : Type u} [CommRing R]
    {K : DerivedCategory (ModuleCat.{u} R)} (P : TwoTermPresentation K) :=
  letI := P.finite (-1)
  letI := P.projective (-1)
  letI := P.finite 0
  letI := P.projective 0
  TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom

private noncomputable abbrev surjectiveDeterminantEquiv {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L)
    (f : P.complex ⟶ Q.complex) (hs : (P.hom Q f).IsDegreewiseSurjective)
    (hq : (P.hom Q f).IsQuasiIso) :
    presentationDeterminant P ≃ₗ[R] presentationDeterminant Q :=
  letI := P.finite (-1)
  letI := P.projective (-1)
  letI := P.finite 0
  letI := P.projective 0
  letI := Q.finite (-1)
  letI := Q.projective (-1)
  letI := Q.finite 0
  letI := Q.projective 0
  letI := TwoTermComplex.kernel_finite (P.hom Q f).neg hs.1
  letI := TwoTermComplex.kernel_projective (P.hom Q f).neg hs.1
  letI := TwoTermComplex.kernel_finite (P.hom Q f).zero hs.2
  letI := TwoTermComplex.kernel_projective (P.hom Q f).zero hs.2
  (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso _ _ (P.hom Q f) hs hq).equiv

private theorem surjectiveDeterminantEquiv_eq_of_Q_map_eq {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L)
    (f g : P.complex ⟶ Q.complex)
    (hsf : (P.hom Q f).IsDegreewiseSurjective) (hqf : (P.hom Q f).IsQuasiIso)
    (hsg : (P.hom Q g).IsDegreewiseSurjective) (hqg : (P.hom Q g).IsQuasiIso)
    (he : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    surjectiveDeterminantEquiv P Q f hsf hqf = surjectiveDeterminantEquiv P Q g hsg hqg := by
  let := P.finite (-1)
  let := P.projective (-1)
  let := P.finite 0
  let := P.projective 0
  let := Q.finite (-1)
  let := Q.projective (-1)
  let := Q.finite 0
  let := Q.projective 0
  let := P.strictlyLE
  let := Q.strictlyGE
  let := isKProjective_presentation P
  obtain ⟨h⟩ := nonempty_homotopy_of_Q_map_eq g f he.symm
  obtain ⟨hn, hz⟩ := homotopy_components h
  have hn' : (P.hom Q g).neg = (P.hom Q f).neg +
      (h.hom 0 (-1)).hom.comp (P.complex.d (-1) 0).hom := hn
  have hz' : (P.hom Q g).zero = (P.hom Q f).zero +
      (Q.complex.d (-1) 0).hom.comp (h.hom 0 (-1)).hom := hz
  have hsn : Function.Surjective ((P.hom Q f).neg +
      (h.hom 0 (-1)).hom.comp (P.complex.d (-1) 0).hom) := hn' ▸ hsg.1
  have hsz : Function.Surjective ((P.hom Q f).zero +
      (Q.complex.d (-1) 0).hom.comp (h.hom 0 (-1)).hom) := hz' ▸ hsg.2
  have ht := TwoTermComplex.determinantEquiv_eq_of_homotopic_surjections
    _ _ (P.hom Q f) hsf hqf (h.hom 0 (-1)).hom hsn hsz
  let b : TwoTermComplex.Hom (P.complex.d (-1) 0).hom (Q.complex.d (-1) 0).hom :=
    { neg := (P.hom Q f).neg + (h.hom 0 (-1)).hom.comp (P.complex.d (-1) 0).hom
      zero := (P.hom Q f).zero + (Q.complex.d (-1) 0).hom.comp (h.hom 0 (-1)).hom
      comm := by
        ext x
        simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
        rw [show (P.hom Q f).zero ((P.complex.d (-1) 0).hom x) =
          (Q.complex.d (-1) 0).hom ((P.hom Q f).neg x) from
          LinearMap.congr_fun (P.hom Q f).comm x] }
  have hb : b = P.hom Q g := by
    have : ∀ (a c : TwoTermComplex.Hom (P.complex.d (-1) 0).hom
        (Q.complex.d (-1) 0).hom), a.neg = c.neg → a.zero = c.zero → a = c := by
      intro a c ha hc
      cases a
      cases c
      cases ha
      cases hc
      rfl
    exact this b (P.hom Q g) hn'.symm hz'.symm
  change b.IsQuasiIso ∧ _ at ht
  let F (c : TwoTermComplex.Hom (P.complex.d (-1) 0).hom (Q.complex.d (-1) 0).hom)
      (hc : c.IsDegreewiseSurjective) (hqc : c.IsQuasiIso) :
      presentationDeterminant P ≃ₗ[R] presentationDeterminant Q :=
    let := TwoTermComplex.kernel_finite c.neg hc.1
    let := TwoTermComplex.kernel_projective c.neg hc.1
    let := TwoTermComplex.kernel_finite c.zero hc.2
    let := TwoTermComplex.kernel_projective c.zero hc.2
    (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso _ _ c hc hqc).equiv
  have ht' : F (P.hom Q f) hsf hqf = F b ⟨hsn, hsz⟩ ht.1 := ht.2 ht.1
  have hb' : F b ⟨hsn, hsz⟩ ht.1 = F (P.hom Q g) hsg hqg := by
    generalize hc : P.hom Q g = c at hb hsg hqg ⊢
    cases hb
    rfl
  exact ht'.trans hb'

private theorem degreewiseSurjective_comp {R : Type u} [CommRing R]
    {K L M : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L) (S : TwoTermPresentation M)
    (f : P.complex ⟶ Q.complex) (g : Q.complex ⟶ S.complex)
    (hf : (P.hom Q f).IsDegreewiseSurjective) (hg : (Q.hom S g).IsDegreewiseSurjective) :
    (P.hom S (f ≫ g)).IsDegreewiseSurjective :=
  ⟨hg.1.comp hf.1, hg.2.comp hf.2⟩

private theorem surjectiveDeterminantEquiv_comp {R : Type u} [CommRing R]
    {K L M : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L) (S : TwoTermPresentation M)
    (f : P.complex ⟶ Q.complex) (g : Q.complex ⟶ S.complex)
    (hf : (P.hom Q f).IsDegreewiseSurjective) (hqf : (P.hom Q f).IsQuasiIso)
    (hg : (Q.hom S g).IsDegreewiseSurjective) (hqg : (Q.hom S g).IsQuasiIso)
    (hqfg : (P.hom S (f ≫ g)).IsQuasiIso) :
    (surjectiveDeterminantEquiv P Q f hf hqf).trans (surjectiveDeterminantEquiv Q S g hg hqg) =
      surjectiveDeterminantEquiv P S (f ≫ g) (degreewiseSurjective_comp P Q S f g hf hg) hqfg := by
  let := P.finite (-1)
  let := P.projective (-1)
  let := P.finite 0
  let := P.projective 0
  let := Q.finite (-1)
  let := Q.projective (-1)
  let := Q.finite 0
  let := Q.projective 0
  let := S.finite (-1)
  let := S.projective (-1)
  let := S.finite 0
  let := S.projective 0
  obtain ⟨_, he⟩ := TwoTermComplex.determinantEquivOfSurjectiveQuasiIso_comp
    _ _ _ (P.hom Q f) (Q.hom S g) hf hqf hg hqg
  exact he

private theorem nonempty_homotopy_of_components {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    [K.IsStrictlyLE 0] [K.IsStrictlyGE (-1)]
    {f g : K ⟶ L} (h : K.X 0 ⟶ L.X (-1))
    (hn : f.f (-1) = K.d (-1) 0 ≫ h + g.f (-1))
    (hz : f.f 0 = h ≫ L.d (-1) 0 + g.f 0) : Nonempty (Homotopy f g) := by
  classical
  let H : ∀ i j, K.X i ⟶ L.X j := fun i j =>
    if hi : i = 0 then if hj : j = -1 then
      eqToHom (congrArg K.X hi) ≫ h ≫ eqToHom (congrArg L.X hj.symm)
    else 0 else 0
  refine ⟨{ hom := H, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    dsimp [H]
    split_ifs with hi hj
    · subst i j
      exact (hij (by decide)).elim
    all_goals rfl
  · intro i
    by_cases hn' : i = -1
    · subst i
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by decide),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-2) (-1) by decide)]
      simpa [H] using hn
    by_cases hz' : i = 0
    · subst i
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by decide),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by decide)]
      simpa [H] using hz
    have hi : IsZero (K.X i) := by
      rcases lt_or_gt_of_ne hz' with hi | hi
      · exact K.isZero_of_isStrictlyGE (-1) i (by omega)
      · exact K.isZero_of_isStrictlyLE 0 i hi
    exact hi.eq_of_src _ _

private theorem double_id_properties {R : Type u} [CommRing R]
    (N : ModuleCat.{u} R) [Module.Finite R N] [Module.Projective R N] :
    let D : CochainComplex (ModuleCat.{u} R) ℤ :=
      HomologicalComplex.double (𝟙 N) (show (ComplexShape.up ℤ).Rel (-1) 0 by decide)
    (∀ i, Module.Finite R (D.X i) ∧ Module.Projective R (D.X i)) ∧
      D.IsStrictlyGE (-1) ∧ D.IsStrictlyLE 0 ∧ Nonempty (Homotopy (𝟙 D) 0) := by
  dsimp only
  let r : (ComplexShape.up ℤ).Rel (-1) 0 := by decide
  let D : CochainComplex (ModuleCat.{u} R) ℤ := HomologicalComplex.double (𝟙 N) r
  let e₁ := HomologicalComplex.doubleXIso₀ (𝟙 N) r
  let e₀ := HomologicalComplex.doubleXIso₁ (𝟙 N) r (by decide : (-1 : ℤ) ≠ 0)
  have hge : D.IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega)
  have hle : D.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega)
  refine ⟨?_, hge, hle, ?_⟩
  · intro i
    by_cases hn : i = -1
    · subst i
      exact ⟨Module.Finite.equiv (e₁.symm.toLinearEquiv),
        Module.Projective.of_equiv (e₁.symm.toLinearEquiv)⟩
    by_cases hz : i = 0
    · subst i
      exact ⟨Module.Finite.equiv (e₀.symm.toLinearEquiv),
        Module.Projective.of_equiv (e₀.symm.toLinearEquiv)⟩
    have := ModuleCat.subsingleton_of_isZero (HomologicalComplex.isZero_double_X (𝟙 N) r i hn hz)
    exact ⟨inferInstance, inferInstance⟩
  · let := hge
    let := hle
    refine nonempty_homotopy_of_components (e₀.hom ≫ e₁.inv) ?_ ?_ <;>
    · dsimp only [HomologicalComplex.id_f, HomologicalComplex.zero_f]
      rw [HomologicalComplex.double_d _ _ (by decide)]
      simp [e₀, e₁]

/-- A derived isomorphism represented by two degreewise-surjective quasi-isomorphisms. -/
private structure SurjectiveSpan {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex) where
  middle : TwoTermPresentation K
  left : middle.complex ⟶ P.complex
  right : middle.complex ⟶ Q.complex
  left_surjective : (middle.hom P left).IsDegreewiseSurjective
  right_surjective : (middle.hom Q right).IsDegreewiseSurjective
  left_isIso : IsIso (DerivedCategory.Q.map left)
  right_isIso : IsIso (DerivedCategory.Q.map right)
  comm : DerivedCategory.Q.map left ≫ a.hom = DerivedCategory.Q.map right

private theorem nonempty_surjectiveSpan {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex) :
    Nonempty (SurjectiveSpan P Q a) := by
  let := isKProjective_presentation P
  obtain ⟨f, hf⟩ := exists_chainMap_of_isKProjective P.complex Q.complex a.hom
  have hfi : IsIso (DerivedCategory.Q.map f) := hf ▸ a.isIso_hom
  have hfq := twoTerm_quasiIso_of_isIso_Q_map P Q f
  let := Q.finite (-1)
  let := Q.projective (-1)
  let r : (ComplexShape.up ℤ).Rel (-1) 0 := by decide
  let D : CochainComplex (ModuleCat.{u} R) ℤ :=
    HomologicalComplex.double (𝟙 (Q.complex.X (-1))) r
  obtain ⟨hDfp, hDge, hDle, ⟨hD⟩⟩ := double_id_properties (Q.complex.X (-1))
  change (∀ i, Module.Finite R (D.X i) ∧ Module.Projective R (D.X i)) at hDfp
  let e₁ := HomologicalComplex.doubleXIso₀ (𝟙 (Q.complex.X (-1))) r
  let e₀ := HomologicalComplex.doubleXIso₁ (𝟙 (Q.complex.X (-1))) r
    (by decide : (-1 : ℤ) ≠ 0)
  let M : CochainComplex (ModuleCat.{u} R) ℤ := P.complex ⊞ D
  let b : M ⟶ P.complex := biprod.fst
  let i : P.complex ⟶ M := biprod.inl
  let t : D ⟶ Q.complex := HomologicalComplex.mkHomFromDouble r
    (by decide : (-1 : ℤ) ≠ 0) (𝟙 _) (Q.complex.d (-1) 0)
    (by simp) (by intro j hj; simp)
  let c : M ⟶ Q.complex := biprod.desc f t
  have hDz : IsZero (DerivedCategory.Q.obj D) := by
    rw [IsZero.iff_id_eq_zero]
    simpa using DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{u} R) hD
  have hbi : IsIso (DerivedCategory.Q.map b) := by
    refine ⟨⟨DerivedCategory.Q.map i, ?_, ?_⟩⟩
    · have ht := congrArg DerivedCategory.Q.map (biprod.total (X := P.complex) (Y := D))
      simp only [Functor.map_add, Functor.map_comp, CategoryTheory.Functor.map_id] at ht
      rw [hDz.eq_of_tgt (DerivedCategory.Q.map (biprod.snd : M ⟶ D)) 0,
        zero_comp, add_zero] at ht
      simpa only [CategoryTheory.Functor.map_id] using ht
    · rw [← Functor.map_comp]
      simp [b, i]
  have hc : DerivedCategory.Q.map c = DerivedCategory.Q.map b ≫ a.hom := by
    have hc' : c = b ≫ f + (biprod.snd : M ⟶ D) ≫ t := by
      apply biprod.hom_ext' <;> simp [c, b]
    rw [hc', Functor.map_add, Functor.map_comp, Functor.map_comp,
      hDz.eq_of_src (DerivedCategory.Q.map t) 0, comp_zero, add_zero, hf]
  have hci : IsIso (DerivedCategory.Q.map c) := by rw [hc]; infer_instance
  have hMfp (j : ℤ) : Module.Finite R (M.X j) ∧ Module.Projective R (M.X j) := by
    let := P.finite j
    let := P.projective j
    let := (hDfp j).1
    let := (hDfp j).2
    let e := (HomologicalComplex.biprodXIso P.complex D j ≪≫
      ModuleCat.biprodIsoProd (P.complex.X j) (D.X j)).symm.toLinearEquiv
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  have hMge : M.IsStrictlyGE (-1) := by
    let := P.strictlyGE
    let := hDge
    rw [CochainComplex.isStrictlyGE_iff]
    intro j hj
    exact IsZero.of_iso ((biprod_isZero_iff _ _).mpr
      ⟨P.complex.isZero_of_isStrictlyGE (-1) j hj, D.isZero_of_isStrictlyGE (-1) j hj⟩)
      (HomologicalComplex.biprodXIso P.complex D j)
  have hMle : M.IsStrictlyLE 0 := by
    let := P.strictlyLE
    let := hDle
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    exact IsZero.of_iso ((biprod_isZero_iff _ _).mpr
      ⟨P.complex.isZero_of_isStrictlyLE 0 j hj, D.isZero_of_isStrictlyLE 0 j hj⟩)
      (HomologicalComplex.biprodXIso P.complex D j)
  let S : TwoTermPresentation K :=
    ⟨M, fun j => (hMfp j).1, fun j => (hMfp j).2, hMge, hMle,
      P.iso ≪≫ (asIso (DerivedCategory.Q.map b)).symm⟩
  have hbs : (S.hom P b).IsDegreewiseSurjective := by
    constructor <;> intro x
    · refine ⟨(i.f (-1)) x, ?_⟩
      exact ConcreteCategory.congr_hom (HomologicalComplex.biprod_inl_fst_f P.complex D (-1)) x
    · refine ⟨(i.f 0) x, ?_⟩
      exact ConcreteCategory.congr_hom (HomologicalComplex.biprod_inl_fst_f P.complex D 0) x
  have hcn : Function.Surjective (S.hom Q c).neg := by
    intro x
    refine ⟨(biprod.inr : D ⟶ M).f (-1) (e₁.inv x), ?_⟩
    have he : e₁.inv ≫ (biprod.inr : D ⟶ M).f (-1) ≫ c.f (-1) = 𝟙 _ := by
      simp [c, t, e₁]
    exact ConcreteCategory.congr_hom he x
  have hcz : Function.Surjective (S.hom Q c).zero := by
    intro y
    obtain ⟨x, hx⟩ := hfq.2.2 (Submodule.Quotient.mk y)
    obtain ⟨x, rfl⟩ := (Submodule.mkQ_surjective (P.complex.d (-1) 0).hom.range) x
    change Submodule.Quotient.mk ((f.f 0) x) = Submodule.Quotient.mk y at hx
    obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).mp hx
    refine ⟨(i.f 0) x - (biprod.inr : D ⟶ M).f 0 (e₀.inv z), ?_⟩
    have he : e₀.inv ≫ (biprod.inr : D ⟶ M).f 0 ≫ c.f 0 = Q.complex.d (-1) 0 := by
      simp [c, t, e₀]
    have hi : (c.f 0) ((i.f 0) x) = (f.f 0) x :=
      ConcreteCategory.congr_hom (HomologicalComplex.biprod_inl_desc_f f t 0) x
    show (c.f 0).hom _ = y
    have he' : (c.f 0).hom ((biprod.inr : D ⟶ M).f 0 (e₀.inv z)) =
        (Q.complex.d (-1) 0).hom z := ConcreteCategory.congr_hom he z
    rw [map_sub, hi, he']
    show (f.f 0) x - (Q.complex.d (-1) 0).hom z = y
    rw [hz]
    abel
  exact ⟨⟨S, b, c, hbs, ⟨hcn, hcz⟩, hbi, hci, hc.symm⟩⟩

private noncomputable abbrev isoSurjectiveDeterminant {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L)
    (f : P.complex ⟶ Q.complex) (hs : (P.hom Q f).IsDegreewiseSurjective)
    [IsIso (DerivedCategory.Q.map f)] :
    presentationDeterminant P ≃ₗ[R] presentationDeterminant Q :=
  surjectiveDeterminantEquiv P Q f hs (twoTerm_quasiIso_of_isIso_Q_map P Q f)

/-- A composite of chain maps that are isomorphisms in the derived category is one too. -/
private instance isIso_Q_map_comp {R : Type u} [CommRing R]
    {X Y Z : CochainComplex (ModuleCat.{u} R) ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIso (DerivedCategory.Q.map f)] [IsIso (DerivedCategory.Q.map g)] :
    IsIso (DerivedCategory.Q.map (f ≫ g)) := by
  rw [Functor.map_comp]
  infer_instance

private theorem isoSurjectiveDeterminant_comp {R : Type u} [CommRing R]
    {K L M : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L) (S : TwoTermPresentation M)
    (f : P.complex ⟶ Q.complex) (g : Q.complex ⟶ S.complex)
    (hf : (P.hom Q f).IsDegreewiseSurjective) (hg : (Q.hom S g).IsDegreewiseSurjective)
    [IsIso (DerivedCategory.Q.map f)] [IsIso (DerivedCategory.Q.map g)] :
    (isoSurjectiveDeterminant P Q f hf).trans (isoSurjectiveDeterminant Q S g hg) =
      surjectiveDeterminantEquiv P S (f ≫ g) (degreewiseSurjective_comp P Q S f g hf hg)
        (twoTerm_quasiIso_of_isIso_Q_map P S (f ≫ g)) :=
  surjectiveDeterminantEquiv_comp _ _ _ _ _ _ _ _ _ _

/-- Factorizations of the same derived morphism give the same composite determinant equivalence. -/
private theorem isoSurjectiveDeterminant_trans_eq {R : Type u} [CommRing R]
    {K L L' M : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L) (Q' : TwoTermPresentation L')
    (S : TwoTermPresentation M) (f : P.complex ⟶ Q.complex) (g : Q.complex ⟶ S.complex)
    (f' : P.complex ⟶ Q'.complex) (g' : Q'.complex ⟶ S.complex)
    (hf : (P.hom Q f).IsDegreewiseSurjective) (hg : (Q.hom S g).IsDegreewiseSurjective)
    (hf' : (P.hom Q' f').IsDegreewiseSurjective) (hg' : (Q'.hom S g').IsDegreewiseSurjective)
    [IsIso (DerivedCategory.Q.map f)] [IsIso (DerivedCategory.Q.map g)]
    [IsIso (DerivedCategory.Q.map f')] [IsIso (DerivedCategory.Q.map g')]
    (h : DerivedCategory.Q.map (f ≫ g) = DerivedCategory.Q.map (f' ≫ g')) :
    (isoSurjectiveDeterminant P Q f hf).trans (isoSurjectiveDeterminant Q S g hg) =
      (isoSurjectiveDeterminant P Q' f' hf').trans (isoSurjectiveDeterminant Q' S g' hg') := by
  rw [isoSurjectiveDeterminant_comp, isoSurjectiveDeterminant_comp]
  exact surjectiveDeterminantEquiv_eq_of_Q_map_eq _ _ _ _ _ _ _ _ h

private theorem isoSurjectiveDeterminant_id {R : Type u} [CommRing R]
    {K : DerivedCategory (ModuleCat.{u} R)} (P : TwoTermPresentation K) :
    surjectiveDeterminantEquiv P P (𝟙 P.complex)
      ⟨Function.surjective_id, Function.surjective_id⟩
      (twoTerm_quasiIso_of_homotopyEquiv P P (HomotopyEquiv.refl _)) =
      LinearEquiv.refl R (presentationDeterminant P) := by
  let h : (P.hom P (𝟙 P.complex)).IsDegreewiseSurjective :=
    ⟨Function.surjective_id, Function.surjective_id⟩
  have : IsIso (DerivedCategory.Q.map (𝟙 P.complex)) := by
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  have he := isoSurjectiveDeterminant_comp P P P (𝟙 _) (𝟙 _) h h
  simp only [Category.id_comp] at he
  let e := isoSurjectiveDeterminant P P (𝟙 _) h
  change e.trans e = e at he
  exact LinearEquiv.ext fun x => e.injective (DFunLike.congr_fun he x)

attribute [local instance] SurjectiveSpan.left_isIso SurjectiveSpan.right_isIso

private noncomputable abbrev spanEquiv {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    {P : TwoTermPresentation K} {Q : TwoTermPresentation L}
    {a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex}
    (s : SurjectiveSpan P Q a) : presentationDeterminant P ≃ₗ[R] presentationDeterminant Q :=
  (isoSurjectiveDeterminant s.middle P s.left s.left_surjective).symm.trans
    (isoSurjectiveDeterminant s.middle Q s.right s.right_surjective)

private theorem spanEquiv_eq {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    {P : TwoTermPresentation K} {Q : TwoTermPresentation L}
    {a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex}
    (s t : SurjectiveSpan P Q a) : spanEquiv s = spanEquiv t := by
  obtain ⟨r⟩ := nonempty_surjectiveSpan s.middle t.middle
    (asIso (DerivedCategory.Q.map s.left) ≪≫ (asIso (DerivedCategory.Q.map t.left)).symm)
  have hl : DerivedCategory.Q.map (r.left ≫ s.left) =
      DerivedCategory.Q.map (r.right ≫ t.left) := by
    have h := congrArg (fun f => f ≫ DerivedCategory.Q.map t.left) r.comm
    simpa [Functor.map_comp, Category.assoc] using h
  have hr : DerivedCategory.Q.map (r.left ≫ s.right) =
      DerivedCategory.Q.map (r.right ≫ t.right) := by
    simpa only [Functor.map_comp, Category.assoc, s.comm, t.comm] using
      congrArg (fun f => f ≫ a.hom) hl
  have hdl := isoSurjectiveDeterminant_trans_eq r.middle s.middle t.middle P r.left s.left
    r.right t.left r.left_surjective s.left_surjective r.right_surjective t.left_surjective hl
  have hdr := isoSurjectiveDeterminant_trans_eq r.middle s.middle t.middle Q r.left s.right
    r.right t.right r.left_surjective s.right_surjective r.right_surjective t.right_surjective hr
  let A := isoSurjectiveDeterminant r.middle s.middle r.left r.left_surjective
  let B := isoSurjectiveDeterminant r.middle t.middle r.right r.right_surjective
  let U := isoSurjectiveDeterminant s.middle P s.left s.left_surjective
  let V := isoSurjectiveDeterminant s.middle Q s.right s.right_surjective
  let U' := isoSurjectiveDeterminant t.middle P t.left t.left_surjective
  let V' := isoSurjectiveDeterminant t.middle Q t.right t.right_surjective
  change A.trans U = B.trans U' at hdl
  change A.trans V = B.trans V' at hdr
  refine LinearEquiv.ext fun x => ?_
  let z := A.symm (U.symm x)
  have hz : B z = U'.symm x :=
    U'.injective (by simpa [z] using (DFunLike.congr_fun hdl z).symm)
  show V (U.symm x) = V' (U'.symm x)
  calc
    V (U.symm x) = V (A z) := by simp [z]
    _ = V' (B z) := DFunLike.congr_fun hdr z
    _ = V' (U'.symm x) := congrArg V' hz

/-- Transport between determinant lines, defined by any surjective span. -/
public noncomputable def determinantTransport {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex) :
    presentationDeterminant P ≃ₗ[R] presentationDeterminant Q :=
  spanEquiv (Classical.choice (nonempty_surjectiveSpan P Q a))

private theorem determinantTransport_eq_span {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    {P : TwoTermPresentation K} {Q : TwoTermPresentation L}
    {a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex}
    (s : SurjectiveSpan P Q a) : determinantTransport P Q a = spanEquiv s :=
  spanEquiv_eq _ s

private theorem determinantTransport_id {R : Type u} [CommRing R]
    {K : DerivedCategory (ModuleCat.{u} R)} (P : TwoTermPresentation K) :
    determinantTransport P P (Iso.refl _) = LinearEquiv.refl R (presentationDeterminant P) := by
  have hi : IsIso (DerivedCategory.Q.map (𝟙 P.complex)) := by
    rw [CategoryTheory.Functor.map_id]; infer_instance
  let s : SurjectiveSpan P P (Iso.refl _) :=
    ⟨P, 𝟙 _, 𝟙 _, ⟨Function.surjective_id, Function.surjective_id⟩,
      ⟨Function.surjective_id, Function.surjective_id⟩, hi, hi, by simp⟩
  rw [determinantTransport_eq_span s]
  exact LinearEquiv.symm_trans_self _

private theorem determinantTransport_eq_of_surjective {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L)
    (f : P.complex ⟶ Q.complex) (hs : (P.hom Q f).IsDegreewiseSurjective)
    [IsIso (DerivedCategory.Q.map f)] :
    determinantTransport P Q (asIso (DerivedCategory.Q.map f)) =
      isoSurjectiveDeterminant P Q f hs := by
  have hi : IsIso (DerivedCategory.Q.map (𝟙 P.complex)) := by
    rw [CategoryTheory.Functor.map_id]; infer_instance
  let s : SurjectiveSpan P Q (asIso (DerivedCategory.Q.map f)) :=
    ⟨P, 𝟙 _, f, ⟨Function.surjective_id, Function.surjective_id⟩, hs, hi,
      inferInstance, by simp⟩
  rw [determinantTransport_eq_span s]
  show (isoSurjectiveDeterminant P P (𝟙 _) _).symm.trans _ = _
  dsimp only [isoSurjectiveDeterminant]
  rw [isoSurjectiveDeterminant_id]
  exact LinearEquiv.refl_trans _

private theorem determinantTransport_comp {R : Type u} [CommRing R]
    {K L M : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L) (S : TwoTermPresentation M)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex)
    (b : DerivedCategory.Q.obj Q.complex ≅ DerivedCategory.Q.obj S.complex) :
    (determinantTransport P Q a).trans (determinantTransport Q S b) =
      determinantTransport P S (a ≪≫ b) := by
  obtain ⟨s⟩ := nonempty_surjectiveSpan P Q a
  obtain ⟨t⟩ := nonempty_surjectiveSpan Q S b
  obtain ⟨r⟩ := nonempty_surjectiveSpan s.middle t.middle
    (asIso (DerivedCategory.Q.map s.right) ≪≫ (asIso (DerivedCategory.Q.map t.left)).symm)
  have hr : DerivedCategory.Q.map (r.left ≫ s.right) =
      DerivedCategory.Q.map (r.right ≫ t.left) := by
    have h := congrArg (fun f => f ≫ DerivedCategory.Q.map t.left) r.comm
    simpa [Functor.map_comp, Category.assoc] using h
  let c : SurjectiveSpan P S (a ≪≫ b) :=
    { middle := r.middle
      left := r.left ≫ s.left
      right := r.right ≫ t.right
      left_surjective := degreewiseSurjective_comp _ _ _ _ _ r.left_surjective s.left_surjective
      right_surjective := degreewiseSurjective_comp _ _ _ _ _ r.right_surjective t.right_surjective
      left_isIso := inferInstance
      right_isIso := inferInstance
      comm := by
        dsimp only [Iso.trans_hom]
        simp only [Functor.map_comp, Category.assoc]
        rw [← Category.assoc (DerivedCategory.Q.map s.left), s.comm, ← Category.assoc]
        rw [show DerivedCategory.Q.map r.left ≫ DerivedCategory.Q.map s.right =
          DerivedCategory.Q.map r.right ≫ DerivedCategory.Q.map t.left from
          by simpa only [Functor.map_comp] using hr]
        rw [Category.assoc, t.comm] }
  have hdm := isoSurjectiveDeterminant_trans_eq r.middle s.middle t.middle Q r.left s.right
    r.right t.left r.left_surjective s.right_surjective r.right_surjective t.left_surjective hr
  rw [determinantTransport_eq_span s, determinantTransport_eq_span t,
    determinantTransport_eq_span c]
  show (spanEquiv s).trans (spanEquiv t) =
    (isoSurjectiveDeterminant r.middle P (r.left ≫ s.left) _).symm.trans
      (isoSurjectiveDeterminant r.middle S (r.right ≫ t.right) _)
  dsimp only [isoSurjectiveDeterminant]
  rw [← isoSurjectiveDeterminant_comp r.middle s.middle P r.left s.left
    r.left_surjective s.left_surjective,
    ← isoSurjectiveDeterminant_comp r.middle t.middle S r.right t.right
      r.right_surjective t.right_surjective]
  let A := isoSurjectiveDeterminant r.middle s.middle r.left r.left_surjective
  let B := isoSurjectiveDeterminant r.middle t.middle r.right r.right_surjective
  let U := isoSurjectiveDeterminant s.middle P s.left s.left_surjective
  let V := isoSurjectiveDeterminant s.middle Q s.right s.right_surjective
  let U' := isoSurjectiveDeterminant t.middle Q t.left t.left_surjective
  let V' := isoSurjectiveDeterminant t.middle S t.right t.right_surjective
  change A.trans V = B.trans U' at hdm
  show (U.symm.trans V).trans (U'.symm.trans V') = (A.trans U).symm.trans (B.trans V')
  apply LinearEquiv.ext
  intro x
  have hx := DFunLike.congr_fun hdm (A.symm (U.symm x))
  have hz : U'.symm (V (U.symm x)) = B (A.symm (U.symm x)) := by
    apply U'.injective
    simpa using hx
  simpa only [LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply] using congrArg V' hz

/-- The canonical element `δ` of the determinant line of a rank-zero two-term presentation. -/
public noncomputable abbrev presentationDelta {R : Type u} [CommRing R]
    {K : DerivedCategory (ModuleCat.{u} R)} (P : TwoTermPresentation K) (h : P.IsRankZero) :
    presentationDeterminant P :=
  letI := P.finite (-1)
  letI := P.projective (-1)
  letI := P.finite 0
  letI := P.projective 0
  TwoTermComplex.delta (P.complex.d (-1) 0).hom h

private theorem surjectiveDeterminantEquiv_apply_delta {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L)
    (f : P.complex ⟶ Q.complex) (hs : (P.hom Q f).IsDegreewiseSurjective)
    (hq : (P.hom Q f).IsQuasiIso) (hQ : Q.IsRankZero) :
    ∃ hP : P.IsRankZero,
      surjectiveDeterminantEquiv P Q f hs hq (presentationDelta P hP) = presentationDelta Q hQ := by
  let := P.finite (-1)
  let := P.projective (-1)
  let := P.finite 0
  let := P.projective 0
  let := Q.finite (-1)
  let := Q.projective (-1)
  let := Q.finite 0
  let := Q.projective 0
  exact TwoTermComplex.determinantEquivOfSurjectiveQuasiIso_apply_delta _ _ (P.hom Q f) hs hq hQ

private theorem determinantTransport_apply_delta {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex)
    (hP : P.IsRankZero) (hQ : Q.IsRankZero) :
    determinantTransport P Q a (presentationDelta P hP) = presentationDelta Q hQ := by
  obtain ⟨s⟩ := nonempty_surjectiveSpan P Q a
  obtain ⟨hm, hl⟩ := surjectiveDeterminantEquiv_apply_delta s.middle P s.left s.left_surjective
    (twoTerm_quasiIso_of_isIso_Q_map _ _ _) hP
  obtain ⟨_, hr⟩ := surjectiveDeterminantEquiv_apply_delta s.middle Q s.right s.right_surjective
    (twoTerm_quasiIso_of_isIso_Q_map _ _ _) hQ
  rw [determinantTransport_eq_span s]
  show (isoSurjectiveDeterminant s.middle Q s.right s.right_surjective)
    ((isoSurjectiveDeterminant s.middle P s.left s.left_surjective).symm
      (presentationDelta P hP)) = _
  rw [← hl, LinearEquiv.symm_apply_apply]
  exact hr

/-- The isomorphism of determinant lines of two two-term presentations induced by an
isomorphism of the derived objects they present. -/
public noncomputable abbrev presentationTransport {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L) (a : K ≅ L) :
    presentationDeterminant P ≃ₗ[R] presentationDeterminant Q :=
  determinantTransport P Q (P.iso.symm ≪≫ a ≪≫ Q.iso)

/-- The transport along the identity of a presented object is the identity. -/
public theorem presentationTransport_id {R : Type u} [CommRing R]
    {K : DerivedCategory (ModuleCat.{u} R)} (P : TwoTermPresentation K) :
    presentationTransport P P (Iso.refl K) = LinearEquiv.refl R (presentationDeterminant P) := by
  have h : P.iso.symm ≪≫ Iso.refl K ≪≫ P.iso = Iso.refl _ := by ext; simp
  show determinantTransport P P _ = _
  rw [h, determinantTransport_id]

/-- The transport along a composite isomorphism is the composite of the transports. -/
public theorem presentationTransport_comp {R : Type u} [CommRing R]
    {K L M : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L) (S : TwoTermPresentation M)
    (a : K ≅ L) (b : L ≅ M) :
    (presentationTransport P Q a).trans (presentationTransport Q S b) =
      presentationTransport P S (a ≪≫ b) := by
  show (determinantTransport _ _ _).trans (determinantTransport _ _ _) = _
  rw [determinantTransport_comp]
  congr 1
  ext
  simp

/-- Applying two transports in turn is applying the transport along the composite isomorphism. -/
private theorem presentationTransport_comp_apply {R : Type u} [CommRing R]
    {K L M : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L) (S : TwoTermPresentation M)
    (a : K ≅ L) (b : L ≅ M) (x : presentationDeterminant P) :
    presentationTransport Q S b (presentationTransport P Q a x) =
      presentationTransport P S (a ≪≫ b) x :=
  DFunLike.congr_fun (presentationTransport_comp P Q S a b) x

/-- The transport between rank-zero presentations carries canonical element to canonical
element. -/
public theorem presentationTransport_apply_delta {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L) (a : K ≅ L)
    (hP : P.IsRankZero) (hQ : Q.IsRankZero) :
    presentationTransport P Q a (presentationDelta P hP) = presentationDelta Q hQ :=
  determinantTransport_apply_delta P Q _ hP hQ

private theorem presentationTransport_eq_surjectiveDeterminant {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L) (a : K ≅ L)
    (f : P.complex ⟶ Q.complex)
    (hf : P.iso.hom ≫ DerivedCategory.Q.map f ≫ Q.iso.inv = a.hom)
    (hs : (P.hom Q f).IsDegreewiseSurjective) (hq : (P.hom Q f).IsQuasiIso) :
    presentationTransport P Q a = surjectiveDeterminantEquiv P Q f hs hq := by
  have he : (P.iso.symm ≪≫ a ≪≫ Q.iso).hom = DerivedCategory.Q.map f := by
    dsimp only [Iso.trans_hom, Iso.symm_hom]
    rw [← hf]
    simp
  have hi : IsIso (DerivedCategory.Q.map f) := he ▸ (P.iso.symm ≪≫ a ≪≫ Q.iso).isIso_hom
  have he' : P.iso.symm ≪≫ a ≪≫ Q.iso = asIso (DerivedCategory.Q.map f) := Iso.ext he
  show determinantTransport P Q _ = _
  rw [he', determinantTransport_eq_of_surjective]

/-- Transports commute with the determinant equivalence of a surjective quasi-isomorphism. -/
private theorem presentationTransport_naturality {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)}
    (P₀ : TwoTermPresentation K) (Q₀ : TwoTermPresentation L)
    (P : TwoTermPresentation K) (Q : TwoTermPresentation L) (e : K ≅ L)
    (f : P.complex ⟶ Q.complex)
    (hf : P.iso.hom ≫ DerivedCategory.Q.map f ≫ Q.iso.inv = e.hom)
    (hs : (P.hom Q f).IsDegreewiseSurjective) (hq : (P.hom Q f).IsQuasiIso)
    (x : presentationDeterminant P₀) :
    presentationTransport Q₀ Q (Iso.refl L) (presentationTransport P₀ Q₀ e x) =
      surjectiveDeterminantEquiv P Q f hs hq (presentationTransport P₀ P (Iso.refl K) x) := by
  rw [← presentationTransport_eq_surjectiveDeterminant P Q e f hf hs hq,
    presentationTransport_comp_apply, presentationTransport_comp_apply]
  simp

/-- The determinant line of a two-term presentation is an invertible module. -/
public theorem presentationDeterminant_invertible {R : Type u} [CommRing R]
    {K : DerivedCategory (ModuleCat.{u} R)} (P : TwoTermPresentation K) :
    Module.Invertible R (presentationDeterminant P) := by
  let := P.finite (-1)
  let := P.projective (-1)
  let := P.finite 0
  let := P.projective 0
  let := ProjectiveDeterminant.invertible (R := R) (M := P.complex.X (-1))
  let := ProjectiveDeterminant.invertible (R := R) (M := P.complex.X 0)
  exact Module.Invertible.congr (dualTensorHomEquiv R
    (ProjectiveDeterminant.module (R := R) (M := P.complex.X (-1)))
    (ProjectiveDeterminant.module (R := R) (M := P.complex.X 0)))

/-- The determinant functor associated to a choice of two-term presentations. -/
@[expose]
public noncomputable def determinantFunctor {R : Type u} [CommRing R]
    (p : ∀ K : PerfectTwoTermComplex R, TwoTermPresentation K.obj) :
    Core (PerfectTwoTermComplex R) ⥤ Core (InvertibleModule R) where
  obj K := ⟨⟨ModuleCat.of R (presentationDeterminant (p K.of)),
    presentationDeterminant_invertible (p K.of)⟩⟩
  map {K L} a := ⟨ObjectProperty.isoMk (invertibleModuleProperty R)
    ((presentationTransport (p K.of) (p L.of)
      ((perfectTwoTermComplexProperty R).ι.mapIso a.iso)).toModuleIso)⟩
  map_id K := by
    apply Core.hom_ext
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    change (presentationTransport (p K.of) (p K.of)
      ((perfectTwoTermComplexProperty R).ι.mapIso (Iso.refl K.of))).toLinearMap = LinearMap.id
    have h : (perfectTwoTermComplexProperty R).ι.mapIso (Iso.refl K.of) = Iso.refl _ := by
      ext; rfl
    rw [h]
    exact congrArg LinearEquiv.toLinearMap (presentationTransport_id (p K.of))
  map_comp {K L M} a b := by
    apply Core.hom_ext
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    change (presentationTransport (p K.of) (p M.of)
      ((perfectTwoTermComplexProperty R).ι.mapIso (a.iso ≪≫ b.iso))).toLinearMap =
      ((presentationTransport (p K.of) (p L.of)
        ((perfectTwoTermComplexProperty R).ι.mapIso a.iso)).trans
        (presentationTransport (p L.of) (p M.of)
          ((perfectTwoTermComplexProperty R).ι.mapIso b.iso))).toLinearMap
    rw [presentationTransport_comp]
    rfl

private theorem determinantFunctor_map_apply {R : Type u} [CommRing R]
    (p : ∀ K : PerfectTwoTermComplex R, TwoTermPresentation K.obj)
    {K L : PerfectTwoTermComplex R}
    (a : (⟨K⟩ : Core (PerfectTwoTermComplex R)) ⟶ ⟨L⟩)
    (x : presentationDeterminant (p K)) :
    ((determinantFunctor p).map a).iso.hom x =
      presentationTransport (p K) (p L)
        ((perfectTwoTermComplexProperty R).ι.mapIso a.iso) x := rfl

/-- **Stacks 0FJM.** There is a determinant functor from perfect complexes of Tor-amplitude
`[-1, 0]` and isomorphisms to invertible modules and isomorphisms. Its value is canonically
identified with the determinant line of every finite-projective two-term presentation; on
rank-zero objects the determinant of the differential defines an element natural under all
isomorphisms. -/
@[stacks 0FJM]
public theorem exists_determinantFunctor_natural_delta {R : Type u} [CommRing R] :
    ∃ (det : Core (PerfectTwoTermComplex R) ⥤ Core (InvertibleModule R))
      (comparison : ∀ (K : PerfectTwoTermComplex R) (P : TwoTermPresentation K.obj),
        letI := P.finite (-1)
        letI := P.projective (-1)
        letI := P.finite 0
        letI := P.projective 0
        (det.obj ⟨K⟩).of.obj ≃ₗ[R]
          TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom)
      (delta : ∀ (K : PerfectTwoTermComplex R),
        IsRankZero K.obj → (det.obj ⟨K⟩).of.obj),
      (∀ (K : PerfectTwoTermComplex R) (P : TwoTermPresentation K.obj)
          (hP : P.IsRankZero),
        letI := P.finite (-1)
        letI := P.projective (-1)
        letI := P.finite 0
        letI := P.projective 0
        (comparison K P).toLinearMap (delta K ⟨P, hP⟩) =
          TwoTermComplex.delta (P.complex.d (-1) 0).hom hP) ∧
      (∀ (K L : PerfectTwoTermComplex R) (P : TwoTermPresentation K.obj)
          (Q : TwoTermPresentation L.obj)
          (a : (⟨K⟩ : Core (PerfectTwoTermComplex R)) ⟶ ⟨L⟩)
          (f : P.complex ⟶ Q.complex)
          (_hf : P.iso.hom ≫ DerivedCategory.Q.map f ≫ Q.iso.inv = a.iso.hom.hom)
          (hs : (P.hom Q f).IsDegreewiseSurjective) (hq : (P.hom Q f).IsQuasiIso),
        letI := P.finite (-1)
        letI := P.projective (-1)
        letI := P.finite 0
        letI := P.projective 0
        letI := Q.finite (-1)
        letI := Q.projective (-1)
        letI := Q.finite 0
        letI := Q.projective 0
        let g := P.hom Q f
        letI := TwoTermComplex.kernel_finite g.neg hs.1
        letI := TwoTermComplex.kernel_projective g.neg hs.1
        letI := TwoTermComplex.kernel_finite g.zero hs.2
        letI := TwoTermComplex.kernel_projective g.zero hs.2
        ∀ x,
          (comparison L Q).toLinearMap ((det.map a).iso.hom x) =
            (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso
              (P.complex.d (-1) 0).hom (Q.complex.d (-1) 0).hom g hs hq).equiv
                ((comparison K P).toLinearMap x)) ∧
      ∀ (K L : PerfectTwoTermComplex R)
        (a : (⟨K⟩ : Core (PerfectTwoTermComplex R)) ⟶ ⟨L⟩)
        (hK : IsRankZero K.obj) (hL : IsRankZero L.obj),
        (det.map a).iso.hom (delta K hK) = delta L hL
    := by
  classical
  let p : ∀ K : PerfectTwoTermComplex R, TwoTermPresentation K.obj :=
    fun K => Classical.choice (nonempty_twoTermPresentation K)
  let comparison (K : PerfectTwoTermComplex R) (P : TwoTermPresentation K.obj) :
      presentationDeterminant (p K) ≃ₗ[R] presentationDeterminant P :=
    presentationTransport (p K) P (Iso.refl K.obj)
  let delta (K : PerfectTwoTermComplex R) (h : IsRankZero K.obj) :
      presentationDeterminant (p K) :=
    presentationTransport h.choose (p K) (Iso.refl K.obj)
      (presentationDelta h.choose h.choose_spec)
  have hc (K : PerfectTwoTermComplex R) (P : TwoTermPresentation K.obj)
      (hP : P.IsRankZero) : comparison K P (delta K ⟨P, hP⟩) = presentationDelta P hP := by
    let h : IsRankZero K.obj := ⟨P, hP⟩
    show presentationTransport (p K) P (Iso.refl K.obj)
      (presentationTransport h.choose (p K) (Iso.refl K.obj)
        (presentationDelta h.choose h.choose_spec)) = _
    rw [presentationTransport_comp_apply]
    exact presentationTransport_apply_delta _ _ _ _ hP
  refine ⟨determinantFunctor p, comparison, delta, ?_, ?_, ?_⟩
  · intro K P hP
    exact hc K P hP
  · intro K L P Q a f hf hs hq
    dsimp only
    intro x
    change presentationDeterminant (p K) at x
    rw [determinantFunctor_map_apply]
    exact presentationTransport_naturality (p K) (p L) P Q _ f hf hs hq x
  · intro K L a hK hL
    rw [determinantFunctor_map_apply]
    let e : K.obj ≅ L.obj := (perfectTwoTermComplexProperty R).ι.mapIso a.iso
    apply (comparison L hL.choose).injective
    rw [hc L hL.choose hL.choose_spec]
    show presentationTransport (p L) hL.choose (Iso.refl L.obj)
      (presentationTransport (p K) (p L) e
        (presentationTransport hK.choose (p K) (Iso.refl K.obj)
          (presentationDelta hK.choose hK.choose_spec))) = _
    rw [presentationTransport_comp_apply, presentationTransport_comp_apply]
    exact presentationTransport_apply_delta _ _ _ hK.choose_spec hL.choose_spec

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

@[expose] public section

/-! ### The determinant as named data -/

/-- A two-term presentation by finite projective modules of a perfect object of Tor-amplitude
in `[-1, 0]`, chosen once and for all for each such object. -/
public noncomputable def presentation (R : Type u) [CommRing R]
    (K : PerfectTwoTermComplex R) : TwoTermPresentation K.obj :=
  Classical.choice (nonempty_twoTermPresentation K)

/-- **Stacks 0FJM.** The determinant functor, from perfect objects of the derived category of
`R`-modules of Tor-amplitude in `[-1, 0]` with isomorphisms as morphisms, to invertible
`R`-modules with isomorphisms as morphisms. -/
@[stacks 0FJM "the determinant functor as a named definition, rather than as the subject of an
existential quantifier"]
public noncomputable def det (R : Type u) [CommRing R] :
    Core (PerfectTwoTermComplex R) ⥤ Core (InvertibleModule R) :=
  determinantFunctor (presentation R)

/-- The determinant of a perfect object of Tor-amplitude in `[-1, 0]` is canonically isomorphic
to the determinant line of any of its two-term presentations by finite projective modules. -/
public noncomputable def detPresentationIso {R : Type u} [CommRing R]
    (K : PerfectTwoTermComplex R) (P : TwoTermPresentation K.obj) :
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    ((det R).obj ⟨K⟩).of.obj ≃ₗ[R] TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom :=
  presentationTransport (presentation R K) P (Iso.refl K.obj)

/-- **Stacks 0FJM.** The canonical element of the determinant of a perfect object of
Tor-amplitude in `[-1, 0]` and rank zero, given by the determinant of the differential of a
two-term presentation of it. -/
@[stacks 0FJM "the canonical section δ of the determinant of a rank-zero object, as a named
definition"]
public noncomputable def delta {R : Type u} [CommRing R] (K : PerfectTwoTermComplex R)
    (hK : IsRankZero K.obj) : ((det R).obj ⟨K⟩).of.obj :=
  presentationTransport hK.choose (presentation R K) (Iso.refl K.obj)
    (presentationDelta hK.choose hK.choose_spec)

private theorem det_map_apply {R : Type u} [CommRing R] {K L : PerfectTwoTermComplex R}
    (a : (⟨K⟩ : Core (PerfectTwoTermComplex R)) ⟶ ⟨L⟩)
    (x : presentationDeterminant (presentation R K)) :
    ((det R).map a).iso.hom x =
      presentationTransport (presentation R K) (presentation R L)
        ((perfectTwoTermComplexProperty R).ι.mapIso a.iso) x :=
  rfl

/-- The comparison between the determinant of a rank-zero perfect object of Tor-amplitude in
`[-1, 0]` and the determinant line of a rank-zero two-term presentation of it matches the
canonical elements of the two. -/
public theorem detPresentationIso_delta {R : Type u} [CommRing R]
    (K : PerfectTwoTermComplex R) (P : TwoTermPresentation K.obj) (hP : P.IsRankZero) :
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    (detPresentationIso K P) (delta K ⟨P, hP⟩) =
      TwoTermComplex.delta (P.complex.d (-1) 0).hom hP := by
  let h : IsRankZero K.obj := ⟨P, hP⟩
  show presentationTransport (presentation R K) P (Iso.refl K.obj)
    (presentationTransport h.choose (presentation R K) (Iso.refl K.obj)
      (presentationDelta h.choose h.choose_spec)) = _
  rw [presentationTransport_comp_apply]
  exact presentationTransport_apply_delta _ _ _ _ hP

/-- **Stacks 0FJM.** The determinant functor carries the canonical element of a rank-zero
perfect object of Tor-amplitude in `[-1, 0]` to the canonical element of any isomorphic
object. -/
@[stacks 0FJM "the compatibility det(a)(δ(L)) = δ(K) of the canonical section with
isomorphisms, as a named theorem"]
public theorem det_map_delta {R : Type u} [CommRing R] {K L : PerfectTwoTermComplex R}
    (a : (⟨K⟩ : Core (PerfectTwoTermComplex R)) ⟶ ⟨L⟩)
    (hK : IsRankZero K.obj) (hL : IsRankZero L.obj) :
    ((det R).map a).iso.hom (delta K hK) = delta L hL := by
  apply (detPresentationIso L hL.choose).injective
  rw [detPresentationIso_delta L hL.choose hL.choose_spec]
  show presentationTransport (presentation R L) hL.choose (Iso.refl L.obj)
    (presentationTransport (presentation R K) (presentation R L)
      ((perfectTwoTermComplexProperty R).ι.mapIso a.iso)
      (presentationTransport hK.choose (presentation R K) (Iso.refl K.obj)
        (presentationDelta hK.choose hK.choose_spec))) = _
  rw [presentationTransport_comp_apply, presentationTransport_comp_apply]
  exact presentationTransport_apply_delta _ _ _ hK.choose_spec hL.choose_spec

/-- The determinant functor computes an isomorphism that is represented by a
degreewise-surjective quasi-isomorphism of two-term presentations as the canonical determinant
equivalence of that quasi-isomorphism. -/
public theorem detPresentationIso_det_map {R : Type u} [CommRing R]
    (K L : PerfectTwoTermComplex R) (P : TwoTermPresentation K.obj)
    (Q : TwoTermPresentation L.obj)
    (a : (⟨K⟩ : Core (PerfectTwoTermComplex R)) ⟶ ⟨L⟩) (f : P.complex ⟶ Q.complex)
    (_hf : P.iso.hom ≫ DerivedCategory.Q.map f ≫ Q.iso.inv = a.iso.hom.hom)
    (hs : (P.hom Q f).IsDegreewiseSurjective) (hq : (P.hom Q f).IsQuasiIso) :
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    letI := Q.finite (-1)
    letI := Q.projective (-1)
    letI := Q.finite 0
    letI := Q.projective 0
    let g := P.hom Q f
    letI := TwoTermComplex.kernel_finite g.neg hs.1
    letI := TwoTermComplex.kernel_projective g.neg hs.1
    letI := TwoTermComplex.kernel_finite g.zero hs.2
    letI := TwoTermComplex.kernel_projective g.zero hs.2
    ∀ x,
      (detPresentationIso L Q).toLinearMap (((det R).map a).iso.hom x) =
        (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso
          (P.complex.d (-1) 0).hom (Q.complex.d (-1) 0).hom g hs hq).equiv
            ((detPresentationIso K P).toLinearMap x) := by
  dsimp only
  intro x
  change presentationDeterminant (presentation R K) at x
  rw [det_map_apply]
  exact presentationTransport_naturality (presentation R K) (presentation R L) P Q _ f _hf hs
    hq x

namespace TwoTermPresentation

end TwoTermPresentation

end

end

end TwoTermDeterminant
