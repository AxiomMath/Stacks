module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceFiniteFamilies
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomComplexStalk

/-!
# The stalk of a product of sheaves of modules with finite support

Let `Rc` be a sheaf of commutative rings on a topological space `X`, write `O_X` for the
underlying sheaf of rings, and let `x ∈ X`. The stalk at `x` is a filtered colimit, so it
commutes with coproducts with no finiteness hypothesis at all — that is Stacks 01AH, available
as `Stacks.SheafOfModules.SheafHomStalk.modStalkCoprodEquiv`. Products are the other direction,
and a colimit does not commute with them in general. This file proves the case in which it
does: if all but finitely many factors vanish, the product is a *finite* product, hence a finite
biproduct, and the stalk functor is additive.

The application is the degree-`n` term of the internal Hom complex `SheafHom(E, F)` of
Stacks 0A8Z. By `AlgebraicGeometry.RingedSite.homDegreeIsLimit` that term is the product over
`q : ℤ` of the internal Hom sheaves `SheafHom(E^{-q}, F^{n-q})`, with the projections
`AlgebraicGeometry.RingedSite.homDegreeProjection`; for `E` bounded all but finitely many of
those sheaves vanish, and the conclusion is that the stalk at `x` of the degree-`n` term is the
product over `q : ℤ` of their stalks. In particular the stalk maps of the projections are
*jointly injective*: an element of the stalk of the degree-`n` term is determined by its
components.

## Main definitions

* `Stacks.SheafOfModules.SheafHomStalk.directSumLequivPiOfFiniteSupport`: a direct sum all but
  finitely many of whose summands are trivial is the full product.
* `Stacks.SheafOfModules.SheafHomStalk.modStalkProdEquiv`: **the product half of the
  stalk/limit interchange**, in general. For a family `P` of `O_X`-modules and a finite set of
  indices off which `P` vanishes, the stalk at `x` of `∏ᶜ P` is the product of the stalks, the
  `i`-th component being the stalk map of the `i`-th projection.
* `Stacks.SheafOfModules.sheafHomDegreeStalkCoprodEquiv`: the stalk at `x` of the degree-`n`
  term of `SheafHom(E, F)`, for `E` bounded, as the direct sum over `q : ℤ` of the stalks of
  the internal Hom sheaves of the terms.
* `Stacks.SheafOfModules.sheafHomDegreeStalkProdEquiv`: **the product half at the degree-`n`
  term**: the same stalk as the product over `q : ℤ` of those stalks, the `q`-th component
  being the stalk map of `AlgebraicGeometry.RingedSite.homDegreeProjection X E F n q`.

## Main results

* `Stacks.SheafOfModules.SheafHomStalk.modStalkMap_π_jointly_injective`: for a family with
  finite support, the stalk maps of the product projections are jointly injective.
* `Stacks.SheafOfModules.modStalkMap_homDegreeProjection_jointly_injective`: for `E` bounded,
  the stalk maps of the degree projections of `SheafHom(E, F)` are jointly injective. This is
  what the comparison of complexes needs: a germ of a local cochain is determined by the
  stalks of its components.

## Implementation notes

The bridge between the two halves is
`AlgebraicGeometry.RingedSite.productCoproductIsoOfFiniteSupport`, which identifies a product
with the coproduct over the same index when all but finitely many factors vanish. Composing its
stalk with `modStalkCoprodEquiv` gives the product half, and the composite is *computed* —
rather than unfolded, which is impossible across modules since the declarations of
`StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexOfAStrictlyPerfectComplex`
are `public` but not `@[expose]` — from the characterisations
`AlgebraicGeometry.RingedSite.productCoproductIsoOfFiniteSupport_inv_π_self` and
`AlgebraicGeometry.RingedSite.productCoproductIsoOfFiniteSupport_inv_π_of_ne`.

At the degree-`n` term the product is not literally `∏ᶜ`: the term is a limit *cone point*,
exhibited as the product by `homDegreeIsLimit`. Rather than transport the general statement
along `IsLimit.conePointUniqueUpToIso`, the degree-level statement is obtained from
`strictlyPerfectHomDegreeIso` and its two characterisations
`AlgebraicGeometry.RingedSite.strictlyPerfectHomDegreeIso_inv_homDegreeProjection` and
`AlgebraicGeometry.RingedSite.strictlyPerfectHomDegreeIso_inv_homDegreeProjection_of_ne`, which
have that transport already built in.

The hypothesis is finite support, and nothing else. In the general statement it is a `Finset`
of indices together with the vanishing of the family off it; at the degree-`n` term it is
boundedness of `E`, `{i : ℤ | ¬ IsZero (E.X i)}.Finite`, which is exactly the hypothesis of
`strictlyPerfectHomDegreeIso`, and the finite set is the image of that set under negation. The
vanishing of the summands off it is `internalHomSheaf_isZero_of_isZero`. Finiteness is genuinely
needed: for a product over `ℤ` of nonvanishing modules the comparison is not surjective.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry DirectSum

universe u

namespace Stacks.SheafOfModules.SheafHomStalk

/-! ### A direct sum with finite support is a product -/

section DirectSumPi

variable {R : Type*} [Semiring R] {ι : Type*}
  (M : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The canonical map from a direct sum to the product over the same index: a finitely supported
family, read as an arbitrary one. -/
def directSumToPi : (⨁ i, M i) →ₗ[R] ∀ i, M i where
  toFun u i := u i
  map_add' u v := by funext i; simp
  map_smul' r u := funext fun i => DFinsupp.smul_apply r u i

/-- The `i`-th component of `directSumToPi M u` is the `i`-th component of `u`. -/
@[simp]
lemma directSumToPi_apply (u : ⨁ i, M i) (i : ι) : directSumToPi (R := R) M u i = u i := rfl

variable [DecidableEq ι]

/-- **A direct sum with finite support is the product.** If all but finitely many of the modules
`M i` are trivial, the canonical map `directSumToPi` from the direct sum to the product is a
linear equivalence.

The hypotheses are a finite set `s` of indices and triviality of `M i` for every `i ∉ s`;
injectivity needs neither. -/
def directSumLequivPiOfFiniteSupport (s : Finset ι)
    (hs : ∀ i, i ∉ s → Subsingleton (M i)) : (⨁ i, M i) ≃ₗ[R] ∀ i, M i :=
  LinearEquiv.ofBijective (directSumToPi M)
    ⟨fun u v h => DFinsupp.ext fun i => congrFun h i,
      fun v => ⟨DFinsupp.mk s fun i => v i, funext fun j => by
        change (DFinsupp.mk s fun i => v i) j = v j
        rw [DFinsupp.mk_apply]
        split
        · rfl
        · exact (hs j ‹_›).elim (0 : M j) (v j)⟩⟩

/-- The `i`-th component of the image of `u` under `directSumLequivPiOfFiniteSupport` is the
`i`-th component of `u`. -/
@[simp]
lemma directSumLequivPiOfFiniteSupport_apply (s : Finset ι)
    (hs : ∀ i, i ∉ s → Subsingleton (M i)) (u : ⨁ i, M i) (i : ι) :
    directSumLequivPiOfFiniteSupport (R := R) M s hs u i = u i := rfl

/-- A linear map out of a direct sum which is the identity on the `q`-th summand and kills every
other summand is the `q`-th component. The two hypotheses are exactly those two statements. -/
lemma eq_component_apply {q : ι} (f : (⨁ i, M i) →ₗ[R] M q)
    (hself : ∀ t : M q, f (DirectSum.of M q t) = t)
    (hne : ∀ (r : ι) (t : M r), r ≠ q → f (DirectSum.of M r t) = 0) (u : ⨁ i, M i) :
    f u = u q := by
  have key : f = DirectSum.component R ι M q := by
    refine DirectSum.linearMap_ext _ fun r => LinearMap.ext fun t => ?_
    simp only [LinearMap.comp_apply, DirectSum.lof_eq_of]
    by_cases hr : r = q
    · subst hr
      rw [hself]
      exact (DirectSum.of_eq_same r t).symm
    · rw [hne r t hr]
      exact (DirectSum.of_eq_of_ne r q t (Ne.symm hr)).symm
  exact LinearMap.congr_fun key u

/-- `eq_component_apply` for a linear map of the form `f ∘ e`, with `e` out of the direct sum. -/
private lemma comp_apply_eq_component_apply {N : Type*} [AddCommMonoid N] [Module R N] {q : ι}
    (e : (⨁ i, M i) ≃ₗ[R] N) (f : N →ₗ[R] M q)
    (hself : ∀ t : M q, f (e (DirectSum.of M q t)) = t)
    (hne : ∀ (r : ι) (t : M r), r ≠ q → f (e (DirectSum.of M r t)) = 0) (u : ⨁ i, M i) :
    f (e u) = u q :=
  eq_component_apply M (f.comp e.toLinearMap) hself hne u

/-- If the maps `π i` read off the components of `e u`, then the components of `e.symm t`
followed by `directSumLequivPiOfFiniteSupport` are the `π i t`. -/
private lemma symm_trans_directSumLequivPiOfFiniteSupport_apply {N : Type*} [AddCommMonoid N]
    [Module R N] (e : (⨁ i, M i) ≃ₗ[R] N) (π : ∀ i, N →ₗ[R] M i)
    (h : ∀ i u, π i (e u) = u i) (s : Finset ι) (hs : ∀ i, i ∉ s → Subsingleton (M i)) (t : N)
    (i : ι) :
    (e.symm.trans (directSumLequivPiOfFiniteSupport M s hs)) t i = π i t := by
  rw [LinearEquiv.trans_apply, directSumLequivPiOfFiniteSupport_apply, ← h i (e.symm t),
    LinearEquiv.apply_symm_apply]

end DirectSumPi

/-! ### The stalk of a vanishing sheaf of modules, and iterated stalk maps -/

section Basic

variable {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}

/-- The stalk at `x` of a zero `O_X`-module is trivial: every germ is the germ of a section, and
every section of a zero sheaf of modules vanishes. -/
lemma subsingleton_modStalk_of_isZero {M : SheafOfModules.{u} (structureSheaf Rc)}
    (hM : IsZero M) (x : X) : Subsingleton (modStalk M x) := by
  have key : ∀ σ : modStalk M x, σ = 0 := by
    intro σ
    obtain ⟨W, hxW, s, rfl⟩ := exists_germ_eq M σ
    rw [eq_zero_of_isZero hM (op W) s, germAt_zero]
  exact ⟨fun t t' => (key t).trans (key t').symm⟩

/-- Functoriality of the stalk, in the form in which two successive stalk maps are applied to a
germ. -/
lemma modStalkMap_modStalkMap {M N P : SheafOfModules.{u} (structureSheaf Rc)} (f : M ⟶ N)
    (g : N ⟶ P) (x : X) (t : modStalk M x) :
    modStalkMap g x (modStalkMap f x t) = modStalkMap (f ≫ g) x t :=
  (LinearMap.congr_fun (modStalkMap_comp f g x) t).symm

/-- Two successive stalk maps applied to the germ carried by the `i`-th summand of a coproduct:
the result is the stalk map of `Sigma.ι P i ≫ e ≫ p`. That composite is exactly what the
characterisations of the two comparison isomorphisms used below compute, on the diagonal and
off it, so this is the single computation behind both product halves. -/
lemma modStalkMap_modStalkMap_modStalkCoprodEquiv_of {ι : Type} [DecidableEq ι]
    (P : ι → SheafOfModules.{u} (structureSheaf Rc)) (x : X)
    {Y Z : SheafOfModules.{u} (structureSheaf Rc)} (e : ∐ P ⟶ Y) (p : Y ⟶ Z) (i : ι)
    (t : modStalk (P i) x) :
    modStalkMap p x (modStalkMap e x (modStalkCoprodEquiv P x (DirectSum.of _ i t))) =
      modStalkMap (Sigma.ι P i ≫ e ≫ p) x t :=
  (congrArg (fun z => modStalkMap p x (modStalkMap e x z))
      (modStalkCoprodEquiv_of P x i t)).trans
    (((congrArg (fun z => modStalkMap p x z)
          (modStalkMap_modStalkMap (Sigma.ι P i) e x t)).trans
        (modStalkMap_modStalkMap (Sigma.ι P i ≫ e) p x t)).trans
      (congrArg (fun φ => modStalkMap φ x t) (Category.assoc (Sigma.ι P i) e p)))

end Basic

/-! ### The stalk of a product with finite support -/

section Product

variable {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}
  {ι : Type} [DecidableEq ι] (P : ι → SheafOfModules.{u} (structureSheaf Rc)) [HasProduct P]
  (x : X) (s : Finset ι) (hs : ∀ i, i ∉ s → IsZero (P i))

/-- The comparison from the direct sum of the stalks to the stalk of the product, for a family
all but finitely many of whose members vanish: the stalk of
`AlgebraicGeometry.RingedSite.productCoproductIsoOfFiniteSupport`, composed with Stacks 01AH for
the stalk of the coproduct. -/
def directSumModStalkProdEquiv :
    (⨁ i : ι, modStalk (P i) x) ≃ₗ[ringStalk Rc x] modStalk (∏ᶜ P) x :=
  (modStalkCoprodEquiv P x).trans
    (modStalkMapEquiv (RingedSite.productCoproductIsoOfFiniteSupport P s hs).symm x)

/-- `directSumModStalkProdEquiv` is the stalk map of the inverse of
`productCoproductIsoOfFiniteSupport` applied after `modStalkCoprodEquiv`. -/
lemma directSumModStalkProdEquiv_apply (u : ⨁ i : ι, modStalk (P i) x) :
    directSumModStalkProdEquiv P x s hs u =
      modStalkMap (RingedSite.productCoproductIsoOfFiniteSupport P s hs).inv x
        (modStalkCoprodEquiv P x u) := rfl

/-- The `i`-th projection of the comparison `directSumModStalkProdEquiv` reads off the `i`-th
component of the direct sum. This is the whole computation: by the characterisation of
`productCoproductIsoOfFiniteSupport` the composite of the `j`-th coproduct inclusion, of the
inverse of that isomorphism and of the `i`-th projection is the identity for `j = i` and zero
otherwise. -/
lemma modStalkMap_π_directSumModStalkProdEquiv (i : ι) (u : ⨁ i : ι, modStalk (P i) x) :
    modStalkMap (Pi.π P i) x (directSumModStalkProdEquiv P x s hs u) = u i := by
  refine comp_apply_eq_component_apply (R := ringStalk Rc x)
    (fun j => (modStalk (P j) x : Type u)) (directSumModStalkProdEquiv P x s hs)
    (modStalkMap (Pi.π P i) x) ?_ ?_ u
  · intro t
    rw [directSumModStalkProdEquiv_apply,
      modStalkMap_modStalkMap_modStalkCoprodEquiv_of P x
        (RingedSite.productCoproductIsoOfFiniteSupport P s hs).inv (Pi.π P i) i t,
      RingedSite.productCoproductIsoOfFiniteSupport_inv_π_self P s hs i, modStalkMap_id]
    rfl
  · intro j t hji
    rw [directSumModStalkProdEquiv_apply,
      modStalkMap_modStalkMap_modStalkCoprodEquiv_of P x
        (RingedSite.productCoproductIsoOfFiniteSupport P s hs).inv (Pi.π P i) j t,
      RingedSite.productCoproductIsoOfFiniteSupport_inv_π_of_ne P s hs hji, modStalkMap_zero]
    rfl

/-- **The product half of the stalk/limit interchange.** For a family `P` of `O_X`-modules all
but finitely many of which vanish, the stalk at `x` of the product `∏ᶜ P` is the product of the
stalks, the `i`-th component of a germ being the stalk map of the `i`-th projection
(`modStalkProdEquiv_apply`).

The hypotheses are a finite set `s : Finset ι` of indices and `hs : ∀ i, i ∉ s → IsZero (P i)`,
and nothing else. Finiteness is what the statement rests on: the stalk is a colimit, so it
commutes with the coproduct unconditionally, and finite support is what makes the product agree
with the coproduct. -/
def modStalkProdEquiv :
    modStalk (∏ᶜ P) x ≃ₗ[ringStalk Rc x] ∀ i : ι, modStalk (P i) x :=
  (directSumModStalkProdEquiv P x s hs).symm.trans
    (directSumLequivPiOfFiniteSupport (R := ringStalk Rc x)
      (fun i => (modStalk (P i) x : Type u)) s
      fun i hi => subsingleton_modStalk_of_isZero (hs i hi) x)

/-- The `i`-th component of `modStalkProdEquiv P x s hs t` is the image of the germ `t` under the
stalk map of the `i`-th projection `Pi.π P i`. -/
@[simp]
lemma modStalkProdEquiv_apply (t : modStalk (∏ᶜ P) x) (i : ι) :
    modStalkProdEquiv P x s hs t i = modStalkMap (Pi.π P i) x t := by
  exact symm_trans_directSumLequivPiOfFiniteSupport_apply (R := ringStalk Rc x)
    (fun j => (modStalk (P j) x : Type u)) (directSumModStalkProdEquiv P x s hs)
    (fun j => modStalkMap (Pi.π P j) x) (modStalkMap_π_directSumModStalkProdEquiv P x s hs) _ _ t i

omit [DecidableEq ι] in
include s hs in
/-- **Joint injectivity of the stalk maps of the projections.** For a family all but finitely
many of whose members vanish, two germs of the product with the same image under every
projection are equal.

Hypotheses: the finite set `s` and the vanishing `hs` off it, as for `modStalkProdEquiv`. -/
theorem modStalkMap_π_jointly_injective {t t' : modStalk (∏ᶜ P) x}
    (h : ∀ i : ι, modStalkMap (Pi.π P i) x t = modStalkMap (Pi.π P i) x t') : t = t' := by
  classical
  exact (modStalkProdEquiv P x s hs).injective <| funext fun i => by
    simpa only [modStalkProdEquiv_apply] using h i

end Product

end Stacks.SheafOfModules.SheafHomStalk

/-! ### The stalk of the degree-`n` term of the internal Hom complex -/

namespace Stacks.SheafOfModules

open Stacks.SheafOfModules.SheafHomStalk

section DegreeProduct

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (E F : CochainComplex (StructureSheafModules Rc) ℤ)
  (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) (n : ℤ) (x : X)

/-- The finite set of indices `q : ℤ` off which the internal Hom sheaf
`SheafHom(E^{-q}, F^{n-q})` vanishes, for `E` bounded: the image of the set of degrees in which
`E` does not vanish under negation. -/
def homDegreeSupport : Finset ℤ := (hE.image (fun i : ℤ => -i)).toFinset

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Off `homDegreeSupport` the internal Hom sheaf of the terms vanishes: for `E` bounded,
`E^{-q}` is zero outside a finite set of `q`, and the internal Hom sheaf out of a zero module is
zero. -/
lemma isZero_internalHomSheaf_of_notMem_homDegreeSupport (q : ℤ)
    (hq : q ∉ homDegreeSupport Rc E hE) :
    IsZero (RingedSite.internalHomSheaf (ringedSite Rc) (E.X (-q)) (F.X (n - q))) := by
  apply RingedSite.internalHomSheaf_isZero_of_isZero
  by_contra h
  exact hq ((Set.Finite.mem_toFinset _).2 ⟨-q, h, neg_neg q⟩)

/-- **The stalk of the degree-`n` term, as a direct sum.** For `E` bounded, the stalk at `x` of
the degree-`n` term of the internal Hom complex `SheafHom(E, F)` of Stacks 0A8Z is the direct
sum over `q : ℤ` of the stalks of the internal Hom sheaves `SheafHom(E^{-q}, F^{n-q})`.

This is the degreewise direct-sum description `strictlyPerfectHomDegreeIso` of Stacks 08DM,
which needs only boundedness of `E`, followed by Stacks 01AH for the stalk of a coproduct, which
needs nothing. There is no hypothesis on the terms of `E` and none on `F`. -/
def sheafHomDegreeStalkCoprodEquiv :
    (⨁ q : ℤ, modStalk
        (RingedSite.internalHomSheaf (ringedSite Rc) (E.X (-q)) (F.X (n - q))) x)
      ≃ₗ[ringStalk Rc x]
      modStalk ((RingedSite.sheafHomComplex (ringedSite Rc) E F).obj.X n) x :=
  (modStalkCoprodEquiv
      (fun q : ℤ => RingedSite.internalHomSheaf (ringedSite Rc) (E.X (-q)) (F.X (n - q)))
      x).trans
    (modStalkMapEquiv (strictlyPerfectHomDegreeIso Rc E F hE n).symm x)

/-- `sheafHomDegreeStalkCoprodEquiv` is the stalk map of the inverse of
`strictlyPerfectHomDegreeIso` applied after `modStalkCoprodEquiv`. -/
lemma sheafHomDegreeStalkCoprodEquiv_apply
    (u : ⨁ q : ℤ, modStalk
      (RingedSite.internalHomSheaf (ringedSite Rc) (E.X (-q)) (F.X (n - q))) x) :
    sheafHomDegreeStalkCoprodEquiv Rc E F hE n x u =
      modStalkMap (strictlyPerfectHomDegreeIso Rc E F hE n).inv x
        (modStalkCoprodEquiv
          (fun q : ℤ =>
            RingedSite.internalHomSheaf (ringedSite Rc) (E.X (-q)) (F.X (n - q))) x u) := rfl

/-- The stalk map of the `q`-th degree projection reads off the `q`-th component of the direct
sum. This is the computation behind the product half at the degree-`n` term: by the
characterisation of `strictlyPerfectHomDegreeIso` the composite of the `r`-th coproduct
inclusion, of the inverse of that isomorphism and of `homDegreeProjection X E F n q` is the
identity for `r = q` and zero otherwise. -/
lemma modStalkMap_homDegreeProjection_sheafHomDegreeStalkCoprodEquiv (q : ℤ)
    (u : ⨁ q : ℤ, modStalk
      (RingedSite.internalHomSheaf (ringedSite Rc) (E.X (-q)) (F.X (n - q))) x) :
    modStalkMap (RingedSite.homDegreeProjection (ringedSite Rc) E F n q) x
        (sheafHomDegreeStalkCoprodEquiv Rc E F hE n x u) = u q := by
  refine comp_apply_eq_component_apply (R := ringStalk Rc x)
    (fun r : ℤ => (modStalk
      (RingedSite.internalHomSheaf (ringedSite Rc) (E.X (-r)) (F.X (n - r))) x : Type u))
    (sheafHomDegreeStalkCoprodEquiv Rc E F hE n x)
    (modStalkMap (RingedSite.homDegreeProjection (ringedSite Rc) E F n q) x) ?_ ?_ u
  · intro t
    rw [sheafHomDegreeStalkCoprodEquiv_apply]
    refine Eq.trans (modStalkMap_modStalkMap_modStalkCoprodEquiv_of
      (fun r : ℤ => RingedSite.internalHomSheaf (ringedSite Rc) (E.X (-r)) (F.X (n - r))) x
      (strictlyPerfectHomDegreeIso Rc E F hE n).inv
      (RingedSite.homDegreeProjection (ringedSite Rc) E F n q) q t) ?_
    exact (congrArg (fun φ => modStalkMap φ x t)
      (RingedSite.strictlyPerfectHomDegreeIso_inv_homDegreeProjection
        (ringedSite Rc) E F hE n q)).trans
      (LinearMap.congr_fun (modStalkMap_id x) t)
  · intro r t hr
    rw [sheafHomDegreeStalkCoprodEquiv_apply]
    refine Eq.trans (modStalkMap_modStalkMap_modStalkCoprodEquiv_of
      (fun r : ℤ => RingedSite.internalHomSheaf (ringedSite Rc) (E.X (-r)) (F.X (n - r))) x
      (strictlyPerfectHomDegreeIso Rc E F hE n).inv
      (RingedSite.homDegreeProjection (ringedSite Rc) E F n q) r t) ?_
    exact (congrArg (fun φ => modStalkMap φ x t)
      (RingedSite.strictlyPerfectHomDegreeIso_inv_homDegreeProjection_of_ne
        (ringedSite Rc) E F hE n hr)).trans
      (LinearMap.congr_fun (modStalkMap_zero x) t)

/-- **The product half at the degree-`n` term.** For `E` bounded, the stalk at `x` of the
degree-`n` term of the internal Hom complex `SheafHom(E, F)` of Stacks 0A8Z is the *product*
over `q : ℤ` of the stalks of the internal Hom sheaves `SheafHom(E^{-q}, F^{n-q})`, the `q`-th
component of a germ being the stalk map of the `q`-th degree projection
(`sheafHomDegreeStalkProdEquiv_apply`).

The only hypothesis is `hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite`, the boundedness of `E` that
`strictlyPerfectHomDegreeIso` already assumes; there is none on the terms of `E` and none on
`F`. Boundedness is what makes the product a finite one: off the finite set
`homDegreeSupport Rc E hE` the internal Hom sheaves vanish, hence so do their stalks, and the
direct sum of the stalks is then the full product. -/
def sheafHomDegreeStalkProdEquiv :
    modStalk ((RingedSite.sheafHomComplex (ringedSite Rc) E F).obj.X n) x ≃ₗ[ringStalk Rc x]
      ∀ q : ℤ, modStalk
        (RingedSite.internalHomSheaf (ringedSite Rc) (E.X (-q)) (F.X (n - q))) x :=
  (sheafHomDegreeStalkCoprodEquiv Rc E F hE n x).symm.trans
    (directSumLequivPiOfFiniteSupport (R := ringStalk Rc x)
      (fun q : ℤ => (modStalk
        (RingedSite.internalHomSheaf (ringedSite Rc) (E.X (-q)) (F.X (n - q))) x : Type u))
      (homDegreeSupport Rc E hE) fun q hq =>
        subsingleton_modStalk_of_isZero
          (isZero_internalHomSheaf_of_notMem_homDegreeSupport Rc E F hE n q hq) x)

/-- The `q`-th component of `sheafHomDegreeStalkProdEquiv Rc E F hE n x t` is the image of the
germ `t` under the stalk map of the `q`-th degree projection `homDegreeProjection`. -/
@[simp]
lemma sheafHomDegreeStalkProdEquiv_apply
    (t : modStalk ((RingedSite.sheafHomComplex (ringedSite Rc) E F).obj.X n) x) (q : ℤ) :
    sheafHomDegreeStalkProdEquiv Rc E F hE n x t q =
      modStalkMap (RingedSite.homDegreeProjection (ringedSite Rc) E F n q) x t := by
  exact symm_trans_directSumLequivPiOfFiniteSupport_apply (R := ringStalk Rc x)
    (fun r : ℤ => (modStalk
      (RingedSite.internalHomSheaf (ringedSite Rc) (E.X (-r)) (F.X (n - r))) x : Type u))
    (sheafHomDegreeStalkCoprodEquiv Rc E F hE n x)
    (fun r => modStalkMap (RingedSite.homDegreeProjection (ringedSite Rc) E F n r) x)
    (modStalkMap_homDegreeProjection_sheafHomDegreeStalkCoprodEquiv Rc E F hE n x) _ _ t q

include hE in
/-- **Joint injectivity of the stalk maps of the degree projections.** For `E` bounded, two
germs at `x` of the degree-`n` term of the internal Hom complex `SheafHom(E, F)` with the same
image under the stalk map of every degree projection are equal.

The only hypothesis is boundedness of `E`, `hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite`; there is
none on the terms of `E` and none on `F`. This is the form in which the product half is used:
`homDegreeIsLimit` makes the degree-`n` term the product of the internal Hom sheaves of the
terms, and joint injectivity of the stalk maps of its projections says that a germ of a local
cochain is determined by the stalks of its components. -/
theorem modStalkMap_homDegreeProjection_jointly_injective
    {t t' : modStalk ((RingedSite.sheafHomComplex (ringedSite Rc) E F).obj.X n) x}
    (h : ∀ q : ℤ, modStalkMap (RingedSite.homDegreeProjection (ringedSite Rc) E F n q) x t =
      modStalkMap (RingedSite.homDegreeProjection (ringedSite Rc) E F n q) x t') : t = t' :=
  (sheafHomDegreeStalkProdEquiv Rc E F hE n x).injective <| funext fun q => by
    simpa only [sheafHomDegreeStalkProdEquiv_apply] using h q

include hE in
/-- The zero form of joint injectivity: a germ of the degree-`n` term all of whose degree
projections have vanishing stalk is itself zero. Hypothesis: `E` bounded. -/
theorem eq_zero_of_modStalkMap_homDegreeProjection_eq_zero
    {t : modStalk ((RingedSite.sheafHomComplex (ringedSite Rc) E F).obj.X n) x}
    (h : ∀ q : ℤ,
      modStalkMap (RingedSite.homDegreeProjection (ringedSite Rc) E F n q) x t = 0) :
    t = 0 :=
  modStalkMap_homDegreeProjection_jointly_injective Rc E F hE n x fun q =>
    (h q).trans (map_zero _).symm

end DegreeProduct

end Stacks.SheafOfModules

end
