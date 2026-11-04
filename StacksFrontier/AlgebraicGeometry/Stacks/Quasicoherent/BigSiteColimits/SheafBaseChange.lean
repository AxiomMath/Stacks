module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.BaseChangeComparison

/-!
# The sections of a presented sheaf of modules over a covering object are a base change

Let `R` be a sheaf of rings on a site, let a sheaf of modules `N` over `R` be presented as the
cokernel of a map between two coproducts `Q` and `P` of copies of the universe lift of the
structure sheaf, and let `h : W ⟶ T` be a morphism of the site.  Write `A` for a commutative
ring acting on the sections over `T` and `B` for one acting on the sections over `W`.  This file
assembles, from the two ingredients the rest of the development supplies, the comparison

```
B ⊗[A] N(T) ≃ₗ[B] N(W)
```

carrying `1 ⊗ₜ n` to the restriction of `n` along `h`.  The two ingredients are:

* *bases.*  Over an object all of whose covering sieves contain a finite covering family the
  sections of a coproduct of copies of the structure sheaf are the finitely supported families
  of sections of the structure sheaf, so the tautological generators are a basis
  (`SheafOfModules.tautBasis`).  Four such bases — for `Q` and for `P`, over `T` and over `W` —
  are the input here; `Module.Basis.mapCoeffs` is what transports a basis over the ring of
  sections of the structure sheaf to one over the commutative ring the caller has identified
  that ring with, and the hypotheses below ask only that the basis vectors are the tautological
  generators.
* *exactness of the sections of the presentation at `T` and at `W`*: the presenting map is
  surjective on the sections over either object, it kills the composite with the relation map,
  and over `W` a section it kills is a value of the relation map.  These are four statements
  about one presentation at one object; none of them compares sections at two different objects,
  and no flatness is involved.

Everything else is `Module.BaseChange.bijective_liftBaseChange_of_presentation`, a diagram chase
using from the theory of the tensor product only that a surjection stays surjective after
tensoring.  The restriction maps of the three sheaves supply the two commuting squares by their
compatibility with the tautological generators, which is
`SheafOfModules.restrict_tautGen` and needs no hypothesis at all.

The last result of the file feeds the comparison back into
`SheafOfModules.detectsRange_of_baseChangeEquiv`: if `B` is in addition faithfully flat over `A`,
then the presenting morphism detects images along `h`, so a section of `N` over `T` which lifts
over `W` lifts over `T`.

## Main results

* `SheafOfModules.bijective_liftBaseChange_of_tautBasis`: a coproduct of copies of the structure
  sheaf whose sections over `T` and over `W` have the tautological generators as bases has its
  sections over `W` the base change of its sections over `T`.
* `SheafOfModules.baseChangeEquivOfPresentationSections`: **the sections of a presented sheaf of
  modules over a covering object as a base change of its sections over the base**, and
  `SheafOfModules.baseChangeEquivOfPresentationSections_one_tmul` for its value on `1 ⊗ₜ n`.
* `SheafOfModules.exists_baseChangeEquiv_of_presentation`: the same statement in the existential
  form a consumer which only needs *some* such comparison uses.
* `SheafOfModules.exists_baseChangeEquiv_of_exact_sections`: the same conclusion with the two
  squares and the four exactness hypotheses replaced by the shape they take when the sections of
  the presented module are the cokernel of the sections of the presentation — the squares become
  the naturality of the two morphisms of sheaves.
* `SheafOfModules.detectsRange_of_presentation`: **a presenting morphism of a sheaf of modules
  detects images along a faithfully flat covering morphism**, given the bases and the exactness
  of the sections of the presentation.

## Implementation notes

The commutative rings, the module structures on the sections and the readings of the morphisms of
sheaves as maps of those modules are all taken as explicit data, as in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.H1Vanishing`: a
`SheafOfModules.{m} R` has `R : Sheaf J RingCat`, so its sections carry a ring and nothing more,
while a base change needs a commutative ring and an algebra, and on a big site of schemes those
are present only through `CategoryTheory.forget₂ CommRingCat RingCat`, which instance search does
not unfold.

The two morphisms of sheaves of modules making up the presentation do not appear in the
statements of the first three results: what those results use of them is the two commuting
squares and the four exactness properties, all of which are properties of the maps of modules.
Only `SheafOfModules.detectsRange_of_presentation`, whose conclusion is about a morphism of
sheaves, mentions one.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe w u v r t

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
  {T W : C}

/-- **A coproduct of copies of the structure sheaf has its sections over `W` the base change of
its sections over `T`**, as soon as the tautological generators are a basis over either object.
Restriction carries the tautological generator indexed by `i` over `T` to the one over `W`
(`SheafOfModules.restrict_tautGen`), so it matches the two bases, and a map matching a basis of
the source with a basis of the target exhibits the target as a base change. -/
theorem bijective_liftBaseChange_of_tautBasis {I : Type w} {M : SheafOfModules.{max t r} R}
    (μ : ∀ _ : I, uliftForPresentation.{u, v, r, r, t} (unit R) ⟶ M) (h : W ⟶ T)
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module A (M.val.obj (op T))] [Module A (M.val.obj (op W))] [Module B (M.val.obj (op W))]
    [IsScalarTower A B (M.val.obj (op W))]
    (basT : Module.Basis I A (M.val.obj (op T))) (basW : Module.Basis I B (M.val.obj (op W)))
    (hbasT : ∀ i, basT i = tautGen μ i (op T)) (hbasW : ∀ i, basW i = tautGen μ i (op W))
    (rM : M.val.obj (op T) →ₗ[A] M.val.obj (op W))
    (hrM : ∀ x, rM x = M.val.restrictₛₗ h.op x) :
    Function.Bijective (rM.liftBaseChange B) :=
  Module.BaseChange.bijective_liftBaseChange_of_basis basT basW rM fun i => by
    rw [hbasT, hrM, restrict_tautGen, hbasW]

section Presentation

variable {K I : Type w} {Q P N : SheafOfModules.{max t r} R}
  (κ : ∀ _ : K, uliftForPresentation.{u, v, r, r, t} (unit R) ⟶ Q)
  (ι : ∀ _ : I, uliftForPresentation.{u, v, r, r, t} (unit R) ⟶ P)
  (h : W ⟶ T) (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Module A (Q.val.obj (op T))] [Module A (P.val.obj (op T))] [Module A (N.val.obj (op T))]
  [Module A (Q.val.obj (op W))] [Module B (Q.val.obj (op W))]
  [IsScalarTower A B (Q.val.obj (op W))]
  [Module A (P.val.obj (op W))] [Module B (P.val.obj (op W))]
  [IsScalarTower A B (P.val.obj (op W))]
  [Module A (N.val.obj (op W))] [Module B (N.val.obj (op W))]
  [IsScalarTower A B (N.val.obj (op W))]
  (basQT : Module.Basis K A (Q.val.obj (op T))) (basQW : Module.Basis K B (Q.val.obj (op W)))
  (basPT : Module.Basis I A (P.val.obj (op T))) (basPW : Module.Basis I B (P.val.obj (op W)))
  (hbasQT : ∀ k, basQT k = tautGen κ k (op T)) (hbasQW : ∀ k, basQW k = tautGen κ k (op W))
  (hbasPT : ∀ i, basPT i = tautGen ι i (op T)) (hbasPW : ∀ i, basPW i = tautGen ι i (op W))
  (rQ : Q.val.obj (op T) →ₗ[A] Q.val.obj (op W))
  (hrQ : ∀ x, rQ x = Q.val.restrictₛₗ h.op x)
  (rP : P.val.obj (op T) →ₗ[A] P.val.obj (op W))
  (hrP : ∀ x, rP x = P.val.restrictₛₗ h.op x)
  (rN : N.val.obj (op T) →ₗ[A] N.val.obj (op W))
  (hrN : ∀ x, rN x = N.val.restrictₛₗ h.op x)
  (aT : Q.val.obj (op T) →ₗ[A] P.val.obj (op T))
  (bT : P.val.obj (op T) →ₗ[A] N.val.obj (op T))
  (aW : Q.val.obj (op W) →ₗ[B] P.val.obj (op W))
  (bW : P.val.obj (op W) →ₗ[B] N.val.obj (op W))
  (hsqa : ∀ q, rP (aT q) = aW (rQ q)) (hsqb : ∀ p, rN (bT p) = bW (rP p))
  (hbT : Function.Surjective bT) (hbW : Function.Surjective bW)
  (hzero : ∀ q, bT (aT q) = 0) (hexW : ∀ p, bW p = 0 → p ∈ LinearMap.range aW)

include hbasQT hbasQW hrQ in
/-- The relation sheaf of the presentation has its sections over `W` the base change of its
sections over `T`. -/
theorem bijective_liftBaseChange_relations : Function.Bijective (rQ.liftBaseChange B) :=
  bijective_liftBaseChange_of_tautBasis κ h A B basQT basQW hbasQT hbasQW rQ hrQ

include hbasPT hbasPW hrP in
/-- The generator sheaf of the presentation has its sections over `W` the base change of its
sections over `T`. -/
theorem bijective_liftBaseChange_generators : Function.Bijective (rP.liftBaseChange B) :=
  bijective_liftBaseChange_of_tautBasis ι h A B basPT basPW hbasPT hbasPW rP hrP

/-- **The sections of a presented sheaf of modules over a covering object as a base change of
its sections over the base.**  This is Stacks 03DX for one presentation and one morphism: the
four bases reduce the two coproducts of the presentation to base changes, and the exactness of
the sections of the presentation at the two objects transports that to the presented module.  No
cohomology is computed and no flatness of `B` over `A` is used. -/
noncomputable def baseChangeEquivOfPresentationSections :
    B ⊗[A] N.val.obj (op T) ≃ₗ[B] N.val.obj (op W) :=
  Module.BaseChange.baseChangeEquivOfPresentation aT bT aW bW rQ rP rN hsqa hsqb
    (bijective_liftBaseChange_relations κ h A B basQT basQW hbasQT hbasQW rQ hrQ)
    (bijective_liftBaseChange_generators ι h A B basPT basPW hbasPT hbasPW rP hrP)
    hbT hbW hzero hexW

include hrN in
/-- `SheafOfModules.baseChangeEquivOfPresentationSections` carries `1 ⊗ₜ n` to the restriction of
`n` along the covering morphism. -/
theorem baseChangeEquivOfPresentationSections_one_tmul (n : N.val.obj (op T)) :
    baseChangeEquivOfPresentationSections κ ι h A B basQT basQW basPT basPW hbasQT hbasQW
        hbasPT hbasPW rQ hrQ rP hrP rN aT bT aW bW hsqa hsqb hbT hbW hzero hexW
        ((1 : B) ⊗ₜ[A] n) =
      N.val.restrictₛₗ h.op n := by
  rw [baseChangeEquivOfPresentationSections,
    Module.BaseChange.baseChangeEquivOfPresentation_one_tmul, hrN]

include hbasQT hbasQW hbasPT hbasPW hrQ hrP hrN hsqa hsqb hbT hbW hzero hexW in
/-- **The sections of a presented sheaf of modules over a covering object are a base change of
its sections over the base**, in existential form.  This is
`SheafOfModules.baseChangeEquivOfPresentationSections` together with
`SheafOfModules.baseChangeEquivOfPresentationSections_one_tmul`, which is the pair of data
`SheafOfModules.detectsRange_of_baseChangeEquiv` asks of a comparison for the target of a
morphism. -/
theorem exists_baseChangeEquiv_of_presentation :
    ∃ e : B ⊗[A] N.val.obj (op T) ≃ₗ[B] N.val.obj (op W),
      ∀ n, e ((1 : B) ⊗ₜ[A] n) = N.val.restrictₛₗ h.op n :=
  ⟨baseChangeEquivOfPresentationSections κ ι h A B basQT basQW basPT basPW hbasQT hbasQW
      hbasPT hbasPW rQ hrQ rP hrP rN aT bT aW bW hsqa hsqb hbT hbW hzero hexW,
    baseChangeEquivOfPresentationSections_one_tmul κ ι h A B basQT basQW basPT basPW hbasQT
      hbasQW hbasPT hbasPW rQ hrQ rP hrP rN hrN aT bT aW bW hsqa hsqb hbT hbW hzero hexW⟩

include hbasQT hbasQW hbasPT hbasPW hrQ hrP hrN in
/-- **(★) from the sections of the presentation being a presheaf cokernel.**  This is
`SheafOfModules.exists_baseChangeEquiv_of_presentation` with its two commuting squares and its
four exactness hypotheses replaced by what a caller actually has when the sections of `N` are the
cokernel of the sections of `a`: the presenting morphism is surjective on the sections over `T`
and over `W`, it kills the composite with `a` over `T`, and over `W` a section it kills is a
value of `a`.  The two squares are then the naturality of `a` and of `b`, which is no hypothesis
at all.

The three sheaves of modules enter only through their sections and their restriction maps, so the
conditions are statements about one presentation at one object; none of them compares sections at
two different objects. -/
theorem exists_baseChangeEquiv_of_exact_sections (a : Q ⟶ P) (b : P ⟶ N)
    (aT' : Q.val.obj (op T) →ₗ[A] P.val.obj (op T))
    (haT' : ∀ q, aT' q = a.val.app (op T) q)
    (bT' : P.val.obj (op T) →ₗ[A] N.val.obj (op T))
    (hbT' : ∀ p, bT' p = b.val.app (op T) p)
    (aW' : Q.val.obj (op W) →ₗ[B] P.val.obj (op W))
    (haW' : ∀ q, aW' q = a.val.app (op W) q)
    (bW' : P.val.obj (op W) →ₗ[B] N.val.obj (op W))
    (hbW' : ∀ p, bW' p = b.val.app (op W) p)
    (hab : ∀ q, b.val.app (op T) (a.val.app (op T) q) = 0)
    (hsurjT : Function.Surjective (b.val.app (op T)))
    (hsurjW : Function.Surjective (b.val.app (op W)))
    (hkerW : ∀ y, b.val.app (op W) y = 0 → y ∈ LinearMap.range (a.val.app (op W)).hom) :
    ∃ e : B ⊗[A] N.val.obj (op T) ≃ₗ[B] N.val.obj (op W),
      ∀ n, e ((1 : B) ⊗ₜ[A] n) = N.val.restrictₛₗ h.op n := by
  refine exists_baseChangeEquiv_of_presentation κ ι h A B basQT basQW basPT basPW hbasQT hbasQW
    hbasPT hbasPW rQ hrQ rP hrP rN hrN aT' bT' aW' bW' (fun q => ?_) (fun p => ?_)
    (fun n => ?_) (fun n => ?_) (fun q => ?_) (fun p hp => ?_)
  · rw [haT', hrP, haW', hrQ]
    exact (PresheafOfModules.naturality_apply a.val h.op q).symm
  · rw [hbT', hrN, hbW', hrP]
    exact (PresheafOfModules.naturality_apply b.val h.op p).symm
  · simpa [hbT'] using hsurjT n
  · simpa [hbW'] using hsurjW n
  · simpa [hbT', haT'] using hab q
  · simpa [haW'] using hkerW p (by simpa [hbW'] using hp)

variable [Module.FaithfullyFlat A B] (b : P ⟶ N)
  (hbTval : ∀ p, bT p = b.val.app (op T) p) (hbWval : ∀ p, bW p = b.val.app (op W) p)

include hbasQT hbasQW hbasPT hbasPW hrQ hrP hrN hsqa hsqb hbT hbW hzero hexW hbTval hbWval in
/-- **A presenting morphism of a sheaf of modules detects images along a faithfully flat covering
morphism.**  The comparison for the generator sheaf is
`Module.BaseChange.baseChangeEquivOfBasis` on the two bases, the comparison for the presented
module is `SheafOfModules.baseChangeEquivOfPresentationSections`, and the two intertwine the
presenting map with its base change by
`Module.BaseChange.comp_baseChangeEquivOfBasis`; so
`SheafOfModules.detectsRange_of_baseChangeEquiv` applies.

Composed with `SheafOfModules.surjective_val_app_of_epi_of_detectsRange` this makes a presenting
morphism surjective on the sections over a terminal object of the site. -/
theorem detectsRange_of_presentation : DetectsRange b h := by
  have hfP : ∀ i, rP (basPT i) = basPW i := fun i => by
    rw [hbasPT, hrP, restrict_tautGen, hbasPW]
  have heP : ∀ x, Module.BaseChange.baseChangeEquivOfBasis basPT basPW x =
      rP.liftBaseChange B x := fun x => by
    rw [Module.BaseChange.liftBaseChange_eq_of_basis basPT basPW rP hfP]
    rfl
  refine detectsRange_of_baseChangeEquiv b h A B bT hbTval bW hbWval
    (Module.BaseChange.baseChangeEquivOfBasis basPT basPW)
    (baseChangeEquivOfPresentationSections κ ι h A B basQT basQW basPT basPW hbasQT hbasQW
      hbasPT hbasPW rQ hrQ rP hrP rN aT bT aW bW hsqa hsqb hbT hbW hzero hexW)
    (fun x => ?_)
    (baseChangeEquivOfPresentationSections_one_tmul κ ι h A B basQT basQW basPT basPW hbasQT
      hbasQW hbasPT hbasPW rQ hrQ rP hrP rN hrN aT bT aW bW hsqa hsqb hbT hbW hzero hexW)
  exact Module.BaseChange.comp_baseChangeEquivOfBasis aT bT aW bW rQ rP rN hsqb _ heP hsqa
    (bijective_liftBaseChange_relations κ h A B basQT basQW hbasQT hbasQW rQ hrQ)
    (bijective_liftBaseChange_generators ι h A B basPT basPW hbasPT hbasPW rP hrP)
    hbT hbW hzero hexW x

end Presentation

end SheafOfModules

end
