module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Sigma.Basic
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.ExactnessCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeHomotopy
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.Homology.LiftAcyclicComplex

/-!
# Exactness of the relative Čech complex

Let `f : 𝒰 ⥤ 𝒳` be a `1`-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S`, let `τ` be one of the five topologies, and let `𝓕` be an abelian sheaf on `𝒳_τ`.
Assume that the image of `f` covers `𝒳` locally: every object `x` of `𝒳` admits a covering
family `{x_i ⟶ x}` of `𝒳_τ` whose members are isomorphic to objects `f u_i`. Then the extended
relative Čech complex

`0 ⟶ 𝓕 ⟶ f_{0,*}f_0⁻¹𝓕 ⟶ f_{1,*}f_1⁻¹𝓕 ⟶ f_{2,*}f_2⁻¹𝓕 ⟶ ⋯`

is exact in the category of abelian sheaves on `𝒳_τ`. Exactness of that complex is three
separate assertions, one for each kind of spot it has: the augmentation is a monomorphism
(exactness at the initial `𝓕`), the augmentation is the kernel of the first differential
(exactness in degree `0` of the Čech complex), and the Čech complex itself is exact in every
positive degree.

## Main results

* `Stacks.RelativeCech.mono_sheafAugmentation`: exactness at the initial sheaf.
* `Stacks.RelativeCech.exact_sheafAugmentation`: exactness at degree zero.
* `Stacks.RelativeCech.exactAt_sheafComplex_succ`: exactness in every positive degree.

## Implementation notes

A covering family is given as a presieve generating a covering sieve, which is what the source's
`{x_i ⟶ x}` is; its members are only required to be *isomorphic* to objects in the image of `f`,
again as in the source.

Exactness is local, so the whole statement is reduced to the case in which `f` admits a section
up to a vertical `2`-isomorphism, where Stacks 06XA
(`Stacks.RelativeCech.nonempty_homotopy_extendedSheafComplex_id_zero`) contracts the extended
complex outright. The reduction has three ingredients.

* The *slice cover* `Σ u : 𝒰, 𝒳/f u` of `𝒳`, with its projection `Over.forget`, has image the
  same as that of `f` up to isomorphism, and `f` acquires a section over it: over the slice
  `𝒳/f u` the identity of `f u` is lifted by the strong cartesianness of a category fibred in
  groupoids, and `CategoryTheory.Over.post f` is fully faithful there, so the lift is functorial.
  This is `exists_sliceCover_lift`, and `sliceCover_covering` says the slice cover still covers.
* Base change along the slice cover: the relative Čech complex of `f` restricted to the slice
  cover is the relative Čech complex of the projection of the `2`-fibre product, by Stacks 06XC
  (`Stacks.RelativeCech.isIso_baseChangeMap_of_isTwoFibreProduct`). The `2`-fibre product is
  replaced by a small model, since the `2`-fibre-product hypothesis of Stacks 06XC asks for an
  equivalence with the concrete construction; `small_twoFibreProductOver` is the smallness that
  makes that model exist, the base object of a quadruple being determined by its first component.
* Detection of exactness: Stacks 06XD
  (`Stacks.exact_of_exact_inverseImage_of_covering_image`) says a complex of abelian sheaves is
  exact as soon as its restriction along a `1`-morphism with locally covering image is.

Exactness at the initial sheaf is the only one of the three that is not local: it is proved
directly from the universal property of the right Kan extension defining
`Stacks.RelativeCech.term`, the one-element tuple `(f u, 𝟙)` showing that the augmentation is a
split monomorphism on the sections over an object in the image of `f`, and
`hom_ext_of_covering_image` propagating that to all of `𝒳`. It therefore needs none of the
fibred hypotheses, and is stated without them.

`Stacks.RelativeCech.sheafAugmentation_comp_d` is the named cocycle identity making the
augmentation and the first differential a short complex, so the degree-zero statement is about
that short complex rather than about an existentially quantified one.

The `Abelian` instance on `AddCommGrpCat` is taken out of the instance set over the sheafified
material and reinstated by hand inside the proofs, as in
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/Cech/RelativeHomotopy.lean`: it is only needed
there, and leaving it in scope makes the sheafification instances for a coefficient universe of
the form `max …` loop.

## References

* [Stacks Project, Tag 06XE](https://stacks.math.columbia.edu/tag/06XE)
* [Stacks Project, Tag 06XA](https://stacks.math.columbia.edu/tag/06XA)
* [Stacks Project, Tag 06XC](https://stacks.math.columbia.edu/tag/06XC)
* [Stacks Project, Tag 06XD](https://stacks.math.columbia.edu/tag/06XD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.RelativeCech

section CoveringImage

universe uX uU uA vX vU vA

/-- Two maps of presheaves into a sheaf are equal as soon as they agree on the objects in the
image of a functor whose image covers every object locally. -/
private lemma hom_ext_of_covering_image
    {𝒳 : Type uX} [Category.{vX} 𝒳] {𝒰 : Type uU} [Category.{vU} 𝒰]
    {A : Type uA} [Category.{vA} A] (J : GrothendieckTopology 𝒳) (f : 𝒰 ⥤ 𝒳)
    (hcover : ∀ x : 𝒳, ∃ R : Presieve x, Sieve.generate R ∈ J x ∧
      ∀ ⦃y : 𝒳⦄ (g : y ⟶ x), R g → ∃ z : 𝒰, Nonempty (y ≅ f.obj z))
    {P Q : 𝒳ᵒᵖ ⥤ A} (hQ : Presheaf.IsSheaf J Q) (a b : P ⟶ Q)
    (h : ∀ z : 𝒰, a.app (Opposite.op (f.obj z)) = b.app (Opposite.op (f.obj z))) :
    a = b := by
  ext x
  obtain ⟨R, hR, hcov⟩ := hcover x.unop
  apply hQ.hom_ext ⟨Sieve.generate R, hR⟩
  intro I
  obtain ⟨y, g, k, hk, hfac⟩ := I.hf
  rw [← hfac]
  obtain ⟨z, ⟨i⟩⟩ := hcov k hk
  have hy : a.app (Opposite.op y) = b.app (Opposite.op y) := by
    apply (cancel_mono (Q.map i.inv.op)).1
    simp only [← a.naturality, ← b.naturality, h z]
  rw [op_comp, Q.map_comp, ← Category.assoc, ← Category.assoc,
    ← a.naturality k.op, ← b.naturality k.op, hy]

end CoveringImage

section LiftAlongFullyFaithful

universe uD uE uZ vD vE vZ

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {Z : Type uZ} [Category.{vZ} Z]

/-- Lift a functor `G : Z ⥤ E` through a fully faithful `F : D ⥤ E`, given objects `o z` of `D`
and isomorphisms `F (o z) ≅ G z`: on morphisms the lift is the preimage under `F` of the
conjugate of `G k`. -/
private def liftAlongFullyFaithful (F : D ⥤ E) (hF : F.FullyFaithful)
    (G : Z ⥤ E) (o : Z → D) (e : ∀ z, F.obj (o z) ≅ G.obj z) : Z ⥤ D where
  obj := o
  map {z z'} k := hF.preimage ((e z).hom ≫ G.map k ≫ (e z').inv)
  map_id z := by simp
  map_comp k l := by
    rw [← hF.preimage_comp]
    congr 1
    simp

/-- The lift along a fully faithful functor is a lift: composing it with `F` recovers `G`, by the
given isomorphisms. -/
private def liftAlongFullyFaithfulCompIso (F : D ⥤ E) (hF : F.FullyFaithful)
    (G : Z ⥤ E) (o : Z → D) (e : ∀ z, F.obj (o z) ≅ G.obj z) :
    liftAlongFullyFaithful F hF G o e ⋙ F ≅ G :=
  NatIso.ofComponents e (by
    intro z z' k
    change F.map (hF.preimage ((e z).hom ≫ G.map k ≫ (e z').inv)) ≫ (e z').hom =
      (e z).hom ≫ G.map k
    rw [hF.map_preimage]
    simp)

end LiftAlongFullyFaithful

section Slices

universe uC uU uX vC vU vX

variable {C : Type uC} [Category.{vC} C]
  {U : Type uU} [Category.{vU} U] {X : Type uX} [Category.{vX} X]

/-- For a `1`-morphism `f` of categories fibred in groupoids, the slice functor
`CategoryTheory.Over.post f : U/u ⥤ X/f u` is fully faithful: a morphism of `X/f u` has a unique
lift to `U`, by the fill-in property of `p`, and that lift automatically lies over `u`. -/
private def overPostFullyFaithful (p : U ⥤ C) (q : X ⥤ C) (f : U ⥤ X)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hf : f ⋙ q = p) (u : U) : (Over.post (X := u) f).FullyFaithful := by
  subst p
  letI : (Over.post (X := u) f).Full := ⟨by
    intro a b φ
    have hw : q.map φ.left ≫ q.map (f.map b.hom) = q.map (f.map a.hom) := by
      have hw := Over.w φ
      change φ.left ≫ f.map b.hom = f.map a.hom at hw
      exact (q.map_comp _ _).symm.trans (congrArg q.map hw)
    obtain ⟨k, ⟨hk, hka⟩, _⟩ := hp.unique_lift b.hom a.hom (q.map φ.left) hw
    refine ⟨Over.homMk k hka, ?_⟩
    ext1
    apply (hq.unique_lift (f.map b.hom) (f.map a.hom) (q.map φ.left) hw).unique
    · exact ⟨hk, by
        simpa [Over.post, Over.homMk, CostructuredArrow.homMk] using congrArg f.map hka⟩
    · exact ⟨rfl, Over.w φ⟩⟩
  letI : (Over.post (X := u) f).Faithful := ⟨by
    intro a b k l hkl
    ext1
    apply (hp.unique_lift b.hom a.hom ((f ⋙ q).map k.left)
      (by rw [← Functor.map_comp, Over.w k])).unique
    · exact ⟨rfl, Over.w k⟩
    · exact ⟨congrArg q.map (congrArg (fun k => k.left) hkl.symm), Over.w l⟩⟩
  exact .ofFullyFaithful _

/-- Every object of the slice `X/f u` is, up to a vertical isomorphism, the image under
`CategoryTheory.Over.post f` of an object of the slice `U/u`: lift the structure morphism along
`p` and compare the two strongly cartesian lifts of it. -/
private lemma exists_vertical_over_lift (p : U ⥤ C) (q : X ⥤ C) (f : U ⥤ X)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hf : f ⋙ q = p) (u : U) (a : Over (f.obj u)) :
    ∃ b : Over u, ∃ e : (Over.post f).obj b ≅ a,
      q.IsHomLift (𝟙 (q.obj a.left)) e.hom.left := by
  subst p
  obtain ⟨z, k, hk⟩ := hp.exists_lift (q.map a.hom) u rfl
  have hk' : q.IsHomLift (q.map a.hom) (f.map k) :=
    Functor.isHomLift_map_of_comp_eq rfl _ _
  have := hq.isStronglyCartesian_homLift (q.map a.hom) (f.map k)
  have := hq.isStronglyCartesian_homLift (q.map a.hom) a.hom
  let e := Functor.IsCartesian.domainUniqueUpToIso q (q.map a.hom) (f.map k) a.hom
  exact ⟨Over.mk k, Over.isoMk e.symm
    (Functor.IsCartesian.fac q (q.map a.hom) a.hom (f.map k)),
    Functor.IsCartesian.domainUniqueUpToIso_hom_isHomLift q (q.map a.hom) (f.map k) a.hom⟩

/-- A `1`-morphism `f` of categories fibred in groupoids has a section over each slice `X/f u`,
up to a vertical `2`-isomorphism: the objectwise lifts of `exists_vertical_over_lift` assemble
into a functor because `CategoryTheory.Over.post f` is fully faithful. -/
private lemma exists_slice_lift (p : U ⥤ C) (q : X ⥤ C) (f : U ⥤ X)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hf : f ⋙ q = p) (u : U) :
    ∃ s : Over (f.obj u) ⥤ U, ∃ e : s ⋙ f ≅ Over.forget (f.obj u),
      ∀ a, q.IsHomLift (𝟙 (q.obj a.left)) (e.hom.app a) := by
  choose b e he using exists_vertical_over_lift p q f hp hq hf u
  let ff := overPostFullyFaithful p q f hp hq hf u
  let s := liftAlongFullyFaithful (Over.post (X := u) f) ff (𝟭 (Over (f.obj u))) b e
  exact ⟨s ⋙ Over.forget u, Functor.isoWhiskerRight
    (liftAlongFullyFaithfulCompIso (Over.post (X := u) f) ff (𝟭 (Over (f.obj u))) b e)
    (Over.forget (f.obj u)), he⟩

/-- The *slice cover* of `X` attached to `f : U ⥤ X`: the disjoint union over the objects `u` of
`U` of the slice categories `X/f u`. Its projection to `X` has the same image as `f` up to
isomorphism, and `f` acquires a section over it. -/
private abbrev SliceCover (f : U ⥤ X) := Σ u : U, Over (f.obj u)

/-- The projection of the slice cover to `X`, which forgets the structure morphism. -/
private def sliceCoverProjection (f : U ⥤ X) : SliceCover f ⥤ X :=
  CategoryTheory.Sigma.desc (fun u => Over.forget (f.obj u))

/-- The slice cover is a category fibred in groupoids over the base: each slice is, by
`CategoryTheory.Functor.IsFiberedInGroupoids.over_forget` and
`CategoryTheory.Functor.IsFiberedInGroupoids.comp`, and lifts and fill-ins in a disjoint union
are computed summandwise. -/
private lemma sliceCoverProjection_comp_isFiberedInGroupoids (q : X ⥤ C)
    (hq : q.IsFiberedInGroupoids) (f : U ⥤ X) :
    (sliceCoverProjection f ⋙ q).IsFiberedInGroupoids := by
  have hslice : ∀ x : X, (Over.forget x ⋙ q).IsFiberedInGroupoids := fun x =>
    Functor.IsFiberedInGroupoids.comp (Over.forget x) q
      (Functor.IsFiberedInGroupoids.over_forget x) hq
  constructor
  · rintro V W k ⟨u, a⟩ ha
    obtain ⟨b, l, hl⟩ := (hslice (f.obj u)).exists_lift k a ha
    refine ⟨⟨u, b⟩, CategoryTheory.Sigma.SigmaHom.mk l, ?_⟩
    exact IsHomLift.of_fac' _ _ _
      (IsHomLift.domain_eq (Over.forget (f.obj u) ⋙ q) k l)
      (IsHomLift.codomain_eq (Over.forget (f.obj u) ⋙ q) k l)
      (IsHomLift.fac' (Over.forget (f.obj u) ⋙ q) k l)
  · rintro ⟨u, a⟩ ⟨_, b⟩ ⟨_, c⟩ ⟨k⟩ ⟨l⟩ m hm
    obtain ⟨n, hn, hu⟩ := (hslice (f.obj u)).unique_lift k l m hm
    refine ⟨CategoryTheory.Sigma.SigmaHom.mk n,
      ⟨hn.1, congrArg CategoryTheory.Sigma.SigmaHom.mk hn.2⟩, ?_⟩
    rintro ⟨n'⟩ hn'
    congr 1
    exact hu n' ⟨hn'.1, by injection hn'.2⟩

/-- A `1`-morphism `f` of categories fibred in groupoids has a section over its slice cover, up
to a vertical `2`-isomorphism. -/
private lemma exists_sliceCover_lift (p : U ⥤ C) (q : X ⥤ C) (f : U ⥤ X)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hf : f ⋙ q = p) :
    ∃ s : SliceCover f ⥤ U, ∃ e : s ⋙ f ≅ sliceCoverProjection f,
      ∀ a, q.IsHomLift (𝟙 (q.obj ((sliceCoverProjection f).obj a))) (e.hom.app a) := by
  choose s e he using exists_slice_lift p q f hp hq hf
  refine ⟨CategoryTheory.Sigma.desc s,
    NatIso.ofComponents (fun a => (e a.1).app a.2) ?_, ?_⟩
  · rintro ⟨u, a⟩ ⟨_, b⟩ ⟨k⟩
    exact (e u).hom.naturality k
  · rintro ⟨u, a⟩
    exact he u a

/-- If the image of `f` covers every object of `X` locally, so does the image of its slice
cover: a member `y ⟶ x` of a covering family factors through an object isomorphic to some
`f u`, and that factorisation is itself an object of the slice `X/f u`. -/
private lemma sliceCover_covering (J : GrothendieckTopology X) (f : U ⥤ X)
    (hc : ∀ x : X, ∃ R : Presieve x, Sieve.generate R ∈ J x ∧
      ∀ ⦃y : X⦄ (g : y ⟶ x), R g → ∃ z : U, Nonempty (y ≅ f.obj z)) :
    ∀ x : X, ∃ R : Sieve x, R ∈ J x ∧
      ∀ ⦃y : X⦄ (g : y ⟶ x), R g →
        ∃ z : SliceCover f, Nonempty (y ≅ (sliceCoverProjection f).obj z) := by
  intro x
  obtain ⟨R, hR, hcov⟩ := hc x
  refine ⟨Sieve.generate R, hR, ?_⟩
  rintro y g ⟨y', k, l, hl, _⟩
  obtain ⟨z, ⟨i⟩⟩ := hcov l hl
  exact ⟨⟨z, Over.mk (k ≫ i.hom)⟩, ⟨Iso.refl _⟩⟩

end Slices

section Products

universe uC uU uX uY vC vU vX vY

variable {C : Type uC} [Category.{vC} C]
  {U : Type uU} [Category.{vU} U] {X : Type uX} [Category.{vX} X]
  {Y : Type uY} [Category.{vY} Y]

/-- The `2`-fibre product over a base has a small model whose objects live in the universe of the
underlying categorical pullback: the base object of a quadruple is determined by the object of
the first factor. -/
private lemma small_twoFibreProductOver (p𝒳 : U ⥤ C) (p𝒴 : Y ⥤ C) (p𝒮 : X ⥤ C)
    (f : U ⥤ X) (e : Y ⥤ X) :
    Small.{max uU uY vX} (TwoFibreProductOver p𝒳 p𝒴 p𝒮 f e) := by
  apply small_of_injective (f := fun a : TwoFibreProductOver p𝒳 p𝒴 p𝒮 f e =>
    (⟨a.x, a.y, a.iso⟩ : CategoricalPullback f e))
  rintro ⟨b, x, y, hx, hy, i, hi⟩ ⟨b', x', y', hx', hy', i', hi'⟩ h
  cases hx
  cases hx'
  cases h
  rfl

/-- Precomposition with a fully faithful functor surjective on objects preserves being fibred in
groupoids. -/
private lemma isFiberedInGroupoids_comp_of_surjective
    (q : X ⥤ C) (hq : q.IsFiberedInGroupoids)
    (e : Y ⥤ X) [e.Full] [e.Faithful] (he : Function.Surjective e.obj) :
    (e ⋙ q).IsFiberedInGroupoids := by
  constructor
  · intro V W k a ha
    obtain ⟨b, l, hl⟩ := hq.exists_lift k (e.obj a) ha
    obtain ⟨b', rfl⟩ := he b
    refine ⟨b', e.preimage l, ?_⟩
    apply IsHomLift.of_fac' (e ⋙ q) k (e.preimage l) (IsHomLift.domain_eq q k l)
      (IsHomLift.codomain_eq q k l)
    simpa using IsHomLift.fac' q k l
  · intro a b c k l m hm
    obtain ⟨n, ⟨hn, hncomp⟩, hu⟩ := hq.unique_lift (e.map k) (e.map l) m hm
    refine ⟨e.preimage n, ⟨by simpa using hn, ?_⟩, ?_⟩
    · exact e.map_injective (by simpa using hncomp)
    · intro n' hn'
      apply e.map_injective
      rw [e.map_preimage]
      exact hu (e.map n') ⟨hn'.1, by simpa using congrArg e.map hn'.2⟩

/-- Two functors to a category over a base that are `2`-isomorphic by a vertical `2`-isomorphism
have the same composite with the structure functor. -/
private lemma comp_eq_of_vertical_iso (q : X ⥤ C) (h e : Y ⥤ X)
    (α : h ≅ e) (hα : ∀ y, q.IsHomLift (𝟙 (q.obj (e.obj y))) (α.hom.app y)) :
    h ⋙ q = e ⋙ q := by
  let := hα
  have ho y : q.obj (h.obj y) = q.obj (e.obj y) :=
    IsHomLift.domain_eq q (𝟙 (q.obj (e.obj y))) (α.hom.app y)
  refine CategoryTheory.Functor.ext ho fun y y' k => ?_
  have hmap z : q.map (α.hom.app z) = eqToHom (ho z) := by
    simpa using IsHomLift.fac' q (𝟙 (q.obj (e.obj z))) (α.hom.app z)
  have hn := congrArg q.map (α.hom.naturality k)
  simp only [Functor.map_comp, hmap] at hn
  simpa only [Functor.comp_map, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id] using
    congrArg (fun k => k ≫ eqToHom (ho y').symm) hn

end Products

section Homotopy

/-- A cochain complex whose identity is homotopic to zero has exact short complex in every
degree, in the form in which the degrees are spelled out. -/
private lemma exact_sc_of_homotopy_id_zero {A : Type*} [Category A] [Preadditive A]
    [CategoryWithHomology A] {K : CochainComplex A ℕ}
    (H : Homotopy (𝟙 K) 0) (n : ℕ) :
    (ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2))
      (K.d_comp_d _ _ _)).Exact :=
  (HomologicalComplex.exactAt_iff' K n (n + 1) (n + 2)
    (CochainComplex.prev_nat_succ n) (by simp [CochainComplex.next])).mp
    (LiftAcyclic.exactAt_of_homotopy_id_zero H (n + 1))

end Homotopy

section Augmentation

universe u vᵤ vₓ wᵤ wₓ t

variable {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒰 : Type vᵤ} [Category.{wᵤ} 𝒰] {𝒳 : Type vₓ} [Category.{wₓ} 𝒳]

/-- The augmentation of the relative Čech complex of abelian presheaves, as a short complex. -/
private def augmentationShortComplex
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS) (f : 𝒰 ⥤ 𝒳)
    (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max vᵤ vₓ wₓ t}) :
    ShortComplex (𝒳ᵒᵖ ⥤ AddCommGrpCat.{max vᵤ vₓ wₓ t}) :=
  ShortComplex.mk (augmentation.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F 0)
    ((complex.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F).d 0 1)
    (augmentation_comp_d.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F)

end Augmentation

section BaseChangeAugmentation

universe u uU uV uX uY vU vV vX vY w

variable {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒰 : Type uU} [Category.{vU} 𝒰] {𝒳 : Type uX} [Category.{vX} 𝒳]
  {𝒴 : Type uY} [Category.{vY} 𝒴] {𝒱 : Type uV} [Category.{vV} 𝒱]

/-- The base-change comparison of relative Čech complexes carries the augmentation of the source
to the augmentation of the target: both are units of right Kan extensions along the Čech
projections, and the comparison is the one induced on them. -/
private lemma augmentation_comp_baseChangeComponent
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS) (f : 𝒰 ⥤ 𝒳) (e : 𝒴 ⥤ 𝒳)
    (g : 𝒱 ⥤ 𝒴) (h : 𝒱 ⥤ 𝒰) (α : h ⋙ f ≅ g ⋙ e)
    (hα : ∀ v : 𝒱, q.IsHomLift (𝟙 (q.obj (f.obj (h.obj v)))) (α.hom.app v))
    (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX uV uY vY w}) (n : ℕ) :
    Functor.whiskerLeft e.op
        (augmentation.{u, uU, uX, vU, vX, max uV uY vY w} q f F n) ≫
        baseChangeComponent q f e g h α hα F n =
      augmentation.{u, uV, uY, vV, vY, max uU uX vX w} (e ⋙ q) g (e.op ⋙ F) n := by
  let rX := (Tuple.projection q f n).op
  let rY := (Tuple.projection (e ⋙ q) g n).op
  let k := Cech.nerveMap q (e ⋙ q) f g h e α rfl hα n
  have hfac : Functor.whiskerLeft rY (baseChangeComponent q f e g h α hα F n) ≫
      rY.ranCounit.app (rY ⋙ e.op ⋙ F) =
      Functor.whiskerLeft k.op (rX.ranCounit.app (rX ⋙ F)) :=
    ((rY.ranAdjunction
      AddCommGrpCat.{max uU uX vX uV uY vY w}).homEquiv _ _).symm_apply_apply _
  apply (rY.ran.obj (rY ⋙ e.op ⋙ F)).hom_ext_of_isRightKanExtension
    (rY.ranCounit.app (rY ⋙ e.op ⋙ F))
  rw [Functor.whiskerLeft_comp, Category.assoc, hfac]
  apply NatTrans.ext
  funext a
  exact (congr_app ((rX.ranAdjunction _).left_triangle_components F) (k.op.obj a)).trans
    (congr_app ((rY.ranAdjunction _).left_triangle_components (e.op ⋙ F)) a).symm

end BaseChangeAugmentation

section Sheafified

attribute [-instance] AddCommGrpCat.instAbelian

section LocalExactness

universe u uU uX uY vU vX vY w

/-- If `f` has a section over `e` up to a vertical `2`-isomorphism, then the restriction along
`e` of the augmented relative Čech complex of `f` is exact after sheafification: base change
along the `2`-fibre product identifies it with the relative Čech complex of a `1`-morphism with
a section, which Stacks 06XA contracts. -/
private lemma exact_restriction_of_lift
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒰 : Type uU} [Category.{vU} 𝒰] {𝒳 : Type uX} [Category.{vX} 𝒳]
    {𝒴 : Type uY} [Category.{vY} 𝒴]
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS) (f : 𝒰 ⥤ 𝒳) (e : 𝒴 ⥤ 𝒳)
    (hp : (f ⋙ q).IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (he : (e ⋙ q).IsFiberedInGroupoids) (τ : AlgebraicGeometry.SiteKind)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS (e ⋙ q) τ)
      AddCommGrpCat.{max uU uX vX uY vY w}]
    (F : Sheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max uU uX vX uY vY w})
    (s : 𝒴 ⥤ 𝒰) (β : s ⋙ f ≅ e)
    (hβ : ∀ y, q.IsHomLift (𝟙 (q.obj (e.obj y))) (β.hom.app y)) (n : ℕ) :
    (((augmentationShortComplex.{u, uU, uX, vU, vX, max uY vY w} q f F.obj).map
      ((Functor.whiskeringLeft 𝒴ᵒᵖ 𝒳ᵒᵖ _).obj e.op)).map
        (presheafToSheaf
          (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS (e ⋙ q) τ) _)).Exact ∧
    (((presheafToSheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS (e ⋙ q) τ)
      AddCommGrpCat.{max uU uX vX uY vY w}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((((Functor.whiskeringLeft 𝒴ᵒᵖ 𝒳ᵒᵖ
        AddCommGrpCat.{max uU uX vX uY vY w}).obj e.op).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (complex.{vU, vX, _, uU, uX, _, max uY vY w} q f F.obj))).ExactAt (n + 1) := by
  let : Abelian AddCommGrpCat.{max uU uX vX uY vY w} := AddCommGrpCat.instAbelian
  let P := TwoFibreProductOver (f ⋙ q) (e ⋙ q) q f e
  let : Small.{max uU uY vX} P := small_twoFibreProductOver (f ⋙ q) (e ⋙ q) q f e
  let V := Shrink.{max uU uY vX} P
  let E := CategoryTheory.Shrink.equivalence.{max uU uY vX} P
  let d := E.inverse
  let pP := TwoFibreProductOver.structureFunctor (f ⋙ q) (e ⋙ q) q f e
  let g := d ⋙ TwoFibreProductOver.snd (f ⋙ q) (e ⋙ q) q f e
  let h := d ⋙ TwoFibreProductOver.fst (f ⋙ q) (e ⋙ q) q f e
  let α : h ⋙ f ≅ g ⋙ e := Functor.isoWhiskerLeft d
    (TwoFibreProductOver.psiIso (f ⋙ q) (e ⋙ q) q f e)
  have hα : ∀ v, q.IsHomLift (𝟙 (q.obj (f.obj (h.obj v)))) (α.hom.app v) := by
    intro v
    show q.IsHomLift (𝟙 ((f ⋙ q).obj (d.obj v).x)) (d.obj v).iso.hom
    rw [(d.obj v).hx]
    exact (d.obj v).vertical
  have hpP : pP.IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hp he hq rfl rfl
  have hcompg : g ⋙ (e ⋙ q) = d ⋙ pP := by
    dsimp only [g, pP]
    rw [Functor.assoc, TwoFibreProductOver.snd_comp_eq]
  have hcomph : h ⋙ (f ⋙ q) = d ⋙ pP := by
    dsimp only [h, pP]
    rw [Functor.assoc, TwoFibreProductOver.fst_comp_eq]
  have hpV : (g ⋙ e ⋙ q).IsFiberedInGroupoids := by
    rw [hcompg]
    exact isFiberedInGroupoids_comp_of_surjective pP hpP d (equivShrink P).symm.surjective
  have hbase : s ⋙ (f ⋙ q) = e ⋙ q := comp_eq_of_vertical_iso q (s ⋙ f) e β hβ
  let sP : 𝒴 ⥤ P := TwoFibreProductOver.lift (f ⋙ q) (e ⋙ q) q f e
    (e ⋙ q) s (𝟭 𝒴) hbase rfl β hβ
  let o : 𝒴 → V := fun y => equivShrink P (sP.obj y)
  let ι : ∀ y, d.obj (o y) ≅ sP.obj y :=
    fun y => eqToIso ((equivShrink P).symm_apply_apply (sP.obj y))
  let sV := liftAlongFullyFaithful d E.fullyFaithfulInverse sP o ι
  let γ : sV ⋙ g ≅ 𝟭 𝒴 := Functor.isoWhiskerRight
    (liftAlongFullyFaithfulCompIso d E.fullyFaithfulInverse sP o ι)
    (TwoFibreProductOver.snd (f ⋙ q) (e ⋙ q) q f e)
  have hγ : ∀ y, (e ⋙ q).IsHomLift (𝟙 ((e ⋙ q).obj y)) (γ.hom.app y) := by
    intro y
    have hy : d.obj (o y) = sP.obj y := (equivShrink P).symm_apply_apply (sP.obj y)
    have key : (e ⋙ q).IsHomLift (𝟙 ((e ⋙ q).obj y))
        ((TwoFibreProductOver.snd (f ⋙ q) (e ⋙ q) q f e).map (eqToHom hy)) := by
      rw [eqToHom_map]
      exact IsHomLift.eqToHom_codomain_lift_id _ rfl
    exact key
  have hprod : (TwoFibreProductOver.lift (f ⋙ q) (e ⋙ q) q f e
      (d ⋙ pP) h g hcomph hcompg α (by
        intro v
        show q.IsHomLift (𝟙 (d.obj v).base) (d.obj v).iso.hom
        exact (d.obj v).vertical)).IsEquivalence := by
    show d.IsEquivalence
    infer_instance
  have hbc := isIso_baseChangeMap_of_isTwoFibreProduct
    q (f ⋙ q) (e ⋙ q) (d ⋙ pP) f e g h rfl rfl hcompg hcomph α hα
    hq hp he (by rw [← hcompg]; exact hpV) hprod F.obj
  let bc := baseChangeMap q f e g h α hα F.obj
  have : IsIso bc := hbc
  let : q.IsFibered := hq.isFibered
  let : (e ⋙ q).IsFibered := he.isFibered
  let := ((hq.isFibredOneMorphism (F := e) rfl).isContinuous_and_isCocontinuous_inheritedTopology
      ((AlgebraicGeometry.BigFppfSite.baseTopology B τ).over (B.obj hS))).1
  let G := (e.sheafPushforwardContinuous AddCommGrpCat.{max uU uX vX uY vY w}
    (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS (e ⋙ q) τ)
    (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)).obj F
  obtain ⟨H⟩ :=
    nonempty_homotopy_extendedSheafComplex_id_zero.{u, max uU uY vX, uY, _, vY,
      max uU uX vX w} B S hS (e ⋙ q) g τ G sV γ hγ
  let T := presheafToSheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS (e ⋙ q) τ)
    AddCommGrpCat.{max uU uX vX uY vY w}
  let K := sheafComplex.{u, max uU uY vX, uY, _, vY, max uU uX vX w}
    B S hS (e ⋙ q) g τ G
  have hex : K.ExactAt (n + 1) :=
    (HomologicalComplex.exactAt_iff' K n (n + 1) (n + 2)
      (CochainComplex.prev_nat_succ n) (by simp [CochainComplex.next])).2
      (exact_sc_of_homotopy_id_zero H (n + 1))
  let bcIso := (T.mapHomologicalComplex (ComplexShape.up ℕ)).mapIso (asIso bc)
  refine ⟨?_, hex.of_iso bcIso.symm⟩
  apply ShortComplex.exact_of_iso _ (exact_sc_of_homotopy_id_zero H 0)
  apply Iso.symm
  refine ShortComplex.isoMk (Iso.refl _)
    ((HomologicalComplex.eval _ _ 0).mapIso bcIso)
    ((HomologicalComplex.eval _ _ 1).mapIso bcIso) ?_ ?_
  · exact ((Category.id_comp _).trans (congrArg T.map
      (augmentation_comp_baseChangeComponent.{u, uU, max uU uY vX, uX, uY, vU, _, vX, vY, w}
        q f e g h α hα F.obj 0).symm)).trans (T.map_comp _ _)
  · exact ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map bc).comm 0 1

end LocalExactness

section DetectExactness

universe u uX uY vX vY w

/-- Exactness of a complex of abelian presheaves, after sheafification, can be checked after
restriction along a `1`-morphism of categories fibred in groupoids whose image covers locally;
this is Stacks 06XD together with the compatibility of restriction and sheafification. -/
private lemma exact_of_exact_restriction
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type uX} [Category.{vX} 𝒳] {𝒴 : Type uY} [Category.{vY} 𝒴]
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS) (e : 𝒴 ⥤ 𝒳)
    (hq : q.IsFiberedInGroupoids) (he : (e ⋙ q).IsFiberedInGroupoids)
    (τ : AlgebraicGeometry.SiteKind)
    (hc : ∀ x : 𝒳, ∃ R : Sieve x,
      R ∈ AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ x ∧
      ∀ ⦃y : 𝒳⦄ (g : y ⟶ x), R g → ∃ z : 𝒴, Nonempty (y ≅ e.obj z))
    [HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max uX uY vX vY w}]
    [HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS (e ⋙ q) τ)
      AddCommGrpCat.{max uX uY vX vY w}]
    (K : ShortComplex (𝒳ᵒᵖ ⥤ AddCommGrpCat.{max uX uY vX vY w}))
    (hK : ((K.map ((Functor.whiskeringLeft 𝒴ᵒᵖ 𝒳ᵒᵖ _).obj e.op)).map
      (presheafToSheaf
        (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS (e ⋙ q) τ) _)).Exact) :
    (K.map (presheafToSheaf
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ) _)).Exact := by
  let : q.IsFibered := hq.isFibered
  let : (e ⋙ q).IsFibered := he.isFibered
  let hf := hq.isFibredOneMorphism (F := e) rfl
  let := (hf.isContinuous_and_isCocontinuous_inheritedTopology
    ((AlgebraicGeometry.BigFppfSite.baseTopology B τ).over (B.obj hS))).1
  let := (hf.isContinuous_and_isCocontinuous_inheritedTopology
    ((AlgebraicGeometry.BigFppfSite.baseTopology B τ).over (B.obj hS))).2
  let R := e.sheafPushforwardContinuous AddCommGrpCat.{max uX uY vX vY w}
    (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS (e ⋙ q) τ)
    (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
  let : R.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  apply Stacks.exact_of_exact_inverseImage_of_covering_image
    B S hS (e ⋙ q) q e he hq hf τ hc
  exact ShortComplex.exact_of_iso (K.mapNatIso
    (e.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{max uX uY vX vY w}
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS (e ⋙ q) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ))) hK

end DetectExactness

universe u vᵤ vₓ wᵤ wₓ t

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 : Type vᵤ} [Category.{wᵤ} 𝒰] {𝒳 : Type vₓ} [Category.{wₓ} 𝒳]
  (p : 𝒰 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (f : 𝒰 ⥤ 𝒳) (τ : AlgebraicGeometry.SiteKind)

/-- **Stacks 06XE.** Exactness of the extended relative Čech complex at its initial term: if the
image of `f` covers every object of `𝒳` locally, the augmentation of an abelian sheaf into degree
`0` of its sheafified relative Čech complex is a monomorphism. -/
@[stacks 06XE "exactness at the initial sheaf"]
public theorem mono_sheafAugmentation
    (hcover : ∀ x : 𝒳, ∃ R : Presieve x,
      Sieve.generate R ∈ AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ x ∧
        ∀ ⦃y : 𝒳⦄ (g : y ⟶ x), R g → ∃ z : 𝒰, Nonempty (y ≅ f.obj z))
    [HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ t}]
    (𝓕 : Sheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ t}) :
    Mono (sheafAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, t} B S hS q f τ 𝓕) := by
  let r := Tuple.projection q f 0
  let adj := r.op.ranAdjunction AddCommGrpCat.{max vᵤ vₓ wₓ t}
  have hunit : Mono (adj.unit.app 𝓕.obj) := by
    constructor
    intro P a b hab
    apply hom_ext_of_covering_image _ f hcover 𝓕.property a b
    intro z
    let c : Tuple q f 0 :=
      ⟨f.obj z, fun _ => z, fun _ => Iso.refl _, fun _ => by dsimp; infer_instance⟩
    have ht := congr_app (adj.left_triangle_components 𝓕.obj) (Opposite.op c)
    have he := congrArg (fun k => k.app (Opposite.op (f.obj z)) ≫
      (adj.counit.app (r.op ⋙ 𝓕.obj)).app (Opposite.op c)) hab
    change (adj.unit.app 𝓕.obj).app (Opposite.op (f.obj z)) ≫
      (adj.counit.app (r.op ⋙ 𝓕.obj)).app (Opposite.op c) = 𝟙 _ at ht
    dsimp only [NatTrans.comp_app] at he
    simpa only [Category.assoc, ht, Category.comp_id] using he
  show Mono ((sheafificationIso 𝓕).hom ≫
    (presheafToSheaf _ _).map (adj.unit.app 𝓕.obj))
  infer_instance

/-- Over the slice cover, the sheafified augmented relative Čech complex of `f` is exact, in the
form needed for the degree-zero and the positive-degree statements. -/
private lemma exact_map_presheafToSheaf_of_slice_cover
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hf : p.IsFibredOneMorphism q f)
    (hcover : ∀ x : 𝒳, ∃ R : Presieve x,
      Sieve.generate R ∈ AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ x ∧
        ∀ ⦃y : 𝒳⦄ (g : y ⟶ x), R g → ∃ z : 𝒰, Nonempty (y ≅ f.obj z))
    [HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ t}]
    (𝓕 : Sheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ t}) (n : ℕ) :
    ((augmentationShortComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f 𝓕.obj).map
      (presheafToSheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ) _)).Exact ∧
    (((complex.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f 𝓕.obj).sc (n + 1)).map
      (presheafToSheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ) _)).Exact := by
  let : Abelian AddCommGrpCat.{max vᵤ vₓ wₓ t} := AddCommGrpCat.instAbelian
  let e := sliceCoverProjection f
  have he : (e ⋙ q).IsFiberedInGroupoids :=
    sliceCoverProjection_comp_isFiberedInGroupoids q hq f
  have hp' : (f ⋙ q).IsFiberedInGroupoids := by rwa [hf.comp_eq]
  let : HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS (e ⋙ q) τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ t} :=
    CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat.{max vᵤ vₓ wₓ t, _, _} _
  obtain ⟨s, β, hβ⟩ := exists_sliceCover_lift p q f hp hq hf.comp_eq
  have hex := exact_restriction_of_lift.{u, vᵤ, vₓ, max vᵤ vₓ wₓ, wᵤ, wₓ, max vᵤ vₓ wₓ, t}
    B S hS q f e hp' hq he τ 𝓕 s β hβ n
  have hglobal := exact_of_exact_restriction.{u, vₓ, max vᵤ vₓ wₓ, wₓ, max vᵤ vₓ wₓ, t}
    B S hS q e hq he τ (sliceCover_covering _ f hcover)
  refine ⟨hglobal _ hex.1, ?_⟩
  rw [HomologicalComplex.exactAt_iff] at hex
  exact hglobal _ hex.2

/-- **Stacks 06XE.** Exactness of the extended relative Čech complex in degree zero: if `f` is a
`1`-morphism of categories fibred in groupoids whose image covers every object of `𝒳` locally,
the augmentation of an abelian sheaf is the kernel of the first differential of its sheafified
relative Čech complex. -/
@[stacks 06XE "exactness at degree zero"]
public theorem exact_sheafAugmentation
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hf : p.IsFibredOneMorphism q f)
    (hcover : ∀ x : 𝒳, ∃ R : Presieve x,
      Sieve.generate R ∈ AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ x ∧
        ∀ ⦃y : 𝒳⦄ (g : y ⟶ x), R g → ∃ z : 𝒰, Nonempty (y ≅ f.obj z))
    [HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ t}]
    (𝓕 : Sheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ t}) :
    (ShortComplex.mk (sheafAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, t} B S hS q f τ 𝓕)
      ((sheafComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} B S hS q f τ 𝓕).d 0 1)
      (sheafAugmentation_comp_d.{u, vᵤ, vₓ, wᵤ, wₓ, t} B S hS q f τ 𝓕)).Exact := by
  have hglobal := (exact_map_presheafToSheaf_of_slice_cover.{u, vᵤ, vₓ, wᵤ, wₓ, t}
    B S hS p q f τ hp hq hf hcover 𝓕 0).1
  apply ShortComplex.exact_of_iso _ hglobal
  apply Iso.symm
  exact ShortComplex.isoMk (sheafificationIso 𝓕) (Iso.refl _) (Iso.refl _)
    (Category.comp_id _).symm ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- **Stacks 06XE.** Exactness of the extended relative Čech complex in every positive degree: if
`f` is a `1`-morphism of categories fibred in groupoids whose image covers every object of `𝒳`
locally, the sheafified relative Čech complex of an abelian sheaf is exact in every positive
degree. -/
@[stacks 06XE "exactness in positive degrees"]
public theorem exactAt_sheafComplex_succ
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (hf : p.IsFibredOneMorphism q f)
    (hcover : ∀ x : 𝒳, ∃ R : Presieve x,
      Sieve.generate R ∈ AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ x ∧
        ∀ ⦃y : 𝒳⦄ (g : y ⟶ x), R g → ∃ z : 𝒰, Nonempty (y ≅ f.obj z))
    [HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ t}]
    (𝓕 : Sheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ t}) (n : ℕ) :
    (sheafComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} B S hS q f τ 𝓕).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff]
  exact (exact_map_presheafToSheaf_of_slice_cover.{u, vᵤ, vₓ, wᵤ, wₓ, t}
    B S hS p q f τ hp hq hf hcover 𝓕 n).2

end Sheafified

end Stacks.RelativeCech

end
