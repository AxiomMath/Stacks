module

public import StacksFrontier.AlgebraicGeometry.ProEtale.CompactGeneration
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.SiteAxioms
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.SmallAffine
public import StacksCore.Tactic.StacksAttribute

/-!
# Enough quasi-compact weakly contractible objects in the pro-étale sites of a scheme

Stacks 0990 asserts that each of the pro-étale sites of a scheme `S` has enough affine
quasi-compact weakly contractible objects. This file proves it for the big pro-étale site
`(Sch/S)_proétale`, the small pro-étale site `S_proétale`, the big affine pro-étale site
`(Aff/S)_proétale` and the affine small pro-étale site `S_{affine, proétale}`; the affine
ind-étale site `S_app` is
`AlgebraicGeometry.ProEtale.affineIndEtaleProetale_hasEnough_quasiCompact_weaklyContractible`.

In each case the covering objects are the affine ones whose ring of global sections is
w-contractible: they cover by Stacks 098I, and each of them is a quasi-compact object of the
site and a weakly contractible one, both by the finite disjoint clopen refinements of
Stacks 098H. On `(Aff/S)_proétale` and on `S_{affine, proétale}`, whose standard covering
families are finite by definition, quasi-compactness of *every* object is already formal.

## Main results

* `AlgebraicGeometry.ProEtale.exists_ofArrows_affine_wContractible`: Stacks 098I in a chosen big
  pro-étale site, with the covering family indexed by the morphism universe of the site.
* `AlgebraicGeometry.ProEtale.BigProetaleOver.hasEnough_affine_quasiCompact_weaklyContractible`:
  Stacks 0990 for `(Sch/S)_proétale`.
* `AlgebraicGeometry.ProEtale.SmallProetale.hasEnough_affine_quasiCompact_weaklyContractible`:
  Stacks 0990 for `S_proétale`.
* `AlgebraicGeometry.ProEtale.BigAffineProetale.hasEnough_affine_quasiCompact_weaklyContractible`:
  Stacks 0990 for `(Aff/S)_proétale`, with
  `AlgebraicGeometry.ProEtale.BigAffineProetale.isQuasiCompactObject` and
  `AlgebraicGeometry.ProEtale.BigAffineProetale.isWeaklyContractible_of_isWContractible` as its
  two inputs.
* `AlgebraicGeometry.ProEtale.SmallAffineProetale.hasEnough_affine_quasiCompact_weaklyContractible`:
  Stacks 0990 for `S_{affine, proétale}`, with
  `AlgebraicGeometry.ProEtale.SmallAffineProetale.isWeaklyContractible_of_isWContractible` and
  `AlgebraicGeometry.ProEtale.SmallAffineProetale.hasEnoughObjects_isWContractible` as its two
  inputs.

## Implementation notes

`CategoryTheory.GrothendieckTopology.HasEnoughObjects` asks for a covering family indexed by the
*morphism* universe `u` of the site, whereas the chosen covering families of a big pro-étale
site are indexed one universe higher. The covering of Stacks 098I is therefore rebuilt here from
the chosen affine open cover of the underlying scheme, whose index type is the underlying
topological space and so lies in `Type u`, refined by the single w-contractible cover of each of
its members. Membership in the chosen covering system costs nothing extra, by
`AlgebraicGeometry.ProEtale.BigProetaleSite.precoverage_eq_comap`.

## References

* [Stacks Project, Tag 0990](https://stacks.math.columbia.edu/tag/0990)
* [Stacks Project, Tag 098I](https://stacks.math.columbia.edu/tag/098I)
* [Stacks Project, Tag 090L](https://stacks.math.columbia.edu/tag/090L)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ProetaleWContractible

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u})

/-- A member of the chosen affine open cover of the underlying scheme of an object `T` of a
chosen big pro-étale site, as an object of that site: it is the source of an open immersion into
an object of the site, hence satisfies the size cutoff. -/
private def affineOpen (T : B.Scheme) (i : T.obj.affineCover.I₀) : B.Scheme :=
  ⟨T.obj.affineCover.X i,
    Scheme.size_lt_of_isOpenImmersion (T.obj.affineCover.f i) T.property⟩

private instance (T : B.Scheme) (i : T.obj.affineCover.I₀) : IsAffine (affineOpen B T i).obj :=
  inferInstanceAs (IsAffine (T.obj.affineCover.X i))

/-- The open immersion of a member of the chosen affine open cover of the underlying scheme of
`T` into `T`, as a morphism of the chosen big pro-étale site. -/
private def affineOpenHom (T : B.Scheme) (i : T.obj.affineCover.I₀) : affineOpen B T i ⟶ T :=
  ObjectProperty.homMk (T.obj.affineCover.f i)

/-- **Stacks 098I, with a covering family indexed by the morphism universe of the site.** Every
object `T` of a chosen big pro-étale site admits a covering family `{T_i → T}` indexed by a type
in `Type u` with each `T_i` affine and the spectrum of a w-contractible ring.

The family is the chosen affine open cover of the underlying scheme of `T`, whose index type is
the underlying topological space, refined by the single affine w-contractible cover of each of
its members. -/
theorem exists_ofArrows_affine_wContractible (T : B.Scheme) :
    ∃ (I : Type u) (V : I → B.Scheme) (p : (i : I) → V i ⟶ T),
      Sieve.ofArrows V p ∈ B.topology T ∧
        ∀ i, IsAffine (V i).obj ∧ IsWContractible.{u, u} Γ((V i).obj, ⊤) := by
  classical
  have hA : Sieve.ofArrows (affineOpen B T) (affineOpenHom B T) ∈ B.topology T := by
    refine Precoverage.generate_mem_toGrothendieck ?_
    rw [B.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    exact zariskiPrecoverage_le_proetalePrecoverage _ T.obj.affineCover.mem₀
  have hstep (i : T.obj.affineCover.I₀) :
      ∃ (W : B.Scheme) (w : W ⟶ affineOpen B T i),
        Sieve.generate (Presieve.singleton w) ∈ B.topology (affineOpen B T i) ∧
          IsAffine W.obj ∧ IsWContractible.{u, u} Γ(W.obj, ⊤) := by
    obtain ⟨W, g, hcov, haff, hwc, -, -⟩ :=
      exists_affine_indEtale_wContractible_cover B (affineOpen B T i)
    refine ⟨W, g, ?_, haff, hwc⟩
    have h := Precoverage.generate_mem_toGrothendieck (J := B.precoverage)
      ((B.mem_precoverage_iff (X := affineOpen B T i)
        (PreZeroHypercover.singleton g).presieve₀).mpr
        ⟨PreZeroHypercover.singleton g, rfl, hcov⟩)
    rwa [PreZeroHypercover.presieve₀_singleton] at h
  choose W w hWcov hWprop using hstep
  refine ⟨T.obj.affineCover.I₀, W, fun i ↦ w i ≫ affineOpenHom B T i, ?_, hWprop⟩
  refine B.topology.transitive hA _ ?_
  rintro Y b ⟨Y', c, d, ⟨i⟩, hcd⟩
  refine B.topology.superset_covering ?_ (B.topology.pullback_stable c (hWcov i))
  rintro Z e ⟨Z', e₁, e₂, ⟨⟩, he₁⟩
  exact ⟨_, e₁, w i ≫ affineOpenHom B T i, ⟨i⟩, by
    rw [← hcd, ← Category.assoc, he₁, Category.assoc]⟩

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0990 for the big pro-étale site `(Sch/S)_proétale`.** Every object of the big
pro-étale site of `S` is covered by objects which are affine, quasi-compact objects of the site
and weakly contractible in it.

The covering is Stacks 098I, lifted to the slice by composing with the structure morphism; the
two properties of its members are
`AlgebraicGeometry.ProEtale.BigProetaleOver.isQuasiCompactObject_of_isWContractible` and
`AlgebraicGeometry.ProEtale.BigProetaleOver.isWeaklyContractible_of_isWContractible`. -/
@[stacks 0990 "the big pro-étale site (Sch/S)_proétale"]
theorem BigProetaleOver.hasEnough_affine_quasiCompact_weaklyContractible :
    (BigProetaleOver.topology B S hS).HasEnoughObjects
      (fun T : BigProetaleOver B S hS ↦
        IsAffine ((BigProetaleOver.toScheme B S hS).obj T) ∧
          (BigProetaleOver.topology B S hS).IsQuasiCompactObject T ∧
          (BigProetaleOver.topology B S hS).IsWeaklyContractible T) := by
  intro T
  obtain ⟨I, V, p, hcov, hV⟩ := exists_ofArrows_affine_wContractible B T.left
  refine ⟨I, fun i ↦ Over.mk (p i ≫ T.hom), fun i ↦ Over.homMk (p i), ?_, fun i ↦ ?_⟩
  · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact hcov
  · exact ⟨(hV i).1,
      BigProetaleOver.isQuasiCompactObject_of_isWContractible B S hS _ (hV i).1 (hV i).2,
      BigProetaleOver.isWeaklyContractible_of_isWContractible B S hS _ (hV i).1 (hV i).2⟩

/-- **Stacks 0990 for the small pro-étale site `S_proétale`.** Every object of the small
pro-étale site of `S` is covered by objects which are affine, quasi-compact objects of the site
and weakly contractible in it.

The covering is Stacks 098I in the small site,
`AlgebraicGeometry.ProEtale.SmallProetale.hasEnoughObjects_isWContractible`; the two properties
of its members are
`AlgebraicGeometry.ProEtale.SmallProetale.isQuasiCompactObject_of_isWContractible` and
`AlgebraicGeometry.ProEtale.SmallProetale.isWeaklyContractible_of_isWContractible`. -/
@[stacks 0990 "the small pro-étale site S_proétale"]
theorem SmallProetale.hasEnough_affine_quasiCompact_weaklyContractible :
    (SmallProetale.topology B S hS).HasEnoughObjects
      (fun U : SmallProetale B S hS ↦
        IsAffine ((SmallProetale.toScheme B S hS).obj U) ∧
          (SmallProetale.topology B S hS).IsQuasiCompactObject U ∧
          (SmallProetale.topology B S hS).IsWeaklyContractible U) := by
  intro U
  obtain ⟨I, V, p, hcov, hV⟩ :=
    SmallProetale.hasEnoughObjects_isWContractible B ⟨S, hS⟩ U
  exact ⟨I, V, p, hcov, fun i ↦ ⟨(hV i).1,
    SmallProetale.isQuasiCompactObject_of_isWContractible B S hS _ (hV i).1 (hV i).2,
    SmallProetale.isWeaklyContractible_of_isWContractible B S hS _ (hV i).1 (hV i).2⟩⟩

/-- The empty sieve covers an object whose underlying scheme is empty, for a precoverage
containing the finite families that map to chosen big pro-étale coverings. -/
private theorem bot_mem_toGrothendieck_of_isEmpty
    [MorphismProperty.ContainsIdentities (@WeaklyEtale : MorphismProperty Scheme.{u})]
    {C : Type*} [Category C] (Pc : Precoverage C) (Q : C ⥤ B.Scheme)
    (hPc : ∀ {Z : C} (E : PreZeroHypercover.{u + 1} Z), B.covering ⟨Q.obj Z, E.map Q⟩ →
      Finite E.I₀ → E.presieve₀ ∈ Pc Z)
    (Z : C) (hZ : IsEmpty (B.inclusion.obj (Q.obj Z)).carrier) :
    (⊥ : Sieve Z) ∈ Pc.toGrothendieck Z := by
  let E : PreZeroHypercover.{u + 1} Z :=
    ⟨ULift.{u + 1} Empty, fun i ↦ i.down.elim, fun i ↦ i.down.elim⟩
  have hE : B.covering ⟨Q.obj Z, E.map Q⟩ := by
    refine ⟨?_, ?_⟩
    · change ((E.map Q).map B.inclusion).presieve₀ ∈ _
      apply Scheme.zariskiPrecoverage_le_propQCPrecoverage
      rw [Scheme.zariskiPrecoverage, Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x ↦ (hZ.false x).elim, fun i ↦ i.down.elim⟩
    · simp only [E, PreZeroHypercover.map_I₀, Cardinal.mk_eq_zero, zero_le]
  have heq : E.sieve₀ = ⊥ :=
    (congrArg Sieve.generate (Presieve.ofArrows_of_isEmpty E.f)).trans Sieve.generate_bot
  rw [← heq]
  exact Precoverage.generate_mem_toGrothendieck (hPc E hE inferInstance)

/-- The pushforward of a sieve containing a chosen big pro-étale covering family, along a
functor to the chosen big site, is a covering sieve there. -/
private theorem functorPushforward_mem_topology {C : Type*} [Category C] (Q : C ⥤ B.Scheme)
    {U : C} {T : Sieve U} {E : PreZeroHypercover.{u + 1} U} (hE : B.covering ⟨Q.obj U, E.map Q⟩)
    (hET : E.presieve₀ ≤ T) : T.functorPushforward Q ∈ B.topology (Q.obj U) := by
  refine B.topology.superset_covering (Sieve.functorPushforward_monotone Q U
    ((Sieve.generate_le_iff _ _).mpr hET)) ?_
  rw [← PreZeroHypercover.sieve₀_map]
  exact Precoverage.generate_mem_toGrothendieck ⟨E.map Q, rfl, hE⟩

/-- The members of a clopen decomposition cover of an affine scheme are affine. -/
private theorem isAffine_of_isClopenDecompositionCover {T : B.Scheme} (hT : IsAffine T.obj)
    {n : ℕ} {V : Fin n → B.Scheme} {g : (i : Fin n) → V i ⟶ T}
    (hdec : IsClopenDecompositionCover (fun i ↦ (V i).obj) (fun i ↦ B.inclusion.map (g i)))
    (i : Fin n) : IsAffine (V i).obj := by
  have h₁ : IsAffine (B.inclusion.obj T) := hT
  have h₂ : IsOpenImmersion (B.inclusion.map (g i)) := hdec.openImmersion i
  have h₃ : IsClosedImmersion (B.inclusion.map (g i)) :=
    IsClosedImmersion.of_isPreimmersion _ (hdec.clopen i).isClosed
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine (B.inclusion.map (g i))).1

/-- A finite family of morphisms to `U` whose images in schemes form a clopen decomposition cover
generates a covering sieve, for a precoverage containing the finite families that map to chosen
big pro-étale coverings. -/
private theorem ofArrows_mem_toGrothendieck_of_isClopenDecompositionCover
    [MorphismProperty.ContainsIdentities (@WeaklyEtale : MorphismProperty Scheme.{u})]
    {C : Type*} [Category C] (Pc : Precoverage C) (Q : C ⥤ B.Scheme)
    (hPc : ∀ {Z : C} (E : PreZeroHypercover.{u + 1} Z), B.covering ⟨Q.obj Z, E.map Q⟩ →
      Finite E.I₀ → E.presieve₀ ∈ Pc Z)
    {U : C} {n : ℕ} (X : Fin n → C) (f : (i : Fin n) → X i ⟶ U)
    (hdec : IsClopenDecompositionCover (fun i ↦ (Q.obj (X i)).obj)
      (fun i ↦ B.inclusion.map (Q.map (f i)))) :
    Sieve.ofArrows X f ∈ Pc.toGrothendieck U := by
  let F : PreZeroHypercover.{u + 1} U :=
    ⟨ULift.{u + 1} (Fin n), fun i ↦ X i.down, fun i ↦ f i.down⟩
  have hF : B.IsProetaleCovering ⟨Q.obj U, F.map Q⟩ := by
    change ((F.map Q).map B.inclusion).presieve₀ ∈ _
    apply Scheme.zariskiPrecoverage_le_propQCPrecoverage
    rw [Scheme.zariskiPrecoverage, Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ hdec.openImmersion i.down⟩
    have hx : x ∈ ⋃ i, Set.range (B.inclusion.map (Q.map (f i))).base :=
      (Set.ext_iff.mp hdec.cover x).mpr (Set.mem_univ x)
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hx
    exact ⟨ULift.up i, y, hy⟩
  have hFQfin : Finite (F.map Q).I₀ := inferInstanceAs (Finite (ULift.{u + 1} (Fin n)))
  obtain ⟨ι, hfin, a, ha, -⟩ := B.exists_finite_restrictIndex_covering (F.map Q) hF
  have hFtop : F.sieve₀ ∈ Pc.toGrothendieck U :=
    Pc.toGrothendieck.superset_covering (Sieve.generate_mono (F.presieve₀_restrictIndex_le a))
      (Precoverage.generate_mem_toGrothendieck (hPc (F.restrictIndex a) ha hfin))
  refine Pc.toGrothendieck.superset_covering (fun Y b hb ↦ ?_) hFtop
  obtain ⟨i, c, hc⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hb
  exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨i.down, c, hc⟩

namespace BigAffineProetale

/-- **Stacks 090H for the big affine pro-étale site `(Aff/S)_proétale`:** every one of its
objects is quasi-compact, its standard covering families being finite by definition. -/
theorem isQuasiCompactObject (X : BigAffineProetale B S hS) :
    (BigAffineProetale.topology B S hS).IsQuasiCompactObject X :=
  GrothendieckTopology.isQuasiCompactObject_of_isSite _ (BigAffineProetale.isSite B S hS)
    (fun _ h ↦ h.2) _ (fun _ _ ↦ Iff.rfl) X

/-- An object of the big affine pro-étale site whose ring of global sections is w-contractible is
a weakly contractible object of that site.

Every covering sieve of the object pushes forward to a covering sieve of the underlying scheme in
the chosen big site, where w-contractibility refines it by a finite disjoint clopen Zariski
cover. The members of that cover are clopen subschemes of an affine scheme, hence affine, so they
are again objects of the big affine pro-étale site and refine the original sieve. -/
theorem isWeaklyContractible_of_isWContractible (U : BigAffineProetale B S hS)
    (hW : IsWContractible.{u, u} Γ((BigAffineProetale.toScheme B S hS).obj U, ⊤)) :
    (BigAffineProetale.topology B S hS).IsWeaklyContractible U := by
  classical
  let I := BigAffineProetale.inclusion B S hS
  let q := BigProetaleOver.forget B S hS
  let Q := I ⋙ q
  let J := BigAffineProetale.topology B S hS
  have hUaff : IsAffine U.obj.left.obj := U.property
  let _ : MorphismProperty.ContainsIdentities @WeaklyEtale := ⟨fun _ ↦ inferInstance⟩
  apply GrothendieckTopology.isWeaklyContractible_of_clopenRefinements J (Q ⋙ B.inclusion) U
  · exact bot_mem_toGrothendieck_of_isEmpty B (BigAffineProetale.precoverage B S hS) Q
      (fun E hE hfin ↦ ⟨E, rfl, hE, hfin⟩)
  · intro X Y f hf
    exact I.mono_of_mono_map (q.mono_of_mono_map (B.inclusion.mono_of_mono_map hf))
  · intro T hT
    obtain ⟨E, hE, hET⟩ := exists_covering_le_of_isSite (BigAffineProetale.IsCovering B S hS)
      (BigAffineProetale.isSite B S hS) (BigAffineProetale.precoverage B S hS)
      (fun _ _ ↦ Iff.rfl) T hT
    have hT' := functorPushforward_mem_topology B Q hE.1 hET
    obtain ⟨n, V, g, hdec, href⟩ :=
      exists_clopenRefinement_of_isWContractible B U.obj.left hW _ hT'
    have hVaffine := isAffine_of_isClopenDecompositionCover B hUaff hdec
    let X (i : Fin n) : BigAffineProetale B S hS :=
      ⟨Over.mk (g i ≫ U.obj.hom), hVaffine i⟩
    let f (i : Fin n) : X i ⟶ U := ObjectProperty.homMk (Over.homMk (g i))
    have hQf (i : Fin n) : Q.map (f i) = g i := rfl
    have hcover := ofArrows_mem_toGrothendieck_of_isClopenDecompositionCover B
      (BigAffineProetale.precoverage B S hS) Q (fun E hE hfin ↦ ⟨E, rfl, hE, hfin⟩) X f hdec
    refine ⟨n, X, f, ?_, hcover, fun i ↦ ?_⟩
    · exact hdec
    · obtain ⟨Z, c₁, c₂, hc₁, hc₂⟩ := href i
      let c : X i ⟶ Z := ObjectProperty.homMk (Over.homMk c₂ (by
        have hw : Q.map c₁ ≫ U.obj.hom = Z.obj.hom := Over.w (I.map c₁)
        show c₂ ≫ Z.obj.hom = g i ≫ U.obj.hom
        rw [← hw, ← Category.assoc, ← hc₂]))
      have hc : c ≫ c₁ = f i := by
        refine I.map_injective (q.map_injective ?_)
        show Q.map c ≫ Q.map c₁ = Q.map (f i)
        rw [hQf, show Q.map c = c₂ from rfl]
        exact hc₂.symm
      rw [← hc]
      exact T.downward_closed hc₁ c

/-- **Stacks 098I in the big affine pro-étale site `(Aff/S)_proétale`.** Every object of that
site is covered by a single affine object with w-contractible ring of global sections.

The cover is the single affine ind-étale w-contractible cover of the underlying scheme of the
object, which is affine; the covering family has one member and so meets the finiteness
requirement on a standard pro-étale covering. -/
theorem hasEnoughObjects_isAffine_isWContractible (U : BigAffineProetale B S hS) :
    ∃ (V : BigAffineProetale B S hS) (p : V ⟶ U),
      Sieve.ofArrows (fun _ : PUnit.{u + 1} ↦ V) (fun _ ↦ p) ∈
          BigAffineProetale.topology B S hS U ∧
        IsWContractible.{u, u} Γ((BigAffineProetale.toScheme B S hS).obj V, ⊤) := by
  classical
  have hUaff : IsAffine U.obj.left.obj := U.property
  have hUaff' : IsAffine (B.inclusion.obj U.obj.left) := U.property
  obtain ⟨W, g, hcov, haff, hwc, -, -⟩ :=
    exists_affine_indEtale_wContractible_cover B U.obj.left
  let V : BigAffineProetale B S hS := ⟨Over.mk (g ≫ U.obj.hom), haff⟩
  let p : V ⟶ U := ObjectProperty.homMk (Over.homMk g)
  exact ⟨V, p, Precoverage.generate_mem_toGrothendieck ⟨PreZeroHypercover.singleton p,
    (Presieve.ofArrows_pUnit p).trans (PreZeroHypercover.presieve₀_singleton p).symm,
    hcov, inferInstance⟩, hwc⟩

end BigAffineProetale

/-- **Stacks 0990 for the big affine pro-étale site `(Aff/S)_proétale`.** Every object of the
big affine pro-étale site of `S` is covered by objects which are affine, quasi-compact objects
of the site and weakly contractible in it. -/
@[stacks 0990 "the big affine pro-étale site (Aff/S)_proétale"]
theorem BigAffineProetale.hasEnough_affine_quasiCompact_weaklyContractible :
    (BigAffineProetale.topology B S hS).HasEnoughObjects
      (fun U : BigAffineProetale B S hS ↦
        IsAffine ((BigAffineProetale.toScheme B S hS).obj U) ∧
          (BigAffineProetale.topology B S hS).IsQuasiCompactObject U ∧
          (BigAffineProetale.topology B S hS).IsWeaklyContractible U) := by
  intro U
  obtain ⟨V, p, hcov, hwc⟩ :=
    BigAffineProetale.hasEnoughObjects_isAffine_isWContractible B S hS U
  exact ⟨PUnit.{u + 1}, fun _ ↦ V, fun _ ↦ p, hcov, fun _ ↦
    ⟨V.property, BigAffineProetale.isQuasiCompactObject B S hS V,
      BigAffineProetale.isWeaklyContractible_of_isWContractible B S hS V hwc⟩⟩

namespace SmallAffineProetale

/-- An object of the affine small pro-étale site whose ring of global sections is w-contractible
is a weakly contractible object of that site.

Every covering sieve of the object pushes forward to a covering sieve of the underlying scheme
in the chosen big site, where w-contractibility refines it by a finite disjoint clopen Zariski
cover. The members of that cover are affine open subschemes of the object, hence weakly étale
over `S`, so they are again objects of the affine small pro-étale site refining the original
sieve. -/
theorem isWeaklyContractible_of_isWContractible (U : SmallAffineProetale B S hS)
    (hW : IsWContractible.{u, u} Γ(U.obj.obj.left.obj, ⊤)) :
    (SmallAffineProetale.topology B S hS).IsWeaklyContractible U := by
  classical
  let I := SmallAffineProetale.inclusion B S hS ⋙ SmallProetale.inclusion B S hS
  let q := BigProetaleOver.forget B S hS
  let Q := I ⋙ q
  let J := SmallAffineProetale.topology B S hS
  have hUaff : IsAffine U.obj.obj.left.obj := U.property
  let _ : MorphismProperty.ContainsIdentities @WeaklyEtale := ⟨fun _ ↦ inferInstance⟩
  apply GrothendieckTopology.isWeaklyContractible_of_clopenRefinements J (Q ⋙ B.inclusion) U
  · exact bot_mem_toGrothendieck_of_isEmpty B (SmallAffineProetale.precoverage B S hS) Q
      (fun E hE hfin ↦ ⟨E, rfl, hE, hfin⟩)
  · intro X Y f hf
    exact I.mono_of_mono_map (q.mono_of_mono_map (B.inclusion.mono_of_mono_map hf))
  · intro T hT
    obtain ⟨E, hE, hET⟩ := exists_covering_le_of_isSite (SmallAffineProetale.IsCovering B S hS)
      (SmallAffineProetale.isSite_isCovering B S hS) (SmallAffineProetale.precoverage B S hS)
      (fun _ _ ↦ Iff.rfl) T hT
    have hT' := functorPushforward_mem_topology B Q hE.1 hET
    obtain ⟨n, V, g, hdec, href⟩ :=
      exists_clopenRefinement_of_isWContractible B U.obj.obj.left hW _ hT'
    have hVaffine := isAffine_of_isClopenDecompositionCover B hUaff hdec
    have hwe (i : Fin n) : WeaklyEtale (B.inclusion.map (g i ≫ U.obj.obj.hom)) := by
      have h₁ : IsOpenImmersion (B.inclusion.map (g i)) := hdec.openImmersion i
      have h₂ : WeaklyEtale (B.inclusion.map U.obj.obj.hom) := U.obj.property
      rw [B.inclusion.map_comp]; infer_instance
    let X (i : Fin n) : SmallAffineProetale B S hS :=
      ⟨⟨Over.mk (g i ≫ U.obj.obj.hom), hwe i⟩, hVaffine i⟩
    let f (i : Fin n) : X i ⟶ U := ObjectProperty.homMk (ObjectProperty.homMk (Over.homMk (g i)))
    have hQf (i : Fin n) : Q.map (f i) = g i := rfl
    have hcover := ofArrows_mem_toGrothendieck_of_isClopenDecompositionCover B
      (SmallAffineProetale.precoverage B S hS) Q (fun E hE hfin ↦ ⟨E, rfl, hE, hfin⟩) X f hdec
    refine ⟨n, X, f, ?_, hcover, fun i ↦ ?_⟩
    · exact hdec
    · obtain ⟨Z, c₁, c₂, hc₁, hc₂⟩ := href i
      let c : X i ⟶ Z := ObjectProperty.homMk (ObjectProperty.homMk (Over.homMk c₂ (by
        have hw : Q.map c₁ ≫ U.obj.obj.hom = Z.obj.obj.hom := c₁.hom.hom.w
        show c₂ ≫ Z.obj.obj.hom = g i ≫ U.obj.obj.hom
        rw [← hw, ← Category.assoc, ← hc₂])))
      have hc : c ≫ c₁ = f i := by
        refine I.map_injective (q.map_injective ?_)
        show Q.map c ≫ Q.map c₁ = Q.map (f i)
        rw [hQf, show Q.map c = c₂ from rfl]
        exact hc₂.symm
      rw [← hc]
      exact T.downward_closed hc₁ c

/-- **Stacks 098I in the affine small pro-étale site `S_{affine, proétale}`.** Every object of
that site is covered by a single object with w-contractible ring of global sections.

The cover is the single affine ind-étale w-contractible cover of the underlying scheme of the
object, which is affine; its structure morphism to `S` is weakly étale because the cover is
weakly étale over the object, and the covering family has one member and so meets the
finiteness requirement on a standard pro-étale covering. -/
theorem hasEnoughObjects_isWContractible (U : SmallAffineProetale B S hS) :
    ∃ (V : SmallAffineProetale B S hS) (p : V ⟶ U),
      Sieve.ofArrows (fun _ : PUnit.{u + 1} ↦ V) (fun _ ↦ p) ∈
          SmallAffineProetale.topology B S hS U ∧
        IsWContractible.{u, u} Γ(V.obj.obj.left.obj, ⊤) := by
  classical
  have hUaff : IsAffine U.obj.obj.left.obj := U.property
  obtain ⟨W, g, hcov, haff, hwc, -, hwetale⟩ :=
    exists_affine_indEtale_wContractible_cover B U.obj.obj.left
  have hstr : WeaklyEtale (B.inclusion.map (g ≫ U.obj.obj.hom)) := by
    have h₁ : WeaklyEtale (B.inclusion.map g) := hwetale
    have h₂ : WeaklyEtale (B.inclusion.map U.obj.obj.hom) := U.obj.property
    rw [B.inclusion.map_comp]; infer_instance
  let V : SmallAffineProetale B S hS := ⟨⟨Over.mk (g ≫ U.obj.obj.hom), hstr⟩, haff⟩
  let p : V ⟶ U := ObjectProperty.homMk (ObjectProperty.homMk (Over.homMk g))
  exact ⟨V, p, Precoverage.generate_mem_toGrothendieck ⟨PreZeroHypercover.singleton p,
    (Presieve.ofArrows_pUnit p).trans (PreZeroHypercover.presieve₀_singleton p).symm,
    hcov, inferInstance⟩, hwc⟩

end SmallAffineProetale

/-- **Stacks 0990 for the affine small pro-étale site `S_{affine, proétale}`.** Every object of
the affine small pro-étale site of `S` is covered by objects which are affine, quasi-compact
objects of the site and weakly contractible in it. -/
@[stacks 0990 "the affine small pro-étale site S_{affine, pro-étale}"]
theorem SmallAffineProetale.hasEnough_affine_quasiCompact_weaklyContractible :
    (SmallAffineProetale.topology B S hS).HasEnoughObjects
      (fun U : SmallAffineProetale B S hS ↦
        IsAffine ((SmallAffineProetale.toScheme B S hS).obj U) ∧
          (SmallAffineProetale.topology B S hS).IsQuasiCompactObject U ∧
          (SmallAffineProetale.topology B S hS).IsWeaklyContractible U) := by
  intro U
  obtain ⟨V, p, hcov, hwc⟩ :=
    SmallAffineProetale.hasEnoughObjects_isWContractible B S hS U
  exact ⟨PUnit.{u + 1}, fun _ ↦ V, fun _ ↦ p, hcov, fun _ ↦
    ⟨V.property, SmallAffineProetale.isQuasiCompactObject B S hS V,
      SmallAffineProetale.isWeaklyContractible_of_isWContractible B S hS V hwc⟩⟩

end AlgebraicGeometry.ProEtale

end
