module

public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksCore.Tactic.StacksAttribute

/-!
# Associated points under isomorphism and under restriction to an open

An associated point of a sheaf of modules on a scheme is a point at which the maximal ideal of
the local ring is the annihilator of a single element of the stalk. Both data entering that
condition — the local ring and the stalk — are unchanged by an isomorphism of the module, and are
transported by the stalk maps of an open immersion. This file records the resulting two
invariance statements, together with the ring-theoretic transport they both rest on.

## Main results

* `Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPrimeStacks_iff_of_semilinear`:
  an associated prime is carried to an associated prime by an additive bijection of modules that
  is semilinear over an isomorphism of the base rings.
* `isAssociatedPoint_iff_of_isIso_stalkFunctor_map`, in the same
  `Stacks.AlgebraicGeometry.CodimensionOneObstruction` namespace:
  a morphism of `𝒪_X`-modules invertible on the stalk at `x` cannot change whether `x` is an
  associated point.
* `Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_congr`: the associated
  points of isomorphic `𝒪_X`-modules coincide. This is the previous statement for a global
  isomorphism.
* `Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_restrict_iff`: a point of
  the source of an open immersion `j` is associated to the restriction of a module along `j`
  exactly when its image is associated to the module.

## Implementation notes

The predicate `Stacks.Divisors.IsAssociatedPoint` is `IsAssociatedPrimeStacks` for the maximal
ideal of the local ring acting on the stalk, so both scheme-theoretic statements are instances of
the ring-theoretic transport, applied to:

* the identity of the local ring together with the stalk of the isomorphism, for
  `isAssociatedPoint_congr`; and
* the stalk map of the open immersion, which is an isomorphism, together with
  `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`, for `isAssociatedPoint_restrict_iff`.

In both cases the stalk isomorphism of modules is only additive — the stalk functor used by the
definition lands in abelian groups — so semilinearity over the ring isomorphism has to be checked
by hand, by writing a scalar and a vector as germs on a common open and using
`PresheafOfModules.germ_smul`. That the ring isomorphism matches the maximal ideals is
`IsLocalRing.map_ringEquiv_maximalIdeal`.

## References

* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.CodimensionOneObstruction

/-- **Transport of an associated prime along a semilinear additive bijection.** Let `e : R ≃+* S`
and let `f : M ≃+ N` satisfy `f (r • m) = e r • f m` for an `R`-module `M` and an `S`-module `N`.
Then a prime `p` of `R` is the annihilator of an element of `M` exactly when its image `p.map e`
is the annihilator of an element of `N`.

Both hypotheses are needed in the stated strength: injectivity of `f` identifies the two
annihilators as ideals related by `Ideal.comap e`, and surjectivity of `e` makes `Ideal.comap e`
undo `Ideal.map e`. -/
theorem isAssociatedPrimeStacks_iff_of_semilinear {R S M N : Type*} [CommRing R]
    [CommRing S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] (e : R ≃+* S)
    (f : M ≃+ N) (hf : ∀ r m, f (r • m) = e r • f m) {p : Ideal R} :
    IsAssociatedPrimeStacks R M p ↔ IsAssociatedPrimeStacks S N (p.map e.toRingHom) := by
  have hker : Ideal.comap e.toRingHom (⊥ : Ideal S) = ⊥ := by
    ext r
    simp
  have hcolon : ∀ m : M, (⊥ : Submodule R M).colon (Submodule.span R {m})
      = ((⊥ : Submodule S N).colon (Submodule.span S {f m})).comap e.toRingHom := by
    intro m
    ext r
    simp only [Ideal.mem_comap, Submodule.mem_colon_span_singleton, Submodule.mem_bot]
    have key : (e.toRingHom r) • f m = f (r • m) := (hf r m).symm
    rw [key]
    exact ⟨fun h => by rw [h, map_zero], fun h => f.injective (by rw [h, map_zero])⟩
  have hcomap : ∀ q : Ideal R, (q.map e.toRingHom).comap e.toRingHom = q := by
    intro q
    rw [Ideal.comap_map_of_surjective e.toRingHom e.surjective q, hker, sup_bot_eq]
  constructor
  · rintro ⟨hp, m, hm⟩
    refine ⟨Ideal.map_isPrime_of_surjective e.surjective
      (show RingHom.ker e.toRingHom ≤ p from hker.le.trans bot_le), f m, ?_⟩
    rw [← (hcolon m).symm.trans hm, Ideal.map_comap_of_surjective e.toRingHom e.surjective]
  · rintro ⟨hp, n, hn⟩
    refine ⟨?_, f.symm n, ?_⟩
    · simpa only [hcomap] using hp.comap e.toRingHom
    · rw [hcolon (f.symm n), f.apply_symm_apply, hn, hcomap]

/-- A scalar and a vector in the stalk at `x` of a module are germs of sections on a common
open neighbourhood of `x`. -/
private theorem exists_germ_eq_pair {X : Scheme.{u}} (M : X.Modules) (x : X)
    (r : X.presheaf.stalk x) (m : TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) (t : Γ(M, U)),
      X.presheaf.germ U x hx a = r ∧ TopCat.Presheaf.germ M.val.presheaf U x hx t = m := by
  obtain ⟨U₁, hx₁, a, ha⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
  obtain ⟨U₂, hx₂, t, ht⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
  have hx : x ∈ U₁ ⊓ U₂ := ⟨hx₁, hx₂⟩
  exact ⟨U₁ ⊓ U₂, hx, X.presheaf.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op a,
    M.val.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op t,
    by rw [TopCat.Presheaf.germ_res_apply]; exact ha,
    by rw [TopCat.Presheaf.germ_res_apply]; exact ht⟩

/-- **A morphism of `𝒪_X`-modules invertible on the stalk at `x` cannot change whether `x` is an
associated point.** Only the stalk at `x` and the local ring there enter the annihilator
condition, and the stalk map is additive and `𝒪_{X,x}`-linear, so an invertible stalk map carries
the condition both ways.

`isAssociatedPoint_congr` is the special case of a global isomorphism. -/
theorem isAssociatedPoint_iff_of_isIso_stalkFunctor_map {X : Scheme.{u}} {A B : X.Modules}
    (g : A ⟶ B) (x : X)
    (hg : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map g.mapPresheaf)) :
    Stacks.Divisors.IsAssociatedPoint A x ↔ Stacks.Divisors.IsAssociatedPoint B x := by
  let f : TopCat.Presheaf.stalk (C := Ab.{u}) A.val.presheaf x ≃+
      TopCat.Presheaf.stalk (C := Ab.{u}) B.val.presheaf x :=
    (@asIso _ _ _ _ _ hg).addCommGroupIsoToAddEquiv
  have hfm : ∀ (U : X.Opens) (hx : x ∈ U) (s : Γ(A, U)),
      f (TopCat.Presheaf.germ A.val.presheaf U x hx s)
        = TopCat.Presheaf.germ B.val.presheaf U x hx (g.app U s) :=
    fun U hx s => TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx _ s
  have hf : ∀ r m, f (r • m) = (RingEquiv.refl (X.presheaf.stalk x)) r • f m := by
    intro r m
    obtain ⟨U, hx, a', t', ha', ht'⟩ := exists_germ_eq_pair A x r m
    rw [← ha', ← ht']
    have h1 := PresheafOfModules.germ_smul A.val x U hx a' t'
    refine (congrArg f h1.symm).trans ?_
    refine (hfm U hx (a' • t')).trans ?_
    rw [Scheme.Modules.Hom.app_smul g a' t']
    refine (PresheafOfModules.germ_smul B.val x U hx a' (g.app U t')).trans ?_
    rw [hfm U hx t']
    rfl
  have key := isAssociatedPrimeStacks_iff_of_semilinear
    (RingEquiv.refl (X.presheaf.stalk x)) f hf
    (p := IsLocalRing.maximalIdeal (X.presheaf.stalk x))
  have hmap : Ideal.map (RingEquiv.refl (X.presheaf.stalk x)).toRingHom
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      = IsLocalRing.maximalIdeal (X.presheaf.stalk x) := Ideal.map_id _
  rwa [hmap] at key

/-- **Isomorphic `𝒪_X`-modules have the same associated points.** An isomorphism induces an
isomorphism of stalks over the same local ring, so the two annihilator conditions at a point are
the same condition. -/
theorem isAssociatedPoint_congr {X : Scheme.{u}} {A B : X.Modules} (ee : A ≅ B) (x : X) :
    Stacks.Divisors.IsAssociatedPoint A x ↔ Stacks.Divisors.IsAssociatedPoint B x :=
  isAssociatedPoint_iff_of_isIso_stalkFunctor_map ee.hom x
    (by
      let e := (TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso
        ((Scheme.Modules.toPresheaf X).mapIso ee)
      exact ⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩)

/-- **Associated points are detected on an open subscheme.** For an open immersion `j : X ⟶ Y`, a
point `x` of `X` is associated to the restriction of `G` along `j` exactly when `j x` is
associated to `G`.

The stalk map of `j` at `x` is an isomorphism of local rings, and the stalk of `G.restrict j` at
`x` is the stalk of `G` at `j x` by
`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`; the two identifications are compatible
with the actions, so the annihilator conditions correspond. -/
theorem isAssociatedPoint_restrict_iff {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (G : Y.Modules) (x : X) :
    Stacks.Divisors.IsAssociatedPoint (Scheme.Modules.restrict G j) x ↔
      Stacks.Divisors.IsAssociatedPoint G (j.base x) := by
  let e : (X.presheaf.stalk x) ≃+* (Y.presheaf.stalk (j.base x)) :=
    (asIso (j.stalkMap x)).symm.commRingCatIsoToRingEquiv
  let f : TopCat.Presheaf.stalk (C := Ab.{u}) (Scheme.Modules.restrict G j).val.presheaf x ≃+
      TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (j.base x) :=
    ((Scheme.Modules.restrictStalkNatIso j x).app G).addCommGroupIsoToAddEquiv
  have he (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
      e (X.presheaf.germ U x hx a) =
        Y.presheaf.germ (j ''ᵁ U) (j.base x) (by simpa) ((j.appIso U).inv a) := by
    apply e.symm.injective
    simp only [e.symm_apply_apply]
    change X.presheaf.germ U x hx a =
      j.stalkMap x (Y.presheaf.germ (j ''ᵁ U) (j.base x) (by simpa) ((j.appIso U).inv a))
    rw [j.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply]
    exact (X.presheaf.germ_res_apply _ _ _ _).symm
  have hf : ∀ r m, f (r • m) = e r • f m := by
    intro r m
    obtain ⟨U, hx, a', t', ha', ht'⟩ := exists_germ_eq_pair (Scheme.Modules.restrict G j) x r m
    have hfm (s : Γ(Scheme.Modules.restrict G j, U)) :
        f (TopCat.Presheaf.germ (Scheme.Modules.restrict G j).val.presheaf U x hx s) =
          G.presheaf.germ (j ''ᵁ U) (j.base x) (by simpa) s :=
      ConcreteCategory.congr_hom
        (Scheme.Modules.germ_restrictStalkNatIso_hom_app j x G hx) s
    rw [← ha', ← ht']
    have hgs := PresheafOfModules.germ_smul (Scheme.Modules.restrict G j).val x U hx a' t'
    refine (congrArg f hgs.symm).trans ?_
    refine (hfm (a' • t')).trans ?_
    rw [he, hfm]
    have hs := Scheme.Modules.smul_restrictAppIso_hom_apply j G U a' t'
    change a' • t' = (G.smul ((j.appIso U).inv a')).asHom.hom t' at hs
    rw [hs]
    let z : Γ(G, j ''ᵁ U) := t'
    change G.presheaf.germ (j ''ᵁ U) (j.base x) (by simpa)
      ((G.smul ((j.appIso U).inv a')).asHom.hom z) = _
    rw [G.smul_apply ((j.appIso U).inv a') z]
    change TopCat.Presheaf.germ G.val.presheaf (j ''ᵁ U) (j.base x) (by simpa)
      (((j.appIso U).inv a') • z) = _
    exact PresheafOfModules.germ_smul G.val (j.base x) (j ''ᵁ U) (by simpa)
      ((j.appIso U).inv a') z
  have key := isAssociatedPrimeStacks_iff_of_semilinear e f hf
    (p := IsLocalRing.maximalIdeal (X.presheaf.stalk x))
  have hmap : Ideal.map e.toRingHom (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      = IsLocalRing.maximalIdeal (Y.presheaf.stalk (j.base x)) :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  rwa [hmap] at key


/-- A prime associated to a ring in the Stacks sense stays associated along a ring
equivalence. -/
theorem isAssociatedPrimeStacks_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {p : Ideal R} (hp : IsAssociatedPrimeStacks R R p) :
    IsAssociatedPrimeStacks S S (p.map e.toRingHom) :=
  (isAssociatedPrimeStacks_iff_of_semilinear e e.toAddEquiv (fun r m => by
    simp [smul_eq_mul])).mp hp

end Stacks.AlgebraicGeometry.CodimensionOneObstruction

end
