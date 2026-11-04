module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.FiniteFlatPullback
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-!
# Weakly associated points and étale pullback

For an étale morphism of schemes, a point is weakly associated to the pullback of a
quasi-coherent module exactly when its image is weakly associated to the original module.

The statement is Zariski-local on source and target, so it reduces first to a morphism of
affine schemes and then, after a further localisation of the source, to `Spec` of a standard
étale ring map `R → R[x]_f / (g)`. Such a map factors as an open immersion followed by `Spec`
of the finite free map `R → R[x]/(f)`, so the finite flat case of Stacks 05FN applies.

## Main results

* `AlgebraicGeometry.isWeaklyAssociatedPoint_pullback_iff_of_etale` characterises weakly
  associated points of a pullback along an étale morphism.

## Implementation notes

Pullback is expressed using Mathlib's canonical functor
`AlgebraicGeometry.Scheme.Modules.pullback`. The image point is written as `h.base x`, so the
equality naming its image in the source is built into the statement.

The localisation steps are organised around the statement of the conclusion for a fixed
morphism, which is stable under pre- and post-composition with an open immersion. That lets the
three reductions — to an affine target, to an affine source, and to the standard étale
presentation — be carried out one at a time.

## References

* [Stacks Project, Tag 05FP](https://stacks.math.columbia.edu/tag/05FP)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The conclusion of Stacks 05FP for a fixed morphism: weak association of a point to the
pullback of any quasi-coherent module is weak association of its image. -/
private def PullbackWeakAssoc {X Y : Scheme.{u}} (h : X ⟶ Y) : Prop :=
  ∀ (G : Y.Modules) [G.IsQuasicoherent] (x : X),
    Stacks.Divisors.IsWeaklyAssociatedPoint ((Scheme.Modules.pullback h).obj G) x ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint G (h.base x)

/-- Precomposing with an open immersion preserves the conclusion. -/
private theorem pullbackWeakAssoc_comp_open_first {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (g : Y ⟶ Z) (hg : PullbackWeakAssoc g) :
    PullbackWeakAssoc (f ≫ g) := by
  intro G _ x
  let G' := (Scheme.Modules.pullback g).obj G
  have h₁ := (isWeaklyAssociatedPoint_iff_of_iso
    ((Scheme.Modules.pullbackComp f g).app G) x).symm
  show Stacks.Divisors.IsWeaklyAssociatedPoint
      ((Scheme.Modules.pullback (f ≫ g)).obj G) x ↔
    Stacks.Divisors.IsWeaklyAssociatedPoint G (g.base (f.base x))
  exact h₁.trans ((isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion f G' x).trans
    (hg G (f.base x)))

/-- The spectrum of a standard étale pair `R[x]_g / (f)` maps to `Spec R` through an open
immersion into `Spec (R[x]/(f))` followed by the finite flat map induced by `R → R[x]/(f)`. -/
private theorem standardEtalePair_factors_open_finiteFlat
    (R : Type u) [CommRing R] (P : StandardEtalePair R) :
    ∃ (T : Scheme.{u}) (j : Spec (.of P.Ring) ⟶ T) (g : T ⟶ Spec (.of R)),
      IsOpenImmersion j ∧ IsFinite g ∧ Flat g ∧
        Spec.map (CommRingCat.ofHom (algebraMap R P.Ring)) = j ≫ g := by
  let A := AdjoinRoot P.f
  let B := Localization.Away (AdjoinRoot.mk P.f P.g)
  let T : Scheme.{u} := Spec (.of A)
  let g : T ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let j : Spec (.of P.Ring) ⟶ T :=
    (Scheme.Spec.mapIso P.equivAwayAdjoinRoot.toCommRingCatIso.op).symm.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B))
  have : IsFinite g := by
    rw [show g = Spec.map (CommRingCat.ofHom (algebraMap R A)) from rfl, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr P.monic_f.finite_adjoinRoot
  have : Flat g := by
    rw [show g = Spec.map (CommRingCat.ofHom (algebraMap R A)) from rfl, Flat.SpecMap_iff]
    have := P.monic_f.free_adjoinRoot
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  refine ⟨T, j, g, ?_, inferInstance, inferInstance, ?_⟩
  · dsimp [j]
    infer_instance
  · dsimp [j, g]
    simp only [← Spec.map_comp]
    congr 1
    ext r
    show algebraMap R P.Ring r =
      P.equivAwayAdjoinRoot.symm (algebraMap A B (algebraMap R A r))
    rw [← IsScalarTower.algebraMap_apply R A B]
    exact (P.equivAwayAdjoinRoot.symm.commutes r).symm

/-- Stacks 05FP for the spectrum of a standard étale pair. -/
private theorem isWeaklyAssociatedPoint_pullback_standardEtalePair_iff
    (R : Type u) [CommRing R] (P : StandardEtalePair R)
    (G : (Spec (.of R)).Modules) [G.IsQuasicoherent] (x : Spec (.of P.Ring)) :
    Stacks.Divisors.IsWeaklyAssociatedPoint
        ((Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R P.Ring)))).obj G) x ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint G
        ((Spec.map (CommRingCat.ofHom (algebraMap R P.Ring))).base x) := by
  obtain ⟨T, j, g, _, _, _, h⟩ := standardEtalePair_factors_open_finiteFlat R P
  rw [h]
  exact pullbackWeakAssoc_comp_open_first j g
    (fun G _ x => isWeaklyAssociatedPoint_pullback_iff_of_finite_flat g G x) G x

/-- Postcomposing with an open immersion preserves the conclusion. -/
private theorem pullbackWeakAssoc_comp_open_second {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g] (hf : PullbackWeakAssoc f) :
    PullbackWeakAssoc (f ≫ g) := by
  intro G _ x
  let G' := (Scheme.Modules.pullback g).obj G
  have : G'.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion g G
  have h₁ := (isWeaklyAssociatedPoint_iff_of_iso
    ((Scheme.Modules.pullbackComp f g).app G) x).symm
  show Stacks.Divisors.IsWeaklyAssociatedPoint
      ((Scheme.Modules.pullback (f ≫ g)).obj G) x ↔
    Stacks.Divisors.IsWeaklyAssociatedPoint G (g.base (f.base x))
  exact h₁.trans ((hf G' x).trans
    (isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion g G (f.base x)))

/-- If the conclusion holds for `j ≫ h` with `j` an open immersion, it holds for `h` at points
in the image of `j`. -/
private theorem isWeaklyAssociatedPoint_pullback_iff_of_comp_isOpenImmersion
    {W X Y : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j] (h : X ⟶ Y)
    (hjh : PullbackWeakAssoc (j ≫ h)) (G : Y.Modules) [G.IsQuasicoherent] (y : W) :
    Stacks.Divisors.IsWeaklyAssociatedPoint ((Scheme.Modules.pullback h).obj G) (j.base y) ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint G (h.base (j.base y)) :=
  (isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion j _ y).symm.trans
    ((isWeaklyAssociatedPoint_iff_of_iso ((Scheme.Modules.pullbackComp j h).app G) y).trans
      (hjh G y))

/-- Stacks 05FP for `Spec` of a standard étale algebra. -/
private theorem pullbackWeakAssoc_isStandardEtale_affine
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsStandardEtale R A] :
    PullbackWeakAssoc (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  let P : StandardEtalePresentation R A :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  let e : Spec (.of A) ≅ Spec (.of P.P.Ring) :=
    (Scheme.Spec.mapIso P.equivRing.toCommRingCatIso.op).symm
  have hstd : PullbackWeakAssoc
      (Spec.map (CommRingCat.ofHom (algebraMap R P.P.Ring))) := by
    intro G _ x
    exact isWeaklyAssociatedPoint_pullback_standardEtalePair_iff R P.P G x
  have hfac : Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P.P.Ring)) := by
    dsimp [e]
    rw [← Spec.map_comp]
    congr 1
    ext r
    show algebraMap R A r = P.equivRing.symm (algebraMap R P.P.Ring r)
    exact (P.equivRing.symm.commutes r).symm
  rw [hfac]
  exact pullbackWeakAssoc_comp_open_first e.hom _ hstd

/-- Stacks 05FP for `Spec` of an étale algebra: at each prime the algebra becomes standard
étale after inverting one element, and the corresponding localisation is an open immersion
whose image contains the prime. -/
private theorem pullbackWeakAssoc_etale_affine
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Etale R A] :
    PullbackWeakAssoc (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  intro G _ x
  let h : Spec (.of A) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A))
  have : x.asIdeal.IsPrime := x.isPrime
  obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) (S := A) x.asIdeal
  have : Algebra.IsStandardEtale R (Localization.Away g) := hstd
  let j : Spec (.of (Localization.Away g)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g)))
  have hxj : x ∈ j.opensRange :=
    (Scheme.Hom.opensRange_localizationAway (R := .of A) g).symm ▸ hg
  obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp hxj
  have hk : j ≫ h = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g))) := by
    dsimp [j, h]
    rw [← Spec.map_comp]
    congr 1
  have hstd' : PullbackWeakAssoc (j ≫ h) := by
    rw [hk]
    exact pullbackWeakAssoc_isStandardEtale_affine R (Localization.Away g)
  rw [← hy]
  exact isWeaklyAssociatedPoint_pullback_iff_of_comp_isOpenImmersion j h hstd' G y

/-- Stacks 05FP for an étale morphism of affine schemes. -/
private theorem pullbackWeakAssoc_of_isAffine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (h : X ⟶ Y) [Etale h] :
    PullbackWeakAssoc h := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := h.appTop.hom.toAlgebra
  have hring : h.appTop.hom.Etale :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).1 inferInstance
  have : Algebra.Etale Γ(Y, ⊤) Γ(X, ⊤) := hring.toAlgebra
  have hmid : PullbackWeakAssoc (Spec.map h.appTop) :=
    pullbackWeakAssoc_etale_affine Γ(Y, ⊤) Γ(X, ⊤)
  have heq : h = (X.isoSpec.hom ≫ Spec.map h.appTop) ≫ Y.isoSpec.inv := by
    rw [← cancel_mono Y.isoSpec.hom]
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      (Scheme.isoSpec_hom_naturality h).symm
  rw [heq]
  exact pullbackWeakAssoc_comp_open_second _ _
    (pullbackWeakAssoc_comp_open_first X.isoSpec.hom _ hmid)

/-- Stacks 05FP for an arbitrary étale morphism, obtained from the affine case by restricting
to an affine open of the target and an affine open of its preimage. -/
private theorem pullbackWeakAssoc_etale
    {X Y : Scheme.{u}} (h : X ⟶ Y) [Etale h] : PullbackWeakAssoc h := by
  intro G _ x
  obtain ⟨V, hV, hxV, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show h.base x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨U, hU, hxU, e⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ h ⁻¹ᵁ V from hxV)
  let k : U.toScheme ⟶ V.toScheme := h.resLE V U e
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : Etale k := by
    show Etale (h.resLE V U e)
    exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)).2
      ((RingHom.Etale.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso h V U e)).2
        (h.etale_appLE hV hU e))
  have hfac : U.ι ≫ h = k ≫ V.ι := (Scheme.Hom.resLE_comp_ι h e).symm
  have hU' : PullbackWeakAssoc (U.ι ≫ h) := by
    rw [hfac]
    exact pullbackWeakAssoc_comp_open_second k V.ι (pullbackWeakAssoc_of_isAffine k)
  exact isWeaklyAssociatedPoint_pullback_iff_of_comp_isOpenImmersion U.ι h hU' G ⟨x, hxU⟩

/-- **Stacks Project, Tag 05FP.** A point is weakly associated to the pullback of a
quasi-coherent module along an étale morphism if and only if its image is weakly associated to
the original module. -/
@[stacks 05FP]
lemma isWeaklyAssociatedPoint_pullback_iff_of_etale
    {U S : Scheme.{u}} (h : U ⟶ S) [Etale h]
    (G : S.Modules) [G.IsQuasicoherent] (x : U) :
    Stacks.Divisors.IsWeaklyAssociatedPoint ((Scheme.Modules.pullback h).obj G) x ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint G (h.base x) :=
  pullbackWeakAssoc_etale h G x

end AlgebraicGeometry

end
