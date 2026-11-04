module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineCoversTop
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtaleWeaklyContractible

/-!
# Weakly contractible objects of the small pro-étale site

A locally surjective morphism of sheaves of types on the small pro-étale site of a scheme is
surjective on sections over an affine object whose ring of global sections is w-contractible.
This is weak contractibility of that object, stated at an arbitrary value universe.

Every covering sieve of the object is pushed forward to a covering sieve of its underlying
scheme in the chosen big site, where w-contractibility refines it by a finite disjoint clopen
Zariski cover. The members of that cover are open subschemes of the object, hence weakly étale
over the base, so they are again objects of the small pro-étale site and refine the original
sieve.

## Main results

* `AlgebraicGeometry.ProEtale.SmallProetale.surjective_sections_of_isWContractible`: the
  criterion for an affine object of the small pro-étale site.
* `AlgebraicGeometry.ProEtale.SmallProetale.hasEnoughObjects_isWContractible`: those objects
  cover every object of the site.

## References

* [Stacks Project, Tag 098F](https://stacks.math.columbia.edu/tag/098F)
* [Stacks Project, Tag 098H](https://stacks.math.columbia.edu/tag/098H)
* [Stacks Project, Tag 0983](https://stacks.math.columbia.edu/tag/0983)
* [Stacks Project, Tag 0990](https://stacks.math.columbia.edu/tag/0990)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite ProetaleWContractible

universe t u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Composing a weakly étale morphism into an object of the small pro-étale site with its
structure morphism is weakly étale. -/
private theorem weaklyEtale_comp_hom (U : SmallProetale B S hS) {V : B.Scheme}
    (g : V ⟶ U.obj.left) [WeaklyEtale (B.inclusion.map g)] :
    WeaklyEtale (B.inclusion.map (g ≫ U.obj.hom)) := by
  have : WeaklyEtale (B.inclusion.map U.obj.hom) := U.property
  rw [B.inclusion.map_comp]; infer_instance

/-- A morphism of the small pro-étale site built from a morphism of underlying schemes maps back
to that morphism. -/
private theorem forget_map_preimage_homMk (X Y : SmallProetale B S hS)
    (g : X.obj.left ⟶ Y.obj.left) (h : g ≫ Y.obj.hom = X.obj.hom) :
    (BigProetaleOver.forget B S hS).map ((SmallProetale.inclusion B S hS).map
      ((SmallProetale.inclusion B S hS).preimage (Over.homMk g h))) = g := by
  rw [Functor.map_preimage]; rfl

/-- An affine object of the small pro-étale site whose ring of global sections is w-contractible
is weakly contractible: a locally surjective morphism of sheaves of types in any universe is
surjective on sections over it. -/
theorem SmallProetale.surjective_sections_of_isWContractible
    (U : SmallProetale B S hS) [IsAffine U.obj.left.obj]
    (hW : IsWContractible.{u, u} Γ(U.obj.left.obj, ⊤))
    (F G : Sheaf (SmallProetale.topology B S hS) (Type t)) (φ : F ⟶ G)
    (hφ : Sheaf.IsLocallySurjective φ) :
    Function.Surjective (φ.hom.app (op U)) := by
  classical
  let I := SmallProetale.inclusion B S hS
  let q := BigProetaleOver.forget B S hS
  let Q := I ⋙ q
  let J := SmallProetale.topology B S hS
  let _ : MorphismProperty.ContainsIdentities @WeaklyEtale := ⟨fun _ ↦ inferInstance⟩
  refine GrothendieckTopology.surjective_sections_of_clopenRefinements J (Q ⋙ B.inclusion) U
    ?_ ?_ ?_ F G φ hφ
  · intro Z hZ
    let E : PreZeroHypercover.{u + 1} Z :=
      ⟨ULift.{u + 1} Empty, fun i ↦ i.down.elim, fun i ↦ i.down.elim⟩
    have hE : SmallProetale.IsCovering B S hS ⟨Z, E⟩ := by
      refine ⟨?_, ?_⟩
      · show ((E.map Q).map B.inclusion).presieve₀ ∈ _
        apply Scheme.zariskiPrecoverage_le_propQCPrecoverage
        rw [Scheme.zariskiPrecoverage, Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun x ↦ (hZ.false x).elim, fun i ↦ i.down.elim⟩
      · simp only [E, PreZeroHypercover.map_I₀, Cardinal.mk_eq_zero, zero_le]
    have heq : E.sieve₀ = ⊥ := by
      ext X f
      refine ⟨fun hf ↦ ?_, False.elim⟩
      obtain ⟨i, -, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hf
      exact i.down.elim
    exact heq ▸ Precoverage.generate_mem_toGrothendieck ⟨E, rfl, hE⟩
  · exact fun _ hf ↦ I.mono_of_mono_map (q.mono_of_mono_map (B.inclusion.mono_of_mono_map hf))
  · intro T hT
    obtain ⟨E, hE, hET⟩ := exists_covering_le_of_isSite (SmallProetale.IsCovering B S hS)
      (SmallProetale.isSite B S hS) (SmallProetale.precoverage B S hS)
      (fun _ _ ↦ Iff.rfl) T hT
    have hT' : T.functorPushforward Q ∈ B.topology (Q.obj U) := by
      refine B.topology.superset_covering (Sieve.functorPushforward_monotone Q U
        ((Sieve.generate_le_iff _ _).mpr hET)) ?_
      rw [← PreZeroHypercover.sieve₀_map]
      exact Precoverage.generate_mem_toGrothendieck ⟨E.map Q, rfl, hE⟩
    obtain ⟨n, V, g, hdec, href⟩ :=
      exists_clopenRefinement_of_isWContractible B U.obj.left hW _ hT'
    let X (i : Fin n) : SmallProetale B S hS :=
      ⟨Over.mk (g i ≫ U.obj.hom), have := hdec.openImmersion i; weaklyEtale_comp_hom B S hS U (g i)⟩
    let f (i : Fin n) : X i ⟶ U := I.preimage (Over.homMk (g i))
    have hQf (i : Fin n) : Q.map (f i) = g i := by
      exact forget_map_preimage_homMk B S hS (X i) U (g i) _
    let F : PreZeroHypercover.{u + 1} U :=
      ⟨ULift.{u + 1} (Fin n), fun i ↦ X i.down, fun i ↦ f i.down⟩
    have hF : B.IsProetaleCovering ⟨Q.obj U, F.map Q⟩ := by
      show ((F.map Q).map B.inclusion).presieve₀ ∈ _
      apply Scheme.zariskiPrecoverage_le_propQCPrecoverage
      rw [Scheme.zariskiPrecoverage, Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x ↦ ?_, fun i ↦ ?_⟩
      · have hx : x ∈ ⋃ i, Set.range (B.inclusion.map (g i)).base :=
          (Set.ext_iff.mp hdec.cover x).mpr (Set.mem_univ x)
        obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hx
        refine ⟨ULift.up i, y, ?_⟩
        show (B.inclusion.map (Q.map (f i))).base y = x
        rwa [hQf]
      · show IsOpenImmersion (B.inclusion.map (Q.map (f i.down)))
        rw [hQf]; exact hdec.openImmersion i.down
    have hFQfin : Finite (F.map Q).I₀ := inferInstanceAs (Finite (ULift.{u + 1} (Fin n)))
    obtain ⟨ι, hfin, a, ha, -⟩ := B.exists_finite_restrictIndex_covering (F.map Q) hF
    have hFa : (F.restrictIndex a).sieve₀ ∈ J U :=
      Precoverage.generate_mem_toGrothendieck ⟨F.restrictIndex a, rfl, ha⟩
    have hFtop : F.sieve₀ ∈ J U :=
      J.superset_covering (Sieve.generate_mono (F.presieve₀_restrictIndex_le a)) hFa
    have hcover : Sieve.ofArrows X f ∈ J U := by
      refine J.superset_covering (fun Y b hb ↦ ?_) hFtop
      obtain ⟨i, c, hc⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hb
      exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨i.down, c, hc⟩
    refine ⟨n, X, f, ?_, hcover, fun i ↦ ?_⟩
    · show IsClopenDecompositionCover (fun i ↦ (V i).obj)
        (fun i ↦ B.inclusion.map (Q.map (f i)))
      simpa only [hQf] using hdec
    · obtain ⟨Z, c₁, c₂, hc₁, hc₂⟩ := href i
      let c : X i ⟶ Z := I.preimage (Over.homMk c₂ (by
        have hw : Q.map c₁ ≫ U.obj.hom = Z.obj.hom := Over.w (I.map c₁)
        show c₂ ≫ Z.obj.hom = g i ≫ U.obj.hom
        rw [← hw, ← Category.assoc, ← hc₂]))
      have hc : c ≫ c₁ = f i := by
        refine I.map_injective (q.map_injective ?_)
        show Q.map c ≫ Q.map c₁ = Q.map (f i)
        rw [hQf, show Q.map c = c₂ from forget_map_preimage_homMk B S hS (X i) Z c₂ _]
        exact hc₂.symm
      exact hc ▸ T.downward_closed hc₁ c

/-- The property of an object of the small pro-étale site of being affine with w-contractible
ring of global sections. -/
def SmallProetale.IsWContractibleObject :
    ObjectProperty (SmallProetale B S hS) :=
  fun U ↦ IsAffine U.obj.left.obj ∧ IsWContractible.{u, u} Γ(U.obj.left.obj, ⊤)

variable (T : B.Scheme)

/-- **Stacks 0990 for the small pro-étale site.** Every object of the small pro-étale site is
covered by affine objects whose rings of global sections are w-contractible: the object is
covered by its affine opens, and each of those is covered by a single affine object with
w-contractible global sections. -/
theorem SmallProetale.hasEnoughObjects_isWContractible :
    (SmallProetale.topology B T.obj T.property).HasEnoughObjects
      (SmallProetale.IsWContractibleObject B T.obj T.property) := by
  classical
  intro U
  let J := SmallProetale.topology B T.obj T.property
  let I := SmallProetale.inclusion B T.obj T.property
  let A := SmallProetale.affineCoverObject B T U
  let a := SmallProetale.affineCoverMap B T U
  have hA : Sieve.ofArrows A a ∈ J U :=
    Precoverage.generate_mem_toGrothendieck
      (SmallProetale.ofArrows_affineCoverObject_mem_precoverage B T U)
  have hstep (i : ((SmallProetale.toScheme B T.obj T.property).obj U).affineCover.I₀) :
      ∃ (W : SmallProetale B T.obj T.property) (w : W ⟶ A i),
        Sieve.generate (Presieve.singleton w) ∈ J (A i) ∧
          SmallProetale.IsWContractibleObject B T.obj T.property W := by
    have _ : IsAffine (A i).obj.left.obj :=
      SmallProetale.isAffine_affineCoverObject B T U i
    obtain ⟨V, g, hcov, haff, hwc, -, hwe⟩ :=
      exists_affine_indEtale_wContractible_cover B (A i).obj.left
    let W : SmallProetale B T.obj T.property :=
      ⟨Over.mk (g ≫ (A i).obj.hom), weaklyEtale_comp_hom B T.obj T.property (A i) g⟩
    let w : W ⟶ A i := I.preimage (Over.homMk g)
    have hcov' : SmallProetale.IsCovering B T.obj T.property
        ⟨A i, PreZeroHypercover.singleton w⟩ := by
      refine ⟨?_, hcov.2⟩
      have hQw : (BigProetaleOver.forget B T.obj T.property).map (I.map w) = g := by
        exact forget_map_preimage_homMk B T.obj T.property W (A i) g _
      have hpre : ((((PreZeroHypercover.singleton w).map I).map
          (BigProetaleOver.forget B T.obj T.property)).map B.inclusion).presieve₀ =
          ((PreZeroHypercover.singleton g).map B.inclusion).presieve₀ := by
        simp only [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀_singleton,
          Presieve.map_singleton, hQw]
      show ((((PreZeroHypercover.singleton w).map I).map
        (BigProetaleOver.forget B T.obj T.property)).map B.inclusion).presieve₀ ∈ _
      rw [hpre]
      exact hcov.1
    refine ⟨W, w, ?_, haff, hwc⟩
    have h := Precoverage.generate_mem_toGrothendieck (J := SmallProetale.precoverage
      B T.obj T.property) ⟨PreZeroHypercover.singleton w, rfl, hcov'⟩
    rwa [PreZeroHypercover.presieve₀_singleton] at h
  choose W w hWcov hWprop using hstep
  refine ⟨((SmallProetale.toScheme B T.obj T.property).obj U).affineCover.I₀,
    W, fun i ↦ w i ≫ a i, ?_, hWprop⟩
  refine J.transitive hA _ fun Y b hb ↦ ?_
  obtain ⟨Y', c, d, ⟨i⟩, hcd⟩ := hb
  refine J.superset_covering (fun Z e he ↦ ?_) (J.pullback_stable c (hWcov i))
  obtain ⟨Z', e₁, e₂, ⟨⟩, he₁⟩ := he
  exact ⟨_, e₁, w i ≫ a i, ⟨i⟩, by
    rw [← hcd, ← Category.assoc, he₁, Category.assoc]⟩

end AlgebraicGeometry.ProEtale

end
