module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber

/-!
# Maximal ideals in the local rings of a morphism with étale fibres

Let `f : X ⟶ S` be a morphism of schemes whose fibres are disjoint unions of spectra of finite
separable residue-field extensions. At every point of `X`, extending the maximal ideal of the
corresponding local ring of `S` along the stalk map gives the maximal ideal.

## Main results

* `AlgebraicGeometry.map_maximalIdeal_eq_of_etale_fibers` identifies the extended maximal ideal
  with the maximal ideal.

## Implementation notes

An étale scheme over a field is precisely a disjoint union of spectra of finite separable field
extensions, so the hypothesis from the source is expressed by requiring every canonical fibre
morphism to the spectrum of the residue field to be étale. The extension of the maximal ideal is
written as `Ideal.map` along the canonical stalk map.

The proof factors through the fibre: for a morphism to the spectrum of a field which is formally
unramified and locally of finite type, every local ring of the source has zero maximal ideal.
Transporting this back uses the local-spectrum correspondence
`AlgebraicGeometry.SpecToEquivOfLocalRing`: the quotient of the local ring of `X` by the extended
maximal ideal is a local ring receiving a map from the residue field of `S`, so its spectrum maps
into the fibre, and the correspondence identifies the induced map on local rings at the closed
point with the quotient map.

## References

* [Stacks Project, Tag 0345](https://stacks.math.columbia.edu/tag/0345)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

universe u

/-- Two opposite stalk comparison isomorphisms compose to the identity: the inverse of one is,
by proof irrelevance, the forward map of the other. -/
private lemma stalkCongr_hom_comp_stalkCongr_hom {Z : TopCat.{u}}
    (F : TopCat.Presheaf CommRingCat.{u} Z) {x y : Z}
    (e₁ : Inseparable x y) (e₂ : Inseparable y x) {W : CommRingCat.{u}}
    (k : F.stalk x ⟶ W) :
    (F.stalkCongr e₁).hom ≫ (F.stalkCongr e₂).hom ≫ k = k := by
  rw [show (F.stalkCongr e₂).hom = (F.stalkCongr e₁).inv from rfl, Iso.hom_inv_id_assoc]

/-- A scheme formally unramified and locally of finite type over a field has zero maximal ideal
in every local ring. -/
private lemma maximalIdeal_stalk_eq_bot_of_unramified
    {K : Type u} [Field K] {X : Scheme.{u}} (g : X ⟶ Spec (.of K))
    [FormallyUnramified g] [LocallyOfFiniteType g] (x : X) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk x) = ⊥ := by
  have hbase : IsLocalRing.maximalIdeal ((Spec (.of K)).presheaf.stalk (g x)) = ⊥ := by
    let e : (Spec (.of K)).presheaf.stalk (g x) ≅ CommRingCat.of K :=
      (Spec (.of K)).presheaf.stalkCongr (.of_eq (Subsingleton.elim _ _)) ≪≫
        stalkClosedPointIso (.of K)
    exact (Ideal.map_eq_bot_iff_of_injective (ConcreteCategory.bijective_of_isIso e.hom).1).mp
      ((IsLocalRing.map_maximalIdeal_of_surjective e.hom.hom
        (ConcreteCategory.bijective_of_isIso e.hom).2).trans IsLocalRing.maximalIdeal_eq_bot)
  have hft := LocallyOfFiniteType.stalkMap g x
  have hfu := FormallyUnramified.stalkMap g x
  algebraize [(g.stalkMap x).hom]
  have : IsLocalHom (algebraMap ((Spec (.of K)).presheaf.stalk (g x))
      (X.presheaf.stalk x)) := inferInstanceAs (IsLocalHom (g.stalkMap x).hom)
  rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := (Spec (.of K)).presheaf.stalk (g x)),
    hbase, Ideal.map_bot]

/-- If the maximal ideal of the local ring of the fibre at a point vanishes, then the extended
maximal ideal at that point is the maximal ideal. -/
private lemma map_maximalIdeal_eq_of_maximalIdeal_fiber_stalk_eq_bot
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (hf : IsLocalRing.maximalIdeal
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) = ⊥) :
    Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  let I := Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
  have hI : I ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := IsLocalRing.map_maximalIdeal_le _
  have : Nontrivial (X.presheaf.stalk x ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hI)
  let Q := CommRingCat.of (X.presheaf.stalk x ⧸ I)
  let q : X.presheaf.stalk x ⟶ Q := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have : IsLocalRing Q := IsLocalRing.of_surjective' q.hom Ideal.Quotient.mk_surjective
  have : IsLocalHom q.hom := IsLocalHom.of_surjective q.hom Ideal.Quotient.mk_surjective
  let b : S.residueField (f x) ⟶ Q := CommRingCat.ofHom
    (Ideal.Quotient.lift _ (q.hom.comp (f.stalkMap x).hom) fun _ ha =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha))
  have hb : S.residue (f x) ≫ b = f.stalkMap x ≫ q := by ext; rfl
  let t : Spec Q ⟶ f.fiber (f x) := pullback.lift
    (Spec.map q ≫ X.fromSpecStalk x) (Spec.map b) (by
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
        ← Spec.map_comp_assoc, ← hb, Spec.map_comp_assoc]
      rfl)
  have ht : t ≫ f.fiberι (f x) = Spec.map q ≫ X.fromSpecStalk x := pullback.lift_fst ..
  let y := t (IsLocalRing.closedPoint Q)
  have hy : f.fiberι (f x) y = x := by
    change (t ≫ f.fiberι (f x)) (IsLocalRing.closedPoint Q) = x
    rw [ht]
    exact (Scheme.Hom.comp_apply (Spec.map q) (X.fromSpecStalk x) _).trans
      (by rw [Spec_closedPoint]; exact Scheme.fromSpecStalk_closedPoint)
  have hxy : Inseparable x (f.fiberι (f x) y) := .of_eq hy.symm
  let a : X.presheaf.stalk x ⟶ Q :=
    (X.presheaf.stalkCongr hxy).hom ≫ (f.fiberι (f x)).stalkMap y ≫ Scheme.stalkClosedPointTo t
  have haq : a = q := by
    have he : SpecToEquivOfLocalRing X Q (t ≫ f.fiberι (f x)) = ⟨x, q, inferInstance⟩ := by
      rw [ht]
      exact (SpecToEquivOfLocalRing X Q).apply_symm_apply ⟨x, q, inferInstance⟩
    obtain ⟨h, he⟩ := SpecToEquivOfLocalRing_eq_iff.mp he
    change Scheme.stalkClosedPointTo (t ≫ f.fiberι (f x)) = _ at he
    dsimp only [a]
    rw [← Scheme.stalkClosedPointTo_comp, he]
    exact stalkCongr_hom_comp_stalkCongr_hom X.presheaf _ _ q
  have hy' : y = f.asFiber x :=
    (f.fiberι (f x)).isEmbedding.injective (hy.trans (f.fiberι_asFiber x).symm)
  refine le_antisymm hI fun r hr => Ideal.Quotient.eq_zero_iff_mem.mp ?_
  change q.hom r = 0
  rw [← haq]
  have hr' := IsLocalRing.map_maximalIdeal_le ((f.fiberι (f x)).stalkMap y).hom
    (Ideal.mem_map_of_mem _ (IsLocalRing.map_maximalIdeal_le
      (X.presheaf.stalkCongr hxy).hom.hom (Ideal.mem_map_of_mem _ hr)))
  have hfy : IsLocalRing.maximalIdeal ((f.fiber (f x)).presheaf.stalk y) = ⊥ := hy'.symm ▸ hf
  rw [hfy, Ideal.mem_bot] at hr'
  change (Scheme.stalkClosedPointTo t).hom _ = 0
  exact (congrArg (Scheme.stalkClosedPointTo t).hom hr').trans (map_zero _)

/-- If every fibre of a scheme morphism is a disjoint union of spectra of finite separable
extensions of the relevant residue field, then extending the maximal ideal along the stalk map
at any point gives the maximal ideal. -/
public lemma map_maximalIdeal_eq_of_etale_fibers
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hfib : ∀ s : S, Etale (f.fiberToSpecResidueField s)) (x : X) :
    Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  have := hfib (f x)
  exact map_maximalIdeal_eq_of_maximalIdeal_fiber_stalk_eq_bot f x
    (maximalIdeal_stalk_eq_bot_of_unramified (K := S.residueField (f x))
      (f.fiberToSpecResidueField (f x)) (f.asFiber x))

end AlgebraicGeometry

end
