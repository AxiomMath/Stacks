module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.ComponentsOverSeparableClosure
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparableClosure

/-!
# Geometrically irreducible components after a finite separable extension

For a scheme locally of finite type over a field and having finitely many irreducible
components, a finite separable extension of the ground field makes every irreducible component
geometrically irreducible.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.exists_finite_separable_extension_geometricallyIrreducible_components`
  gives the finite separable extension over which all irreducible components are geometrically
  irreducible.

## Implementation notes

An irreducible component is endowed with its reduced induced closed subscheme structure: this is
the subscheme defined by the vanishing ideal of the corresponding closed subset. Geometric
irreducibility is insensitive to this choice of reduced scheme structure.

The proof works over a separable closure `K` of `k`, where the components are classified by
Tag 04KZ, and then descends to the compositum `E` of the finitely many finite subextensions
over which the individual components are defined.

## References

* [Stacks Project, Tag 054R](https://stacks.math.columbia.edu/tag/054R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

open CommRingCat

/-- A scheme over a field whose base change to a separable closure is irreducible is
geometrically irreducible. -/
private lemma geometricallyIrreducible_of_irreducibleSpace_of_isSepClosure
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    (Y : Scheme.{u}) (g : Y ⟶ Spec (.of k)) :
    IrreducibleSpace ↥(pullback g (Spec.map (ofHom (algebraMap k K)))) →
      GeometricallyIrreducible g :=
  ((geometricallyIrreducible_tfae_of_isSepClosure k Y g K).out 3 1).mp

/-- Criterion for geometric irreducibility of a scheme `S` over `k`: its base change to a
separable closure is identified with a pullback along a closed immersion whose set-theoretic
preimage is a given irreducible set. -/
private lemma geometricallyIrreducible_of_closed_pullback
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    (S Y X : Scheme.{u}) (g : S ⟶ Spec (.of k)) (i : S ⟶ Y) [IsClosedImmersion i]
    (q : X ⟶ Y) (Z : Set X) (hZ : IsIrreducible Z)
    (hpre : q.base ⁻¹' Set.range i.base = Z)
    (e : pullback g (Spec.map (ofHom (algebraMap k K))) ≅ pullback i q) :
    GeometricallyIrreducible g := by
  refine geometricallyIrreducible_of_irreducibleSpace_of_isSepClosure k K S g
    (e.schemeIsoToHomeo.irreducibleSpace_iff.mpr ?_)
  apply (pullback.snd i q).isClosedEmbedding.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr
  rw [Scheme.Pullback.range_snd, hpre]
  exact Subtype.irreducibleSpace hZ

/-- Base change of a subscheme `T ⊆ X ×_S E` along `K ⟶ E`, read through a comparison
isomorphism `a` for the two-step base change and the induced projection `q`. -/
private noncomputable def componentBaseChangeIso
    {X S E K T Y : Scheme.{u}} (f : X ⟶ S) (g : E ⟶ S) (h : K ⟶ E)
    (i : T ⟶ pullback f g) (a : pullback (pullback.snd f g) h ≅ Y)
    (q : Y ⟶ pullback f g)
    (hfac : a.hom ≫ q = pullback.fst (pullback.snd f g) h) :
    pullback (i ≫ pullback.snd f g) h ≅ pullback i q :=
  have hq : q = a.inv ≫ pullback.fst (pullback.snd f g) h := a.eq_inv_comp.mpr hfac
  (pullbackRightPullbackFstIso (pullback.snd f g) h i).symm ≪≫
    (asIso (pullback.map i q i (pullback.fst (pullback.snd f g) h) (𝟙 T) a.inv
      (𝟙 (pullback f g)) (by simp) (by rw [Category.comp_id, hq]))).symm

/-- A scheme locally of finite type over a field with finitely many irreducible components still
has finitely many irreducible components after base change to a separable closure. -/
public theorem finite_irreducibleComponents_baseChange_of_isSepClosure
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (hX : (irreducibleComponents X).Finite) :
    (irreducibleComponents
      (pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k K))))).Finite := by
  classical
  let XK := pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k K)))
  let p := pullback.fst f (Spec.map (ofHom (algebraMap k K)))
  let Xover : Over (Spec (.of k)) := Over.mk f
  let imageComponent : Set XK → Set X := fun Z => p.base '' Z
  have : LocallyOfFiniteType Xover.hom := inferInstanceAs (LocallyOfFiniteType f)
  refine Set.Finite.of_finite_fibers imageComponent (s := irreducibleComponents XK)
    (hX.subset ?_) ?_
  · rintro T ⟨Z, hZ, rfl⟩
    exact mapsTo_irreducibleComponents_baseChange k K X f hZ
  rintro T ⟨W, hW, rfl⟩
  let Tcomp : irreducibleComponents X :=
    ⟨p.base '' W, mapsTo_irreducibleComponents_baseChange k K X f hW⟩
  obtain ⟨s, hsne, hdecomp, horbit⟩ :=
    exists_finite_single_orbit_decomposition (k := k) (K := K) Xover Tcomp
  have hdecomp' : p.base ⁻¹' (Tcomp : Set X) = ⋃ V ∈ s, V.1 := by
    simpa [p, Xover] using hdecomp
  let sSet : Finset (Set XK) := s.attach.image fun V => V.1.1
  have hsSet : ((sSet : Finset (Set XK)) : Set (Set XK)).Finite := sSet.finite_toSet
  apply hsSet.subset
  rintro Z ⟨hZcomp, hZT⟩
  have hZT' : p.base '' Z = p.base '' W := by
    simpa [imageComponent] using hZT
  have hZsub : Z ⊆ p.base ⁻¹' (Tcomp : Set X) := by
    intro x hx
    change p.base x ∈ p.base '' W
    rw [← hZT']
    exact ⟨x, hx, rfl⟩
  have hZsUnion : Z ⊆ ⋃₀ (sSet : Set (Set XK)) := by
    intro x hx
    have hxT := hZsub hx
    rw [hdecomp'] at hxT
    obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.mp hxT
    exact Set.mem_sUnion_of_mem hxV <| Finset.mem_image.mpr
      ⟨⟨V, hV⟩, Finset.mem_attach _ _, rfl⟩
  have hsSetComp : (sSet : Set (Set XK)) ⊆ irreducibleComponents XK := by
    intro V hV
    obtain ⟨V', -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hV)
    exact V'.1.2
  exact mem_of_subset_sUnion_irreducibleComponents
    Z hZcomp (sSet : Set (Set XK)) hsSet hsSetComp hZsUnion

/-- Let `E₀ ≤ E` be intermediate fields of `K / k`, and `q : X_K ⟶ X_E` the base change map.
If a subset `Z_K ⊆ X_K` is the preimage of a subset of `X_{E₀}` and maps onto `Z ⊆ X_E`, then
`Z_K = q⁻¹(Z)`. -/
public theorem preimage_eq_of_le_of_preimage_eq
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {E₀ E : IntermediateField k K} (hE : E₀ ≤ E)
    (p₀ : pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k K))) ⟶
      pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k E₀))))
    (hp₁ : p₀ ≫ pullback.fst f (Spec.map (ofHom (algebraMap k E₀))) =
      pullback.fst f (Spec.map (ofHom (algebraMap k K))))
    (hp₂ : p₀ ≫ pullback.snd f (Spec.map (ofHom (algebraMap k E₀))) =
      pullback.snd f (Spec.map (ofHom (algebraMap k K))) ≫ Spec.map (ofHom E₀.val))
    (T : Set (pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k E₀)))))
    (ZK : Set (pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k K)))))
    (hp₃ : p₀.base ⁻¹' T = ZK)
    (q : pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k K))) ⟶
      pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k E)))) [Surjective q]
    (hq₁ : q ≫ pullback.fst f (Spec.map (ofHom (algebraMap k E))) =
      pullback.fst f (Spec.map (ofHom (algebraMap k K))))
    (hq₂ : q ≫ pullback.snd f (Spec.map (ofHom (algebraMap k E))) =
      pullback.snd f (Spec.map (ofHom (algebraMap k K))) ≫ Spec.map (ofHom (algebraMap E K)))
    (Z : Set (pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k E)))))
    (hZ : q.base '' ZK = Z) :
    q.base ⁻¹' Z = ZK := by
  let gK := Spec.map (ofHom (algebraMap k K))
  let gE := Spec.map (ofHom (algebraMap k E))
  let g0 := Spec.map (ofHom (algebraMap k E₀))
  let c := Spec.map (ofHom (algebraMap E K))
  let c0 := Spec.map (ofHom (IntermediateField.inclusion hE).toRingHom)
  have hc0g0 : c0 ≫ g0 = gE := (Spec.map_comp _ _).symm
  let r0 := pullback.map f gE f g0
    (𝟙 X) c0 (𝟙 (Spec (.of k))) (by simp) (by rw [Category.comp_id, hc0g0])
  have hc0k : c ≫ c0 = Spec.map (ofHom E₀.val) := (Spec.map_comp _ _).symm
  have hpFactor : p₀ = q ≫ r0 := by
    apply pullback.hom_ext
    · calc
        p₀ ≫ pullback.fst f g0 = pullback.fst f gK := hp₁
        _ = q ≫ pullback.fst f gE := hq₁.symm
        _ = q ≫ r0 ≫ pullback.fst f g0 := by
          simp only [r0, pullback.map, pullback.lift_fst, Category.comp_id]
    · calc
        p₀ ≫ pullback.snd f g0 = pullback.snd f gK ≫ Spec.map (ofHom E₀.val) := hp₂
        _ = q ≫ pullback.snd f gE ≫ c0 := by
          rw [← hc0k, ← Category.assoc, ← hq₂, Category.assoc]
        _ = q ≫ r0 ≫ pullback.snd f g0 := by
          simp only [r0, pullback.map, pullback.lift_snd, Category.comp_id]
  have hh : q.base ⁻¹' (r0.base ⁻¹' T) = ZK := by
    calc
      _ = (q.base ≫ r0.base) ⁻¹' T := rfl
      _ = p₀.base ⁻¹' T := by rw [← Scheme.Hom.comp_base, hpFactor]
      _ = ZK := hp₃
  have hu : r0.base ⁻¹' T = Z := by
    rw [← hZ, ← hh, Set.image_preimage_eq _ q.surjective]
  rwa [hu] at hh

/-- Let `E` be an intermediate field of a separable closure `K / k` containing a field of
definition of every irreducible component of `X_K`. Then every irreducible component of `X_E` is
geometrically irreducible. -/
public theorem geometricallyIrreducible_irreducibleComponents_of_forall_le
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (E : IntermediateField k K)
    (hE : ∀ ZK : irreducibleComponents
        (pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k K)))),
      ∃ (E₀ : IntermediateField k K) (_ : E₀ ≤ E)
        (T : irreducibleComponents
          (pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k E₀)))))
        (p : pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k K))) ⟶
          pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k E₀)))),
        p ≫ pullback.fst f (Spec.map (ofHom (algebraMap k E₀))) =
            pullback.fst f (Spec.map (ofHom (algebraMap k K))) ∧
          p ≫ pullback.snd f (Spec.map (ofHom (algebraMap k E₀))) =
            pullback.snd f (Spec.map (ofHom (algebraMap k K))) ≫ Spec.map (ofHom E₀.val) ∧
          p.base ⁻¹' (T : Set _) = (ZK : Set _))
    (Z : irreducibleComponents (pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k E))))) :
    GeometricallyIrreducible
      ((Scheme.IdealSheafData.vanishingIdeal
          (X := pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k E))))
          ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩).subschemeι ≫
        pullback.snd f (Spec.map (ofHom (algebraMap k E)))) := by
  let gK := Spec.map (ofHom (algebraMap k K))
  let XK := pullback f gK
  let gE := Spec.map (ofHom (algebraMap k E))
  let XE := pullback f gE
  let r := pullback.snd f gE
  let c := Spec.map (ofHom (algebraMap E K))
  have hcomp : gK = c ≫ gE := by
    rw [← Spec.map_comp]
    congr 1
  let Q : Scheme.{u} := pullback r c
  let eQ : Q ≅ XK := baseChangeTowerIsoTo f gE c gK hcomp
  let q : XK ⟶ XE := eQ.inv ≫ pullback.fst r c
  have heQq : eQ.hom ≫ q = pullback.fst r c := eQ.hom_inv_id_assoc _
  have : IsSepClosure E K := isSepClosure_of_intermediateField E
  obtain ⟨W, hW, hWT⟩ := surjOn_irreducibleComponents_baseChange E K XE r Z.2
  let ZK : irreducibleComponents XK :=
    ⟨eQ.hom.base '' (W : Set Q), image_mem_irreducibleComponents_of_iso eQ hW⟩
  have hqImage : q.base '' (ZK : Set XK) = Z.1 := by
    change q.base '' (eQ.hom.base '' (W : Set Q)) = Z.1
    have hfun : (fun x : Q => q.base (eQ.hom.base x)) = (pullback.fst r c).base := by
      funext x
      simpa [Scheme.Hom.comp_base, TopCat.coe_comp] using
        congrArg (fun m : Q ⟶ XE => m.base x) heQq
    rwa [Set.image_image, hfun]
  have : Surjective c := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap E K))).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance) |>.2
  have : Surjective (pullback.fst r c) := inferInstance
  have : Surjective q := by
    dsimp [q]
    infer_instance
  have heQfst : eQ.hom ≫ pullback.fst f gK = pullback.fst r c ≫ pullback.fst f gE :=
    baseChangeTowerIsoTo_hom_fst f gE c gK hcomp
  have heQsnd : eQ.hom ≫ pullback.snd f gK = pullback.snd r c :=
    baseChangeTowerIsoTo_hom_snd f gE c gK hcomp
  have hqfst : q ≫ pullback.fst f gE = pullback.fst f gK := by
    apply (cancel_epi eQ.hom).1
    simpa only [q, Category.assoc, eQ.hom_inv_id_assoc] using heQfst.symm
  have hqsnd : q ≫ r = pullback.snd f gK ≫ c := by
    apply (cancel_epi eQ.hom).1
    simp only [q, Category.assoc, eQ.hom_inv_id_assoc, pullback.condition]
    simpa only [Category.assoc] using congrArg (fun t => t ≫ c) heQsnd.symm
  obtain ⟨E₀, hE₀, T, p₀, hp₁, hp₂, hp₃⟩ := hE ZK
  have hpre := preimage_eq_of_le_of_preimage_eq f hE₀ p₀ hp₁ hp₂ _ _ hp₃ q hqfst hqsnd _ hqImage
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ : Closeds XE)
  have hirange : Set.range I.subschemeι.base = Z.1 := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  exact geometricallyIrreducible_of_closed_pullback E K I.subscheme XE XK
    (I.subschemeι ≫ r) I.subschemeι q ZK.1 ZK.2.1 (by simpa [hirange] using hpre)
    (componentBaseChangeIso f gE c I.subschemeι eQ q heQq)

/-- **Stacks Project, Tag 054R.** After a finite separable extension of the ground field, every
irreducible component of a scheme locally of finite type over a field is geometrically
irreducible, provided that the original scheme has only finitely many irreducible components. -/
@[stacks 054R]
public theorem exists_finite_separable_extension_geometricallyIrreducible_components
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (hX : (irreducibleComponents X).Finite) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k') (_ : Algebra.IsSeparable k k'),
      let X' := pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k k')))
      ∀ Z : irreducibleComponents X',
        GeometricallyIrreducible
          ((Scheme.IdealSheafData.vanishingIdeal (X := X')
              ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩).subschemeι ≫
            pullback.snd f (Spec.map (ofHom (algebraMap k k')))) := by
  classical
  let K := SeparableClosure k
  let XK := pullback (C := Scheme.{u}) f (Spec.map (ofHom (algebraMap k K)))
  have : Finite (irreducibleComponents XK) :=
    (finite_irreducibleComponents_baseChange_of_isSepClosure k K X f hX).to_subtype
  choose E₀ hE₀ T₀ p₀ hp₀₁ hp₀₂ hp₀₃ using
    fun Z : irreducibleComponents XK =>
      exists_finite_subextension_defining_component (k := k) (K := K) X f Z
  let E : IntermediateField k K := ⨆ Z, E₀ Z
  have : ∀ Z : irreducibleComponents XK, FiniteDimensional k (E₀ Z) := hE₀
  have : FiniteDimensional k E := IntermediateField.finiteDimensional_iSup_of_finite
  have : ∀ Z : irreducibleComponents XK, Algebra.IsSeparable k (E₀ Z) := fun Z =>
    Algebra.isSeparable_tower_bot_of_isSeparable k (E₀ Z) K
  have : Algebra.IsSeparable k E := inferInstance
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact geometricallyIrreducible_irreducibleComponents_of_forall_le X f E fun ZK =>
    ⟨E₀ ZK, le_iSup E₀ ZK, T₀ ZK, p₀ ZK, hp₀₁ ZK, hp₀₂ ZK, hp₀₃ ZK⟩

end AlgebraicGeometry

end
