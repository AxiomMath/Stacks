module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Jacobson.Artinian
public import Mathlib.RingTheory.Unramified.Field
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.RingTheory.AbsolutelyFlat.Basic
public import StacksFrontier.RingTheory.WeaklyEtale.Basic
public import StacksFrontier.RingTheory.WeaklyEtale.Descent
public import StacksFrontier.RingTheory.WeaklyEtale.FormallyUnramified

@[expose] public section

/-!
# Weakly étale algebras over a field

Let `K` be a field. For a `K`-algebra `B`, flatness of the multiplication map
`B ⊗[K] B → B` is already equivalent to weak étaleness, and to `B` being a filtered colimit of
étale `K`-algebras; under these conditions every finitely generated `K`-subalgebra of `B` is
étale. The starting point is the case of a field extension `L/K`: flatness of its
multiplication map `L ⊗[K] L → L` forces `L/K` to be algebraic and separable. Consequently a
weakly étale algebra over a field is reduced and integral, its finitely generated subalgebras
are finite products of finite separable field extensions, and having no nontrivial idempotents
characterizes being a field or the zero ring. Weak étaleness over `K` is inherited by
subalgebras and quotient algebras, and is preserved by tensor products over `K`.

## Main definitions

No new definitions are introduced.

## Main results

* `isSeparable_of_flat_lmul` (Stacks 092P): flatness of the multiplication map of a field
  extension implies that the extension is algebraic and separable.
* `flat_lmul_weaklyEtale_filteredColimitEtale_tfae` (Stacks 092Q): for an algebra over a
  field, flatness of the multiplication map, weak étaleness and being a filtered colimit of
  étale algebras are equivalent, and under these conditions every finitely generated
  subalgebra is étale.
* `structure_of_weaklyEtale_over_field` (Stacks 0CKR): the structure and closure properties of
  a weakly étale algebra over a field.

## Implementation notes

The multiplication map is `Algebra.TensorProduct.lmul' K`. Mathlib's
`Algebra.IsSeparable K L` expresses that every element of `L` is algebraic over `K` with
separable minimal polynomial, so it includes both parts of the conclusion of Stacks 092P.

A filtered-colimit presentation is expressed by a filtered diagram in `CommAlgCat K`, a
colimit cocone, and an isomorphism from its apex to the given algebra. Finite generation of a
subalgebra is expressed by `Subalgebra.FG`. The colimit presentation used for the forward
direction of Stacks 092Q is the diagram of subalgebras `Algebra.adjoin K S` indexed by the
finite subsets `S` of the algebra; it is colimiting because those subalgebras are directed
with supremum `⊤`.

A finite product of finite separable extensions is expressed by a finite type `ι`, a family of
field extensions indexed by `ι`, and a `K`-algebra equivalence with their dependent product.
Quotient algebras are expressed by surjective `K`-algebra homomorphisms. Since commutative
rings may be trivial, the empty product is included in the idempotent characterization as the
zero ring.

Since the three groups of results use incompatible `open` directives, each is kept in its own
section: `SeparableExtension`, `WeaklyEtaleTFAE` and `StructureOverField`.

## References

* [The Stacks Project, Tag 092P](https://stacks.math.columbia.edu/tag/092P)
* [The Stacks Project, Tag 092Q](https://stacks.math.columbia.edu/tag/092Q)
* [The Stacks Project, Tag 0CKR](https://stacks.math.columbia.edu/tag/0CKR)
* [Olivier, *Anneaux absolument plats universels et épimorphismes à buts réduits*][Olivier-AF]
-/

universe u v w

section SeparableExtension

/-- Let `L/K` be a field extension. If the multiplication map `L ⊗[K] L → L` is flat,
then `L/K` is algebraic and separable. -/
@[stacks 092P]
theorem isSeparable_of_flat_lmul (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L]
    (h : (Algebra.TensorProduct.lmul' K (S := L)).Flat) :
    Algebra.IsSeparable K L := by
  rw [Algebra.isSeparable_def]
  intro x
  let E : IntermediateField K L := IntermediateField.adjoin K {x}
  have : Algebra.EssFiniteType K E := IntermediateField.essFiniteType_iff.mpr
    (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x))
  have hsepE : Algebra.IsSeparable K E :=
    (Algebra.FormallyUnramified.iff_isSeparable (K := K) E).mp <|
      formallyUnramified_of_flat_lmul K E ((flat_lmul'_and_weaklyEtale_of_faithfullyFlat K E L).1 h)
  exact ((hsepE.isSeparable K ⟨x, IntermediateField.subset_adjoin K {x} (Set.mem_singleton x)⟩
    ).map E.val Subtype.val_injective :)

end SeparableExtension

section WeaklyEtaleTFAE

open CategoryTheory CategoryTheory.Limits

section Colimit

variable (K : Type u) (B : Type v) [CommRing K] [CommRing B] [Algebra K B]

private abbrev finiteAdjoin (S : Finset B) : Subalgebra K B :=
  Algebra.adjoin K (S : Set B)

private def finiteAdjoinDiagram : Finset B ⥤ CommAlgCat.{v} K where
  obj S := CommAlgCat.of K (finiteAdjoin K B S)
  map {S T} f := CommAlgCat.ofHom <|
    Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr f.le))
  map_id := by
    intro S
    apply CommAlgCat.hom_ext
    ext x
    rfl
  map_comp := by
    intro S T U f g
    apply CommAlgCat.hom_ext
    ext x
    rfl

private def finiteAdjoinCocone : Cocone (finiteAdjoinDiagram K B) where
  pt := CommAlgCat.of K B
  ι := {
    app := fun S => CommAlgCat.ofHom (Subalgebra.val (finiteAdjoin K B S))
    naturality := by
      intro S T f
      apply CommAlgCat.hom_ext
      ext x
      rfl }

private theorem finiteAdjoin_sup : ⨆ S : Finset B, finiteAdjoin K B S = ⊤ := by
  classical
  exact top_unique fun b _ =>
    le_iSup (finiteAdjoin K B) {b} (Algebra.subset_adjoin (Finset.mem_singleton_self b))

private theorem finiteAdjoin_directed :
    Directed (· ≤ ·) (finiteAdjoin K B) := by
  classical
  intro S T
  refine ⟨S ∪ T, ?_, ?_⟩
  · exact Algebra.adjoin_mono (Finset.coe_subset.mpr Finset.subset_union_left)
  · exact Algebra.adjoin_mono (Finset.coe_subset.mpr Finset.subset_union_right)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def finiteAdjoinIsColimit : IsColimit (finiteAdjoinCocone K B) := by
  classical
  let A := finiteAdjoin K B
  let F := finiteAdjoinDiagram K B
  let c := finiteAdjoinCocone K B
  have hdir : Directed (· ≤ ·) A := finiteAdjoin_directed K B
  have hsup : ⨆ S, A S = ⊤ := finiteAdjoin_sup K B
  let leg (s : Cocone F) (S : Finset B) : A S →ₐ[K] s.pt := (s.ι.app S).hom
  have hcompat (s : Cocone F) (S T : Finset B) (h : A S ≤ A T) :
      leg s S = (leg s T).comp (Subalgebra.inclusion h) := by
    ext x
    change (ConcreteCategory.hom (s.ι.app S)) x =
      (ConcreteCategory.hom (s.ι.app T)) (Subalgebra.inclusion h x)
    let U := S ∪ T
    have hSU : S ≤ U := Finset.subset_union_left
    have hTU : T ≤ U := Finset.subset_union_right
    have hSTU : (Subalgebra.inclusion (Algebra.adjoin_mono
        (Finset.coe_subset.mpr hSU)) : A S →ₐ[K] A U) =
        (Subalgebra.inclusion (Algebra.adjoin_mono
          (Finset.coe_subset.mpr hTU))).comp (Subalgebra.inclusion h) := by
      ext y
      rfl
    have hs0 : F.map (homOfLE hSU) ≫ s.ι.app U = s.ι.app S := by
      simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        using s.ι.naturality (homOfLE hSU)
    have ht0 : F.map (homOfLE hTU) ≫ s.ι.app U = s.ι.app T := by
      simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        using s.ι.naturality (homOfLE hTU)
    have hs := congrArg (fun f : F.obj S ⟶ s.pt => f x) hs0
    have ht := congrArg (fun f : F.obj T ⟶ s.pt => f (Subalgebra.inclusion h x)) ht0
    simpa [F, finiteAdjoinDiagram, CommAlgCat.comp_apply, hSTU] using hs.symm.trans ht
  let desc (s : Cocone F) : B →ₐ[K] s.pt :=
    (Subalgebra.iSupLift A hdir (leg s) (hcompat s) ⊤
      (le_of_eq hsup.symm)).comp (Subalgebra.topEquiv).symm.toAlgHom
  have desc_val (s : Cocone F) (S : Finset B) (x : A S) :
      desc s (x : B) = leg s S x := by
    change (Subalgebra.iSupLift A hdir (leg s) (hcompat s) ⊤
      (le_of_eq hsup.symm)) ((Subalgebra.topEquiv).symm (x : B)) = leg s S x
    exact Subalgebra.iSupLift_mk (T := ⊤) (hT := le_of_eq hsup.symm) A x
      Algebra.mem_top
  refine IsColimit.mk (fun s => CommAlgCat.ofHom (desc s)) (fun s S => ?_)
    (fun s m hm => ?_)
  · apply CommAlgCat.hom_ext
    ext x
    exact desc_val s S x
  · apply CommAlgCat.hom_ext
    ext b
    let S : Finset B := {b}
    have hb : b ∈ A S := by
      change b ∈ Algebra.adjoin K (↑S : Set B)
      exact Algebra.subset_adjoin (Finset.mem_singleton_self b)
    let x : A S := ⟨b, hb⟩
    have h := congrArg (fun f : F.obj S ⟶ s.pt => f x) (hm S)
    change (c.ι.app S ≫ m) x = s.ι.app S x at h
    rw [CommAlgCat.comp_apply] at h
    change m b = s.ι.app S x at h
    exact h.trans (desc_val s S x).symm

end Colimit

section FieldLocalizations

variable (K : Type u) (B : Type v) [Field K] [CommRing B] [Algebra K B]

private theorem weaklyEtale_of_flat_lmul
    (hμ : (Algebra.TensorProduct.lmul' K (S := B)).Flat) :
    Algebra.WeaklyEtale K B :=
  (Algebra.weaklyEtale_iff K B).2 ⟨RingHom.flat_algebraMap_iff.1
    (RingHom.Flat.of_isField (Field.toIsField K) (algebraMap K B)), hμ⟩

private theorem localization_isField
    (hμ : (Algebra.TensorProduct.lmul' K (S := B)).Flat)
    (q : Ideal B) [q.IsPrime] : IsField (Localization.AtPrime q) := by
  have hB := (absolutelyFlat_and_isReduced_of_flat_lmul' K B hμ).1 fun _ _ _ => inferInstance
  have hiff :
      (∀ (N : Type v) [AddCommGroup N] [Module B N], Module.Flat B N) ↔
        ∀ (p : Ideal B) [p.IsPrime], IsField (Localization.AtPrime p) :=
    (forall_flat_tfae B).out 1 3
  exact (hiff.mp hB) q

set_option backward.isDefEq.respectTransparency false in
private theorem localization_isSeparable
    (hμ : (Algebra.TensorProduct.lmul' K (S := B)).Flat)
    (q : Ideal B) [q.IsPrime] : Algebra.IsSeparable K (Localization.AtPrime q) := by
  have : Algebra.WeaklyEtale K B := weaklyEtale_of_flat_lmul K B hμ
  have : Algebra.WeaklyEtale B (Localization.AtPrime q) :=
    (weaklyEtale_of_isLocalization_etale_filteredColimit.{v, v, v} B).1
      (Localization.AtPrime q) q.primeCompl
  have : Algebra.WeaklyEtale K (Localization.AtPrime q) :=
    Algebra.WeaklyEtale.trans K B (Localization.AtPrime q)
  let : Field (Localization.AtPrime q) :=
    (localization_isField K B hμ q).toField
  exact isSeparable_of_flat_lmul K (Localization.AtPrime q)
    (Algebra.WeaklyEtale.flat_lmul' K (Localization.AtPrime q))

private theorem ker_localization_atPrime
    (hμ : (Algebra.TensorProduct.lmul' K (S := B)).Flat)
    (q : Ideal B) [q.IsPrime] :
    RingHom.ker (algebraMap B (Localization.AtPrime q)) = q := by
  let : Field (Localization.AtPrime q) :=
    (localization_isField K B hμ q).toField
  ext x
  change (algebraMap B (Localization.AtPrime q)) x = 0 ↔ x ∈ q
  simpa [IsLocalRing.maximalIdeal_eq_bot] using
    IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q x

end FieldLocalizations

section FiniteSubalgebras

variable (K : Type u) (B : Type v) [Field K] [CommRing B] [Algebra K B]

private theorem minimalPrime_isMaximal_and_isSeparable
    (hμ : (Algebra.TensorProduct.lmul' K (S := B)).Flat)
    (A : Subalgebra K B) (p : Ideal A) (hp : p ∈ minimalPrimes A) :
    p.IsMaximal ∧ Algebra.IsSeparable K (A ⧸ p) := by
  obtain ⟨q, hq, hqp⟩ :=
    Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective
      (f := (A.val : A →+* B)) Subtype.val_injective p hp
  have : q.IsPrime := hq
  let : Field (Localization.AtPrime q) :=
    (localization_isField K B hμ q).toField
  let f : A →ₐ[K] Localization.AtPrime q :=
    (IsScalarTower.toAlgHom K B (Localization.AtPrime q)).comp A.val
  have hfker : RingHom.ker (f : A →+* Localization.AtPrime q) = p := by
    ext x
    change (algebraMap B (Localization.AtPrime q)) (x : B) = 0 ↔ x ∈ p
    rw [← hqp]
    change (algebraMap B (Localization.AtPrime q)) (x : B) = 0 ↔
      (A.val x) ∈ q
    simpa only [Subalgebra.val_apply, RingHom.mem_ker] using
      (congrArg (fun I : Ideal B => (x : B) ∈ I)
        (ker_localization_atPrime K B hμ q)).to_iff
  let g : A ⧸ p →ₐ[K] Localization.AtPrime q :=
    Ideal.Quotient.liftₐ p f (by
      intro x hx
      exact (RingHom.mem_ker).mp (hfker.symm ▸ hx))
  have hg : Function.Injective g := by
    change Function.Injective (Ideal.Quotient.lift p (f : A →+* Localization.AtPrime q) _)
    exact RingHom.lift_injective_of_ker_le_ideal p _ (le_of_eq hfker)
  have : Algebra.IsSeparable K (Localization.AtPrime q) :=
    localization_isSeparable K B hμ q
  have hsep : Algebra.IsSeparable K (A ⧸ p) :=
    ⟨fun x => (isSeparable_map_iff g hg).mp (Algebra.IsSeparable.isSeparable K (g x))⟩
  have : Algebra.IsIntegral K (Localization.AtPrime q) := ⟨Algebra.IsSeparable.isIntegral K⟩
  have : Algebra.IsIntegral K (A ⧸ p) := Algebra.IsIntegral.of_injective g hg
  have : p.IsPrime := hp.isPrime
  exact ⟨(Ideal.Quotient.maximal_ideal_iff_isField_quotient p).2
    (isField_of_isIntegral_of_isField' (Field.toIsField K)), hsep⟩

private theorem finiteSubalgebra_etale
    (hμ : (Algebra.TensorProduct.lmul' K (S := B)).Flat)
    (A : Subalgebra K B) (hA : A.FG) : Algebra.Etale K A := by
  classical
  have : Algebra.FiniteType K A := (Subalgebra.fg_iff_finiteType A).mp hA
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have : IsReduced B :=
    (absolutelyFlat_and_isReduced_of_flat_lmul' K B hμ).2
      (inferInstance : IsReduced K) (weaklyEtale_of_flat_lmul K B hμ)
  have : IsReduced A := isReduced_of_injective A.val Subtype.val_injective
  have hdim : Ring.KrullDimLE 0 A :=
    (Ring.krullDimLE_zero_iff_forall_minimalPrimes_isMaximal).2
      (fun p hp => (minimalPrime_isMaximal_and_isSeparable K B hμ A p hp).1)
  have : IsArtinianRing A :=
    (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero).2 ⟨inferInstance, hdim⟩
  apply (Algebra.Etale.iff_exists_algEquiv_prod K A).2
  refine ⟨MaximalSpectrum A, inferInstance, (fun m => A ⧸ m.asIdeal),
    (fun m => Ideal.Quotient.field m.asIdeal), (fun m => inferInstance),
    (IsArtinianRing.equivPi A).restrictScalars K, ?_⟩
  intro m
  let : Field (A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  have hm : m.asIdeal ∈ minimalPrimes A :=
    IsArtinianRing.mem_minimalPrimes bot_le
  exact ⟨finite_of_finite_type_of_isJacobsonRing K (A ⧸ m.asIdeal),
    (minimalPrime_isMaximal_and_isSeparable K B hμ A m.asIdeal hm).2⟩

end FiniteSubalgebras

section ColimitEtale

variable (K : Type u) (B : Type v) [Field K] [CommRing B] [Algebra K B]

private theorem weaklyEtale_of_filteredColimitEtale
    (J : Type v) [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{v} K) (c : Cocone F) (hc : IsColimit c)
    (e : c.pt ≅ CommAlgCat.of K B)
    (het : ∀ j, Algebra.Etale K (F.obj j)) : Algebra.WeaklyEtale K B := by
  let d : Cocone F :=
    { pt := CommAlgCat.of K B
      ι :=
        { app := fun j => c.ι.app j ≫ e.hom
          naturality := by
            intro j k f
            simpa only [Functor.const_obj_obj, Functor.const_obj_map,
              Category.comp_id, Category.assoc] using
                congrArg (fun g => g ≫ e.hom) (c.ι.naturality f) } }
  let ed : c ≅ d := Cocone.ext e fun _ => rfl
  exact (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, v, v}
    K).2.2 J F d (hc.ofIsoColimit ed) fun j => have := het j; inferInstance

end ColimitEtale

/-- Let `B` be an algebra over a field `K`. The following are equivalent: the multiplication
map `B ⊗[K] B → B` is flat; `B` is weakly étale over `K`; and `B` is a filtered colimit of
étale `K`-algebras. Under these equivalent conditions, every finitely generated
`K`-subalgebra of `B` is étale over `K`. -/
@[stacks 092Q]
theorem flat_lmul_weaklyEtale_filteredColimitEtale_tfae
    (K : Type u) (B : Type v) [Field K] [CommRing B] [Algebra K B] :
    [ (Algebra.TensorProduct.lmul' K (S := B)).Flat,
      Algebra.WeaklyEtale K B,
      ∃ (J : Type v) (_ : SmallCategory J) (_ : IsFiltered J)
        (F : J ⥤ CommAlgCat.{v} K) (c : Cocone F) (_ : IsColimit c),
        Nonempty (c.pt ≅ CommAlgCat.of K B) ∧ ∀ j, Algebra.Etale K (F.obj j) ].TFAE ∧
      ((Algebra.TensorProduct.lmul' K (S := B)).Flat →
        ∀ A : Subalgebra K B, A.FG → Algebra.Etale K A) := by
  refine ⟨?_, finiteSubalgebra_etale K B⟩
  tfae_have 1 → 2 := weaklyEtale_of_flat_lmul K B
  tfae_have 2 → 1 := fun h => h.flat_lmul'
  tfae_have 1 → 3 := fun hμ => ⟨Finset B, inferInstance, inferInstance,
    finiteAdjoinDiagram K B, finiteAdjoinCocone K B, finiteAdjoinIsColimit K B, ⟨Iso.refl _⟩,
    fun S => finiteSubalgebra_etale K B hμ _ (Subalgebra.fg_adjoin_finset S)⟩
  tfae_have 3 → 2 := by
    rintro ⟨J, _, _, F, c, hc, ⟨e⟩, het⟩
    exact weaklyEtale_of_filteredColimitEtale K B J F c hc e het
  tfae_finish

end WeaklyEtaleTFAE

section StructureOverField

open CategoryTheory CategoryTheory.Limits TensorProduct

private lemma weaklyEtale_of_fg_etale
    (K : Type u) (C : Type v) [Field K] [CommRing C] [Algebra K C]
    (h : ∀ A : Subalgebra K C, A.FG → Algebra.Etale K A) :
    Algebra.WeaklyEtale K C := by
  apply ((flat_lmul_weaklyEtale_filteredColimitEtale_tfae K C).1.out 3 2).mp
  exact ⟨Finset C, inferInstance, inferInstance, finiteAdjoinDiagram K C, finiteAdjoinCocone K C,
    finiteAdjoinIsColimit K C, ⟨Iso.refl _⟩, fun S ↦ h _ (Subalgebra.fg_adjoin_finset S)⟩

private lemma fg_subalgebra_etale
    (K : Type u) (B : Type v) [Field K] [CommRing B] [Algebra K B]
    (hB : Algebra.WeaklyEtale K B) :
    ∀ A : Subalgebra K B, A.FG → Algebra.Etale K A :=
  (flat_lmul_weaklyEtale_filteredColimitEtale_tfae K B).2 hB.flat_lmul'

private lemma fg_subalgebra_product
    (K : Type u) (B : Type v) [Field K] [CommRing B] [Algebra K B]
    (hB : Algebra.WeaklyEtale K B) :
    ∀ A : Subalgebra K B, A.FG →
      ∃ (ι : Type v) (_ : Finite ι) (L : ι → Type v) (_ : ∀ i, Field (L i))
        (_ : ∀ i, Algebra K (L i)) (_ : A ≃ₐ[K] ∀ i, L i),
        ∀ i, Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i) :=
  fun A hA ↦ (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := A)).mp
    (fg_subalgebra_etale K B hB A hA)

private lemma ideal_isIdempotentElem_pi_fields {ι : Type v} [Finite ι]
    (L : ι → Type v) [∀ i, Field (L i)] (I : Ideal (∀ i, L i)) :
    IsIdempotentElem I := by
  classical
  rw [Ideal.isIdempotentElem_iff_of_fg I (IsNoetherian.noetherian I)]
  let e : ∀ i, L i := fun i => if (Ideal.piOrderIso I) i = ⊤ then 1 else 0
  refine ⟨e, ?_, ?_⟩
  · ext i
    simp [e]
  · apply Ideal.piOrderIso.injective
    funext i
    change (Ideal.piOrderIso I) i = (Ideal.piOrderIso ((∀ i, L i) ∙ e)) i
    change I.map (Pi.evalRingHom L i) =
      ((Ideal.span {e} : Ideal (∀ i, L i)).map (Pi.evalRingHom L i))
    rw [Ideal.map_span]
    by_cases hi : (Ideal.piOrderIso I) i = ⊤
    · have he : e i = 1 := ite_eq_left hi
      change I.map (Pi.evalRingHom L i) = ⊤ at hi
      rw [hi, Set.image_singleton]
      change (⊤ : Ideal (L i)) = Ideal.span {e i}
      rw [he, Ideal.span_singleton_one]
    · have hi' : (Ideal.piOrderIso I) i = ⊥ :=
        (Ideal.eq_bot_or_top ((Ideal.piOrderIso I) i)).resolve_right hi
      change I.map (Pi.evalRingHom L i) = ⊥ at hi'
      rw [hi', Set.image_singleton]
      change (⊥ : Ideal (L i)) = Ideal.span {e i}
      have he : e i = 0 := ite_eq_right hi
      rw [he, Ideal.span_singleton_zero]

private lemma etale_of_surjective_of_etale
    (K : Type u) {A : Type v} {C : Type w} [Field K] [CommRing A] [CommRing C]
    [Algebra K A] [Algebra K C] [Algebra.Etale K A]
    (f : A →ₐ[K] C) (hf : Function.Surjective f) : Algebra.Etale K C := by
  obtain ⟨ι, _, L, _, _, ψ, hL⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := A)).mp inferInstance
  let g : (∀ i, L i) →ₐ[K] C := f.comp ψ.symm.toAlgHom
  have hg : Function.Surjective g := hf.comp ψ.symm.surjective
  let := g.toAlgebra
  have hformal : Algebra.FormallyEtale (∀ i, L i) C :=
    (Algebra.FormallyEtale.iff_of_surjective hg).2 (ideal_isIdempotentElem_pi_fields L _)
  have : Algebra.FinitePresentation (∀ i, L i) C := by
    rw [← RingHom.finitePresentation_algebraMap]
    exact RingHom.FinitePresentation.of_surjective g.toRingHom hg
      (IsNoetherian.noetherian (RingHom.ker g.toRingHom))
  have : Algebra.Etale (∀ i, L i) C := ⟨hformal, inferInstance⟩
  have : Algebra.Etale K (∀ i, L i) := Algebra.Etale.of_equiv ψ
  have : IsScalarTower K (∀ i, L i) C := .of_algebraMap_eq' g.comp_algebraMap.symm
  exact Algebra.Etale.comp K (∀ i, L i) C

/-- If all finitely generated subalgebras are étale, every element lies in an étale subalgebra. -/
private lemma exists_etale_subalgebra_mem
    (K : Type u) (B : Type v) [Field K] [CommRing B] [Algebra K B]
    (h : ∀ A : Subalgebra K B, A.FG → Algebra.Etale K A) (x : B) :
    ∃ A : Subalgebra K B, Algebra.Etale K A ∧ x ∈ A :=
  ⟨Algebra.adjoin K {x}, h _ ⟨{x}, by simp⟩, Algebra.self_mem_adjoin_singleton K x⟩

private lemma exists_mul_mul_eq_self_of_fg_etale
    (K : Type u) (B : Type v) [Field K] [CommRing B] [Algebra K B]
    (h : ∀ A : Subalgebra K B, A.FG → Algebra.Etale K A) (x : B) :
    ∃ y : B, x * x * y = x := by
  classical
  obtain ⟨A, _, hxA⟩ := exists_etale_subalgebra_mem K B h x
  obtain ⟨ι, _, L, _, _, ψ, _⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := A)).mp inferInstance
  let a : A := ⟨x, hxA⟩
  let b : ∀ i, L i := fun i ↦ if ψ a i = 0 then 0 else (ψ a i)⁻¹
  have hab : a * a * ψ.symm b = a := by
    apply ψ.injective
    ext i
    simp only [map_mul, ψ.apply_symm_apply, Pi.mul_apply]
    by_cases hi : ψ a i = 0 <;> simp [b, hi]
  exact ⟨↑(ψ.symm b), congrArg Subtype.val hab⟩

private lemma isIntegral_of_weaklyEtale
    (K : Type u) (B : Type v) [Field K] [CommRing B] [Algebra K B]
    (hB : Algebra.WeaklyEtale K B) : Algebra.IsIntegral K B := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨A, _, hxA⟩ := exists_etale_subalgebra_mem K B (fg_subalgebra_etale K B hB) x
  have : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
  exact (IsIntegral.of_finite K (⟨x, hxA⟩ : A)).map A.val

private lemma weaklyEtale_subalgebra_of_weaklyEtale
    (K : Type u) (B : Type v) [Field K] [CommRing B] [Algebra K B]
    (hB : Algebra.WeaklyEtale K B) (S : Subalgebra K B) : Algebra.WeaklyEtale K S := by
  refine weaklyEtale_of_fg_etale K S fun T hT => ?_
  have : Algebra.Etale K (T.map S.val) := fg_subalgebra_etale K B hB _ (hT.map S.val)
  exact Algebra.Etale.of_equiv (T.equivMapOfInjective S.val Subtype.val_injective).symm

private lemma weaklyEtale_of_surjective_of_weaklyEtale
    (K : Type u) (B : Type v) [Field K] [CommRing B] [Algebra K B]
    (hB : Algebra.WeaklyEtale K B) {Q : Type w} [CommRing Q] [Algebra K Q]
    (f : B →ₐ[K] Q) (hf : Function.Surjective f) : Algebra.WeaklyEtale K Q := by
  classical
  apply weaklyEtale_of_fg_etale K Q
  rintro T ⟨s, hs⟩
  let g (q : Q) : B := Classical.choose (hf q)
  have hg (q : Q) : f (g q) = q := Classical.choose_spec (hf q)
  let t : Finset B := s.image g
  let A : Subalgebra K B := Algebra.adjoin K (↑t : Set B)
  have hmap : A.map f = T := by
    calc
      A.map f = Algebra.adjoin K (f '' (↑t : Set B)) := AlgHom.map_adjoin f _
      _ = Algebra.adjoin K (↑s : Set Q) := by
        rw [← Finset.coe_image]
        congr 1
        ext q
        simp [t, hg]
      _ = T := hs
  have : Algebra.Etale K A := fg_subalgebra_etale K B hB A (Subalgebra.fg_adjoin_finset t)
  rw [← hmap]
  exact etale_of_surjective_of_etale K (f.subalgebraMap A) (f.subalgebraMap_surjective A)

private lemma subsingleton_or_isField_iff_idempotent
    (K : Type u) (B : Type v) [Field K] [CommRing B] [Algebra K B]
    (hB : Algebra.WeaklyEtale K B) :
    (Subsingleton B ∨ IsField B) ↔ ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  classical
  constructor
  · rintro (hs | hf) e he
    · exact Or.inl (Subsingleton.elim e 0)
    · let : Field B := hf.toField
      have hz : e * (e - 1) = 0 := by
        change e * e = e at he
        linear_combination he
      exact (mul_eq_zero.mp hz).imp id sub_eq_zero.mp
  · intro hid
    by_cases hs : Subsingleton B
    · exact Or.inl hs
    right
    have : Nontrivial B := not_subsingleton_iff_nontrivial.mp hs
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {x} hx ↦ ?_⟩
    obtain ⟨y, hy⟩ := exists_mul_mul_eq_self_of_fg_etale K B (fg_subalgebra_etale K B hB) x
    have he : IsIdempotentElem (x * y) := by
      change (x * y) * (x * y) = x * y
      linear_combination y * hy
    rcases hid _ he with h0 | h1
    · exact (hx (by linear_combination x * h0 - hy)).elim
    · exact ⟨y, h1⟩

private lemma isSeparable_of_weaklyEtale_of_isField
    (K : Type u) (B : Type v) [Field K] [CommRing B] [Algebra K B]
    (hB : Algebra.WeaklyEtale K B) (hf : IsField B) : Algebra.IsSeparable K B := by
  let : Field B := hf.toField
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨A, _, hxA⟩ := exists_etale_subalgebra_mem K B (fg_subalgebra_etale K B hB) x
  have : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
  let : Field A := (IsField.of_isDomain_of_finite K A).toField
  have : Algebra.IsSeparable K A :=
    (Algebra.FormallyEtale.iff_isSeparable K A).mp inferInstance
  exact (Algebra.IsSeparable.isSeparable K (⟨x, hxA⟩ : A)).map A.val Subtype.val_injective

/-- A weakly étale algebra `B` over a field `K` is reduced and integral. Every finitely
generated `K`-subalgebra is a finite product of finite separable extensions of `K`. Moreover,
`B` is a field or the zero ring exactly when it has no nontrivial idempotents; if it is a field,
then it is a separable algebraic extension. Subalgebras and quotient algebras of `B` are weakly
étale over `K`, as is the tensor product of `B` with any weakly étale `K`-algebra. -/
@[stacks 0CKR,
  ega "IV 18.3.3" "partial",
  sga "1 IX 1.8" "decomposition direction",
  sga "4½ Arcata 2.1.2" "partial",
  sga "4½ Arcata 2.4.2" "more general"]
theorem structure_of_weaklyEtale_over_field
    (K : Type u) (B : Type v) [Field K] [CommRing B] [Algebra K B]
    (hB : Algebra.WeaklyEtale K B) :
    IsReduced B ∧
      Algebra.IsIntegral K B ∧
      (∀ A : Subalgebra K B, A.FG →
        ∃ (ι : Type v) (_ : Finite ι) (L : ι → Type v) (_ : ∀ i, Field (L i))
          (_ : ∀ i, Algebra K (L i)) (_ : A ≃ₐ[K] ∀ i, L i),
          ∀ i, Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i)) ∧
      (((Subsingleton B ∨ IsField B) ↔
          ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) ∧
        (IsField B → Algebra.IsSeparable K B ∧ Algebra.IsAlgebraic K B)) ∧
      ((∀ S : Subalgebra K B, Algebra.WeaklyEtale K S) ∧
        (∀ (Q : Type w) [CommRing Q] [Algebra K Q],
          (∃ f : B →ₐ[K] Q, Function.Surjective f) → Algebra.WeaklyEtale K Q)) ∧
      (∀ (B' : Type w) [CommRing B'] [Algebra K B'],
        Algebra.WeaklyEtale K B' → Algebra.WeaklyEtale K (B ⊗[K] B')) := by
  have hint := isIntegral_of_weaklyEtale K B hB
  refine ⟨(absolutelyFlat_and_isReduced_of_flat_lmul' K B hB.flat_lmul').2 inferInstance hB,
    hint, fg_subalgebra_product K B hB,
    ⟨subsingleton_or_isField_iff_idempotent K B hB,
      fun hf ↦ ⟨isSeparable_of_weaklyEtale_of_isField K B hB hf, hint.isAlgebraic⟩⟩,
    ⟨weaklyEtale_subalgebra_of_weaklyEtale K B hB,
      fun Q _ _ ⟨f, hf⟩ ↦ weaklyEtale_of_surjective_of_weaklyEtale K B hB f hf⟩,
    fun B' _ _ _ => Algebra.WeaklyEtale.trans K B (B ⊗[K] B')⟩

end StructureOverField
