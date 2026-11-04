module

public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Logic.Small.Set
public import StacksFrontier.AlgebraicGeometry.Seminormalization.CandidateTensor
public import StacksFrontier.AlgebraicGeometry.Seminormalization.LocalProperty
public import StacksFrontier.AlgebraicGeometry.SnCharacterization.Basic

/-!
# Functoriality of the seminormalization of a ring

Every homomorphism of commutative rings induces a unique compatible homomorphism between the
seminormalizations of its source and target.

## Main results

* `AlgebraicGeometry.existsUnique_seminormalizationMap`: the unique compatible map on
  seminormalizations induced by a ring homomorphism.
* `AlgebraicGeometry.isIso_residueFieldMap_specMap_tensorProduct_includeLeft`: inducing
  isomorphisms on residue fields passes to the projection `Spec (C ⊗[A] B) ⟶ Spec C`.
* `AlgebraicGeometry.isSeminormalizationCandidateAlgebra_tensorProduct`: the base change of a
  subintegral algebra along any ring homomorphism is again subintegral.
* `AlgebraicGeometry.exists_small_seminormal_subring`: a family of elements of a seminormal ring
  lies in a small seminormal subring.
* `AlgebraicGeometry.bijective_algebraMap_seminormalization`: the canonical map from a seminormal
  ring to its own seminormalization is bijective.

## Implementation notes

Compatibility means that the induced map, composed with the canonical map into the source
seminormalization, is the canonical map into the target seminormalization after the given ring
homomorphism.

The construction is the universal property rather than the colimit.  For `φ : A → A'` the base
change `A' ⊗[A] Aˢⁿ` is a subintegral `A'`-algebra, so
`AlgebraicGeometry.seminormalizationAlgebraObject_isTerminal` sends it to `A'ˢⁿ`, and
precomposing with `Algebra.TensorProduct.includeRight` gives a map `Aˢⁿ → A'ˢⁿ`; its
compatibility is the commutation of that terminal map with the structure map of `A'`.
Uniqueness is the tensor product's own universal property, which identifies a competing map with
the terminal one.

That argument needs source and target in the same universe, because
`AlgebraicGeometry.UniversalHomeomorphism` is available only for `Scheme.{u}`.  The general case
is reduced to it by the one genuinely infinitary step: a map `A → S` into a seminormal ring takes
values in a *small* seminormal subring of `S`, obtained as the set of values of the formal terms
built from the family using the ring operations and the square-and-cube root supplied by
seminormality.  The target is then replaced by `Shrink` of that subring and the same-universe
statement applies.  The source's seminormalization is seminormal by
`AlgebraicGeometry.isSeminormalRing_of_isTerminal`, which is what makes the lift available at
all, and the identification of a seminormal ring with its own seminormalization is the
characterization of Tag 0EUR's `sn_characterization` label.

The base-change input is taken from
`StacksDraft.AlgebraicGeometry.F3.Seminormalization.CandidateTensor`, which already proves both
halves for the projection induced by `Algebra.TensorProduct.includeRight`, and the universal
homeomorphism half for the other projection as well; only the residue-field half for the other
projection is added here, by the same commutativity isomorphism of the tensor product that file
uses.

No hypothesis beyond those of Tag 0EUR is used: `A` and `A'` are arbitrary commutative rings in
arbitrary universes, with no Noetherian, reducedness or finiteness assumption.

## References

* [Stacks Project, Tag 0EUL](https://stacks.math.columbia.edu/tag/0EUL)
* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
-/

public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace AlgebraicGeometry

/-! ### Base change of a subintegral algebra -/

section BaseChange

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

/-- The commutativity isomorphism of the tensor product turns the projection induced by
`Algebra.TensorProduct.includeLeftRingHom` into the one induced by
`Algebra.TensorProduct.includeRight`. -/
private lemma specMap_includeLeftRingHom_eq :
    Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := C) (B := B))) =
      (asIso (Spec.map (RingEquiv.toCommRingCatIso
          (Algebra.TensorProduct.comm A C B).toRingEquiv).hom)).inv ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom) := by
  let ρ : CommRingCat.of (C ⊗[A] B) ≅ CommRingCat.of (B ⊗[A] C) :=
    RingEquiv.toCommRingCatIso (Algebra.TensorProduct.comm A C B).toRingEquiv
  let i : Spec (CommRingCat.of (B ⊗[A] C)) ⟶ Spec (CommRingCat.of (C ⊗[A] B)) := Spec.map ρ.hom
  let p := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom)
  let q := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := C) (B := B)))
  have hcomp : i ≫ q = p := by
    have hr : CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := C) (B := B)) ≫ ρ.hom =
        CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom :=
      CommRingCat.hom_ext (congrArg (fun φ : C →ₐ[A] B ⊗[A] C => φ.toRingHom)
        (Algebra.TensorProduct.comm_comp_includeLeft A C B))
    simpa [i, p, q, Spec.map_comp] using congrArg Spec.map hr
  show q = (asIso i).inv ≫ p
  rw [← hcomp]
  simp

/-- If `Spec B ⟶ Spec A` induces isomorphisms on residue fields, so does the projection
`Spec (C ⊗[A] B) ⟶ Spec C`.  This is the companion of
`AlgebraicGeometry.universalHomeomorphism_specMap_tensorProduct_includeLeft`. -/
theorem isIso_residueFieldMap_specMap_tensorProduct_includeLeft
    (hB : ∀ x : Spec (CommRingCat.of B),
      IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B))).residueFieldMap x))
    (x : Spec (CommRingCat.of (C ⊗[A] B))) :
    IsIso (Scheme.Hom.residueFieldMap (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := C) (B := B)))) x) := by
  rw [specMap_includeLeftRingHom_eq A B C, Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso'
    (isIso_residueFieldMap_specMap_tensorProduct_includeRight A B C hB _) inferInstance

/-- **Stacks 0EUR.** The base change of a subintegral `A`-algebra along `A ⟶ C` is a subintegral
`C`-algebra: if `Spec B ⟶ Spec A` is a universal homeomorphism inducing isomorphisms on all
residue fields, then so is `Spec (C ⊗[A] B) ⟶ Spec C`. -/
theorem isSeminormalizationCandidateAlgebra_tensorProduct
    (hB : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hBres : Scheme.Hom.InducesResidueFieldIsomorphisms
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    IsSeminormalizationCandidateAlgebra C (CommAlgCat.of C (C ⊗[A] B)) :=
  ⟨universalHomeomorphism_specMap_tensorProduct_includeLeft A B C hB,
    fun _ => isIso_residueFieldMap_specMap_tensorProduct_includeLeft A B C hBres _⟩

end BaseChange

/-! ### Functoriality in a single universe -/

/-- **Stacks 0EUR** for source and target in the same universe: a ring homomorphism induces a
unique compatible homomorphism between the seminormalizations. -/
theorem existsUnique_seminormalizationMap_sameUniverse
    {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A') :
    ∃! φsn : Algebra.seminormalization A →+* Algebra.seminormalization A',
      φsn.comp (algebraMap A (Algebra.seminormalization A)) =
        (algebraMap A' (Algebra.seminormalization A')).comp φ := by
  classical
  let N := Algebra.seminormalization A
  let B := A'
  let _ : Algebra A B := φ.toAlgebra
  let C := B ⊗[A] N
  let hC : IsSeminormalizationCandidateAlgebra B (CommAlgCat.of B C) :=
    isSeminormalizationCandidateAlgebra_tensorProduct A N B
      (seminormalization_universalHomeomorphism A)
      (seminormalization_inducesResidueFieldIsomorphisms A)
  let R : SeminormalizationAlgebraCategory B := ⟨CommAlgCat.of B C, hC⟩
  let t := seminormalizationAlgebraObject_isTerminal B
  let q := t.from R
  let qMap : C →+* Algebra.seminormalization B := q.hom.hom.toRingHom
  let ι : N →+* C := (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := N)).toRingHom
  let φsn : N →+* Algebra.seminormalization B := qMap.comp ι
  have hcompat : φsn.comp (algebraMap A N) =
      (algebraMap B (Algebra.seminormalization B)).comp φ :=
    RingHom.ext fun a => (congrArg qMap
      (((Algebra.TensorProduct.includeRight (R := A) (A := B) (B := N)).commutes a).trans
        (IsScalarTower.algebraMap_apply A B C a))).trans (q.hom.hom.commutes (φ a))
  refine ⟨φsn, hcompat, fun ψ hψ => ?_⟩
  let _ : Algebra A (Algebra.seminormalization B) := Algebra.compHom _ φ
  let _ : IsScalarTower A B (Algebra.seminormalization B) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ψA : N →ₐ[A] Algebra.seminormalization B :=
    { toRingHom := ψ
      commutes' := fun a =>
        (RingHom.congr_fun hψ a).trans (IsScalarTower.algebraMap_apply A B _ a).symm }
  let lift : C →ₐ[B] Algebra.seminormalization B :=
    Algebra.TensorProduct.lift (Algebra.ofId B (Algebra.seminormalization B)) ψA
      (fun _ _ => Commute.all _ _)
  let q' : R ⟶ seminormalizationAlgebraObject B :=
    ObjectProperty.homMk (CommAlgCat.ofHom lift)
  have hrestrict : lift.toRingHom.comp ι = qMap.comp ι :=
    congrArg (fun f : R ⟶ seminormalizationAlgebraObject B => f.hom.hom.toRingHom.comp ι)
      (t.hom_ext q' q)
  have hlift : ψ = lift.toRingHom.comp ι :=
    congrArg AlgHom.toRingHom (Algebra.TensorProduct.lift_comp_includeRight
      (Algebra.ofId B (Algebra.seminormalization B)) ψA (fun _ _ => Commute.all _ _)).symm
  exact hlift.trans hrestrict

/-! ### A small seminormal subring containing a given family -/

/-- Formal terms in a family of elements of a ring, built from the ring operations together with
a formal common square-and-cube root. -/
private inductive SeminormalTerm (ι : Type u) : Type u
  | of (i : ι)
  | zero
  | one
  | add (x y : SeminormalTerm ι)
  | neg (x : SeminormalTerm ι)
  | mul (x y : SeminormalTerm ι)
  | root (x y : SeminormalTerm ι)

/-- The common square-and-cube root of a pair `x ^ 3 = y ^ 2` supplied by seminormality, as a
total function. -/
private noncomputable def seminormalRoot {S : Type v} [CommRing S]
    (hS : IsSeminormalRing S) (x y : S) : S :=
  open Classical in if h : x ^ 3 = y ^ 2 then (hS x y h).choose else 0

private lemma seminormalRoot_spec {S : Type v} [CommRing S]
    (hS : IsSeminormalRing S) {x y : S} (h : x ^ 3 = y ^ 2) :
    x = seminormalRoot hS x y ^ 2 ∧ y = seminormalRoot hS x y ^ 3 := by
  simpa only [seminormalRoot, dite_eq_left h] using (hS x y h).choose_spec.1

/-- The value of a formal term. -/
private noncomputable def SeminormalTerm.eval {ι : Type u} {S : Type v} [CommRing S]
    (hS : IsSeminormalRing S) (f : ι → S) : SeminormalTerm ι → S
  | .of i => f i
  | .zero => 0
  | .one => 1
  | .add x y => x.eval hS f + y.eval hS f
  | .neg x => -x.eval hS f
  | .mul x y => x.eval hS f * y.eval hS f
  | .root x y => seminormalRoot hS (x.eval hS f) (y.eval hS f)

/-- A family of elements of a seminormal ring indexed by a type in universe `u` lies in a
seminormal subring which is small in universe `u`. -/
theorem exists_small_seminormal_subring {ι : Type u} {S : Type v} [CommRing S]
    (hS : IsSeminormalRing S) (f : ι → S) :
    ∃ T : Subring S, Small.{u} T ∧ IsSeminormalRing T ∧ ∀ i, f i ∈ T := by
  classical
  let ev := SeminormalTerm.eval hS f
  let T : Subring S :=
    { carrier := Set.range ev
      zero_mem' := ⟨.zero, rfl⟩
      one_mem' := ⟨.one, rfl⟩
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨.add x y, rfl⟩
      neg_mem' := by
        rintro _ ⟨x, rfl⟩
        exact ⟨.neg x, rfl⟩
      mul_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨.mul x y, rfl⟩ }
  refine ⟨T, small_range ev, ?_, fun i => ⟨.of i, rfl⟩⟩
  intro x y hxy
  have h : (x : S) ^ 3 = (y : S) ^ 2 := congrArg Subtype.val hxy
  have hm : seminormalRoot hS (x : S) (y : S) ∈ T := by
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    refine ⟨.root a b, ?_⟩
    show seminormalRoot hS (ev a) (ev b) = _
    rw [ha, hb]
  refine ⟨⟨seminormalRoot hS (x : S) (y : S), hm⟩,
    ⟨Subtype.ext (seminormalRoot_spec hS h).1, Subtype.ext (seminormalRoot_spec hS h).2⟩,
    fun z hz => Subtype.ext ((hS (x : S) (y : S) h).unique
      ⟨congrArg Subtype.val hz.1, congrArg Subtype.val hz.2⟩ (seminormalRoot_spec hS h))⟩

/-! ### Lifting a map into a seminormal ring -/

/-- A seminormal ring is its own seminormalization: the canonical map is bijective. -/
theorem bijective_algebraMap_seminormalization
    (R : Type u) [CommRing R] (hR : IsSeminormalRing R) :
    Function.Bijective (algebraMap R (Algebra.seminormalization R)) := by
  have hf : Spec.map (CommRingCat.ofHom (algebraMap R R)) =
      𝟙 (Spec (CommRingCat.of R)) :=
    Spec.map_id _
  have hU : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap R R))) := by
    rw [hf]
    exact universalHomeomorphism_of_isIso _
  have hres : Scheme.Hom.InducesResidueFieldIsomorphisms
      (Spec.map (CommRingCat.ofHom (algebraMap R R))) := by
    rw [hf]
    intro x
    rw [Scheme.residueFieldMap_id]
    exact IsIso.id _
  let P : SeminormalizationAlgebraCategory R := ⟨CommAlgCat.of R R, hU, hres⟩
  let q := (seminormalizationAlgebraObject_isTerminal R).from P
  have _ : IsIso q :=
    (isIso_lift_to_seminormalization_iff_isSeminormalRing R R hU hres).mpr hR
  have hq := ConcreteCategory.bijective_of_isIso ((ObjectProperty.ι _).map q)
  have heq : q.hom.hom.toRingHom = algebraMap R (Algebra.seminormalization R) :=
    RingHom.ext q.hom.hom.commutes
  change Function.Bijective q.hom.hom.toRingHom at hq
  rwa [heq] at hq

/-- Every ring map into a seminormal ring in the same universe factors uniquely through the
seminormalization of its source. -/
theorem existsUnique_lift_to_seminormal_sameUniverse
    {R S : Type u} [CommRing R] [CommRing S]
    (hS : IsSeminormalRing S) (f : R →+* S) :
    ∃! g : Algebra.seminormalization R →+* S,
      g.comp (algebraMap R (Algebra.seminormalization R)) = f := by
  let e := RingEquiv.ofBijective (algebraMap S (Algebra.seminormalization S))
    (bijective_algebraMap_seminormalization S hS)
  obtain ⟨g, hg, hu⟩ := existsUnique_seminormalizationMap_sameUniverse f
  refine ⟨e.symm.toRingHom.comp g, ?_, ?_⟩
  · ext x
    have hx := RingHom.congr_fun hg x
    simp only [RingHom.comp_apply] at hx
    show e.symm (g (algebraMap R (Algebra.seminormalization R) x)) = f x
    rw [hx]
    exact e.symm_apply_apply (f x)
  · intro k hk
    have he : e.toRingHom.comp k = g := hu _ (by
      show (e.toRingHom.comp k).comp (algebraMap R (Algebra.seminormalization R)) = _
      rw [RingHom.comp_assoc, hk]
      rfl)
    exact RingHom.ext fun x => e.injective (by simpa using RingHom.congr_fun he x)

/-- Every ring map into a seminormal ring factors through the seminormalization of its source,
with no constraint relating the two universes. -/
theorem exists_lift_to_seminormal
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (hS : IsSeminormalRing S) (f : R →+* S) :
    ∃ g : Algebra.seminormalization R →+* S,
      g.comp (algebraMap R (Algebra.seminormalization R)) = f := by
  obtain ⟨T, _, hT, hf⟩ := exists_small_seminormal_subring hS f
  let e := Shrink.ringEquiv.{u} T
  let fT : R →+* T := f.codRestrict T hf
  let f' : R →+* Shrink.{u} T := e.symm.toRingHom.comp fT
  obtain ⟨g, hg, _⟩ := existsUnique_lift_to_seminormal_sameUniverse
    (Stacks.RingTheory.Seminormal.IsSeminormalRing.of_ringEquiv e.symm hT) f'
  refine ⟨T.subtype.comp (e.toRingHom.comp g), RingHom.ext fun x => ?_⟩
  have hx := RingHom.congr_fun hg x
  simp only [RingHom.comp_apply] at hx
  show (e (g (algebraMap R (Algebra.seminormalization R) x)) : S) = f x
  rw [hx]
  exact congrArg Subtype.val (e.apply_symm_apply (fT x))

/-- The factorization of a ring map into a seminormal ring through the seminormalization of its
source is unique, with no constraint relating the two universes. -/
theorem lift_to_seminormal_unique
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (hS : IsSeminormalRing S) (f : R →+* S)
    (g k : Algebra.seminormalization R →+* S)
    (hg : g.comp (algebraMap R (Algebra.seminormalization R)) = f)
    (hk : k.comp (algebraMap R (Algebra.seminormalization R)) = f) : g = k := by
  obtain ⟨T, _, hT, hmem⟩ := exists_small_seminormal_subring hS
    (Sum.elim g k : Algebra.seminormalization R ⊕ Algebra.seminormalization R → S)
  let e := Shrink.ringEquiv.{u} T
  let gT : Algebra.seminormalization R →+* T := g.codRestrict T (fun x => hmem (.inl x))
  let kT : Algebra.seminormalization R →+* T := k.codRestrict T (fun x => hmem (.inr x))
  let g' := e.symm.toRingHom.comp gT
  let k' := e.symm.toRingHom.comp kT
  have heq : g'.comp (algebraMap R (Algebra.seminormalization R)) =
      k'.comp (algebraMap R (Algebra.seminormalization R)) :=
    RingHom.ext fun x => congrArg e.symm (Subtype.ext (RingHom.congr_fun (hg.trans hk.symm) x))
  have he : g' = k' := (existsUnique_lift_to_seminormal_sameUniverse
    (Stacks.RingTheory.Seminormal.IsSeminormalRing.of_ringEquiv e.symm hT)
    (g'.comp (algebraMap R (Algebra.seminormalization R)))).unique rfl heq.symm
  exact RingHom.ext fun x => congrArg Subtype.val
    (e.symm.injective (RingHom.congr_fun he x : e.symm (gT x) = e.symm (kT x)))

/-! ### Functoriality -/

/-- **Stacks 0EUR.** A ring homomorphism induces a unique compatible homomorphism between the
seminormalizations of its source and target. -/
@[stacks 0EUR "sn_functoriality"]
theorem existsUnique_seminormalizationMap
    {A : Type u} {A' : Type v} [CommRing A] [CommRing A'] (φ : A →+* A') :
    ∃! φsn : Algebra.seminormalization A →+* Algebra.seminormalization A',
      φsn.comp (algebraMap A (Algebra.seminormalization A)) =
        (algebraMap A' (Algebra.seminormalization A')).comp φ := by
  have hS := isSeminormalRing_of_isTerminal A' (seminormalizationAlgebraObject A')
    (seminormalizationAlgebraObject_isTerminal A')
  obtain ⟨g, hg⟩ := exists_lift_to_seminormal hS
    ((algebraMap A' (Algebra.seminormalization A')).comp φ)
  exact ⟨g, hg, fun k hk => lift_to_seminormal_unique hS _ k g hk hg⟩

/-- Tag 0EUR's `sn_functoriality` assertion, restated with every binder explicit and in the
order the source states them, to record that nothing is assumed beyond two commutative rings in
two unrelated universes. -/
example {A : Type u} {A' : Type v} [CommRing A] [CommRing A'] (φ : A →+* A') :
    ∃! φsn : Algebra.seminormalization A →+* Algebra.seminormalization A',
      φsn.comp (algebraMap A (Algebra.seminormalization A)) =
        (algebraMap A' (Algebra.seminormalization A')).comp φ :=
  existsUnique_seminormalizationMap φ

end AlgebraicGeometry

end
