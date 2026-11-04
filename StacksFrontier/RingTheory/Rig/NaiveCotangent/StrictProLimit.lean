module

public import StacksFrontier.RingTheory.LocalCohomology.StrictProCategory
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.ProIsomorphism
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.ReductionIdentification

/-!
# Strict pro-isomorphism of the naive cotangent systems

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal and let `B` be an `I`-adically complete
`A`-algebra of finite type modulo `I`.  Writing `Aₙ = A / Iⁿ` and `Bₙ = B / IⁿB`, and fixing a
presentation `B = A⟨x₁, …, x_r⟩ / J` of `B` as a quotient of a completed polynomial algebra,
the two inverse systems

`{NL^∧_{B/A} ⊗_B Bₙ}`  and  `{NL_{Bₙ/Aₙ}}`

of two-term complexes of `B`-modules are *strictly* isomorphic as pro-objects: there is a
single shift `c ≥ 0` and, for every `n`, maps in both directions
`NL^∧_{B/A} ⊗_B B_{n+c} ⟶ NL_{B_{n+c}/A_{n+c}} ⟶ NL^∧_{B/A} ⊗_B Bₙ ⟶ NL_{Bₙ/Aₙ}` whose two
composites are exactly the transition maps of the two systems.  That is the content of
Stacks 0AJS (1); "strictly isomorphic" means isomorphic in the strict pro-category, in which a
morphism is a uniform shift `c` together with a compatible family `X_{n+c} ⟶ Yₙ`, taken up to
increasing `c`.

Two-term complexes of `S`-modules and chain maps are made into a category here, so that an
inverse system of them is a functor `ℕᵒᵖ ⥤ TwoTerm S` and the strict pro-category of Stacks
0GA5 applies verbatim.  The interleaving is then formal: every map in sight is the canonical
surjection between two quotients of `NL^∧_{B/A}` by nested pairs of submodules, so all four
required identities — naturality of the two families and the two composites — hold because both
sides send the class of an element to the class of that same element.  The one piece of
mathematics is the sandwich of submodules of `J / J²`

`Iⁿ · (J / J²) ⊆ ⟨image of J ∩ Iⁿ A⟨x⟩⟩ ⊆ I^{n-c} · (J / J²)`,  `n ≥ c`,

whose right-hand inclusion is the Artin–Rees lemma (Stacks 00IN) in the Noetherian ring
`A⟨x⟩` (Stacks 0AJQ); it is `Rig.CompletedPolynomialPresentation.exists_conormalSub_le_smul_top`.

## Main definitions

* `Stacks.LocalCohomology.proObj`, `Stacks.LocalCohomology.proHom`: an inverse sequence and a
  representative, read as an object and a morphism of the strict pro-category.
* `NaiveCotangent.instCategoryTwoTerm`: two-term complexes of `S`-modules form a category.
* `NaiveCotangent.TwoTerm.modIdealTower`: the inverse system `{X ⊗_S S/𝔞ⁿ}`.
* `NaiveCotangent.TwoTerm.quotTower`: the inverse system of quotients of `X` by a decreasing
  family of submodules in degree `1` and by `𝔞ⁿ` in degree `0`.
* `Rig.CompletedNaiveCotangentComplex.completedReductionTower` and
  `Rig.CompletedNaiveCotangentComplex.reductionTower`: the two inverse systems of
  Stacks 0AJS (1).

## Main results

* `Stacks.LocalCohomology.nonempty_iso_of_interleaved`: two inverse sequences carrying
  interleaved natural transformations with a uniform shift are isomorphic in the strict
  pro-category.
* `NaiveCotangent.TwoTerm.nonempty_iso_proObj_quotTower`: the generic strict pro-isomorphism
  attached to a sandwich of submodules.
* `Rig.CompletedNaiveCotangentComplex.nonempty_iso_reductionTower`: **Stacks 0AJS (1)** — the
  two systems are strictly isomorphic, and at every level the second one is the naive
  cotangent complex of the induced presentation `Bₙ = Aₙ[x₁, …, x_r] / Jₙ`.
* `Rig.CompletedPolynomialPresentation.conormalSub_antitone`: the submodules of `J / J²` cut
  out by the ideals `J ∩ Iⁿ A⟨x⟩` decrease with `n`, so they do form an inverse system.

## Implementation notes

The shift `c` is the Artin–Rees constant, and both interleaving families are defined for every
`n ≥ 0`, so no "eventually" clause is needed: the equivalence relation of the strict
pro-category is used only to recognise the two composites as the identity.

`reductionTower` is `NL_{Bₙ/Aₙ}` presented as a quotient of `NL^∧_{B/A}`, which is how the
source produces it.  Its identification with the naive cotangent complex of an honest
`Algebra.Generators Aₙ Bₙ (Fin r)` is the content of `Rig/NaiveCotangent/ReductionComparison.lean`
and `Rig/NaiveCotangent/ReductionIdentification.lean`, and is carried by the main statement as a
pair of isomorphisms of the two terms commuting with the differentials.  It is stated that way
rather than as an isomorphism in `TwoTerm B` because the degree-`0` term of `NL(Bₙ = Aₙ[x]/Jₙ)`
is a tensor product over `Aₙ[x]`, so it lives one universe higher than the degree-`0` term
`(⨁ᵢ B dxᵢ) / IⁿB` of `reductionTower`, and the two are not objects of one category of two-term
complexes.

What is *not* proved here is that the transition maps of the system `{NL(Bₙ = Aₙ[x]/Jₙ)}`
induced by morphisms of presentations correspond, under those isomorphisms, to the transition
maps of `reductionTower`; the two agree up to homotopy by Stacks 00S1 (2), but the strict
pro-category sees chain maps on the nose.  Part (2) of Stacks 0AJS, the identification
`NL^∧_{B/A} = R lim NL_{Bₙ/Aₙ}` in `D(B)`, is not proved here either.

## References

* [Stacks Project, Tag 0AJS](https://stacks.math.columbia.edu/tag/0AJS)
* [Stacks Project, Tag 0GA5](https://stacks.math.columbia.edu/tag/0GA5)
* [Stacks Project, Tag 00IN](https://stacks.math.columbia.edu/tag/00IN)
-/

@[expose] public section

/-! ## The strict pro-category: objects, morphisms, and a criterion for an isomorphism -/

namespace Stacks.LocalCohomology

open CategoryTheory Opposite

universe v u

variable {C : Type u} [Category.{v} C]

/-- Any two parallel arrows of an inverse sequence have the same image: the index category
`ℕᵒᵖ` is a preorder, so its hom types are subsingletons. -/
private theorem map_eq_map (X : Functor ℕᵒᵖ C) {m n : ℕᵒᵖ} (f g : m ⟶ n) :
    X.map f = X.map g := by
  congr 1
  apply Subsingleton.elim

/-- An inverse sequence, read as an object of the strict pro-category. -/
public def proObj (X : Functor ℕᵒᵖ C) : StrictProCategory C :=
  (CategoryTheory.Quotient.functor (strictProRelations (C := C))).obj
    (show Paths (strictProQuiver C) from X)

/-- The strict pro-morphism represented by a uniform shift together with a compatible family
of component maps. -/
public def proHom {X Y : Functor ℕᵒᵖ C} (f : StrictProHomRep X Y) : proObj X ⟶ proObj Y :=
  (CategoryTheory.Quotient.functor (strictProRelations (C := C))).map
    ((Paths.of (strictProQuiver C)).map f)

/-- Representatives compose to the composite representative. -/
public theorem proHom_comp {X Y Z : Functor ℕᵒᵖ C} (f : StrictProHomRep X Y)
    (g : StrictProHomRep Y Z) : proHom f ≫ proHom g = proHom (StrictProHomRep.comp f g) :=
  ((CategoryTheory.Quotient.functor (strictProRelations (C := C))).map_comp
      ((Paths.of (strictProQuiver C)).map f)
      ((Paths.of (strictProQuiver C)).map g)).symm.trans
    (CategoryTheory.Quotient.sound _ (strictProRelations.comp f g))

/-- The identity representative represents the identity. -/
public theorem proHom_id (X : Functor ℕᵒᵖ C) :
    proHom (StrictProHomRep.id X) = 𝟙 (proObj X) :=
  (CategoryTheory.Quotient.sound _ (strictProRelations.id X)).symm.trans
    ((CategoryTheory.Quotient.functor (strictProRelations (C := C))).map_id _)

/-- Equivalent representatives represent the same strict pro-morphism. -/
public theorem proHom_eq_of_equivalent {X Y : Functor ℕᵒᵖ C} {f g : StrictProHomRep X Y}
    (h : f.Equivalent g) : proHom f = proHom g :=
  CategoryTheory.Quotient.sound _ (strictProRelations.equivalent f g h)

/-- **Interleaving criterion for a strict pro-isomorphism.**  Two inverse sequences `X` and `Y`
are isomorphic in the strict pro-category as soon as there is a uniform shift `c` together with
natural families `φₙ : Xₙ ⟶ Yₙ` and `ψₙ : Y_{n+c} ⟶ Xₙ` whose two composites
`X_{n+c} ⟶ Y_{n+c} ⟶ Xₙ` and `Y_{n+c} ⟶ Xₙ ⟶ Yₙ` are the transition maps of `X` and of `Y`. -/
public theorem nonempty_iso_of_interleaved {X Y : Functor ℕᵒᵖ C} (c : ℕ)
    (φ : NatTrans X Y) (ψ : NatTrans (shiftedInverseSequence Y c) X)
    (hXY : ∀ n : ℕ, φ.app (op (n + c)) ≫ ψ.app (op n) =
      X.map (opHomOfLE (Nat.le_add_right n c)))
    (hYX : ∀ n : ℕ, ψ.app (op n) ≫ φ.app (op n) =
      Y.map (opHomOfLE (Nat.le_add_right n c))) :
    Nonempty (proObj X ≅ proObj Y) := by
  let f : StrictProHomRep X Y := ⟨0, φ⟩
  let g : StrictProHomRep Y X := ⟨c, ψ⟩
  refine ⟨⟨proHom f, proHom g, ?_, ?_⟩⟩
  · rw [proHom_comp, ← proHom_id X]
    refine proHom_eq_of_equivalent ⟨c, 0, Nat.le_refl c, Nat.zero_le c, fun n _ => ?_⟩
    dsimp [StrictProHomRep.comp, StrictProHomRep.id, shiftedInverseSequenceTransition,
      shiftedInverseSequence, inverseSequenceShift, f, g]
    rw [hXY, ← X.map_comp, ← X.map_comp, Category.comp_id]
    exact map_eq_map X _ _
  · rw [proHom_comp, ← proHom_id Y]
    refine proHom_eq_of_equivalent
      ⟨c, 0, Nat.le_of_eq (Nat.zero_add c), Nat.zero_le c, fun n _ => ?_⟩
    dsimp [StrictProHomRep.comp, StrictProHomRep.id, shiftedInverseSequenceTransition,
      shiftedInverseSequence, inverseSequenceShift, f, g]
    rw [hYX, ← Y.map_comp, ← Y.map_comp, Category.comp_id]
    exact map_eq_map Y _ _

end Stacks.LocalCohomology

/-! ## Inverse systems of two-term complexes -/

namespace NaiveCotangent

open CategoryTheory Opposite Stacks.LocalCohomology

universe u v w

/-- Two-term complexes of `S`-modules and chain maps between them form a category. -/
public instance instCategoryTwoTerm (S : Type u) [CommRing S] :
    Category.{max v w} (TwoTerm.{u, v, w} S) where
  Hom A B := ChainMap A B
  id A := ChainMap.id A
  comp f g := ChainMap.comp g f
  id_comp f := by ext <;> rfl
  comp_id f := by ext <;> rfl
  assoc f g h := by ext <;> rfl

namespace TwoTerm

variable {S : Type u} [CommRing S]

/-- Composition in the category of two-term complexes is composition of chain maps. -/
public theorem comp_eq {X Y Z : TwoTerm.{u, v, w} S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = ChainMap.comp g f := rfl

variable (X : TwoTerm.{u, v, w} S)

/-- The inverse system `{X ⊗_S S/𝔞ⁿ}` of reductions of a two-term complex along the powers of
an ideal, with the canonical surjections as transition maps. -/
public def modIdealTower (𝔞 : Ideal S) : Functor ℕᵒᵖ (TwoTerm.{u, v, w} S) where
  obj n := X.modIdeal (𝔞 ^ n.unop)
  map f := X.modIdealMap (Ideal.pow_le_pow_right (leOfHom f.unop))
  map_id _ := X.modIdealMap_self _
  map_comp _ _ := (X.modIdealMap_comp _ _).symm

/-- The `n`-th term of `X.modIdealTower 𝔞` is the reduction `X ⊗_S S/𝔞ⁿ`. -/
@[simp] public theorem modIdealTower_obj (𝔞 : Ideal S) (n : ℕ) :
    (X.modIdealTower 𝔞).obj (op n) = X.modIdeal (𝔞 ^ n) := rfl

/-- The inverse system of quotients of `X` by a decreasing family `U` of submodules of `X₁`
and by `𝔞ⁿ X₀` in degree `0`, with the canonical surjections as transition maps. -/
public def quotTower (𝔞 : Ideal S) (U : ℕ → Submodule S X.X₁) (hU : Antitone U)
    (hd : ∀ n, U n ≤ (𝔞 ^ n • ⊤ : Submodule S X.X₀).comap X.d) :
    Functor ℕᵒᵖ (TwoTerm.{u, v, w} S) where
  obj n := X.quotBy (U n.unop) (𝔞 ^ n.unop • ⊤) (hd n.unop)
  map f := X.quotByMap _ _ (hU (leOfHom f.unop))
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (leOfHom f.unop)))
  map_id _ := X.quotByMap_self _
  map_comp _ _ := (X.quotByMap_comp _ _ _ _ _ _ _).symm

/-- The `n`-th term of `X.quotTower 𝔞 U hU hd` is the quotient `X / (Uₙ, 𝔞ⁿ X₀)`. -/
@[simp] public theorem quotTower_obj (𝔞 : Ideal S) (U : ℕ → Submodule S X.X₁) (hU : Antitone U)
    (hd : ∀ n, U n ≤ (𝔞 ^ n • ⊤ : Submodule S X.X₀).comap X.d) (n : ℕ) :
    (X.quotTower 𝔞 U hU hd).obj (op n) = X.quotBy (U n) (𝔞 ^ n • ⊤) (hd n) := rfl

/-- The comparison `X ⊗_S S/𝔞ⁿ ⟶ X / (Uₙ, 𝔞ⁿ X₀)`, for a family `U` containing `𝔞ⁿ X₁`. -/
public def modIdealToQuot (𝔞 : Ideal S) (U : ℕ → Submodule S X.X₁) (hU : Antitone U)
    (hd : ∀ n, U n ≤ (𝔞 ^ n • ⊤ : Submodule S X.X₀).comap X.d)
    (hlo : ∀ n, (𝔞 ^ n • ⊤ : Submodule S X.X₁) ≤ U n) :
    NatTrans (X.modIdealTower 𝔞) (X.quotTower 𝔞 U hU hd) where
  app n := X.quotByMap _ _ (hlo n.unop) le_rfl
  naturality _ _ _ := by
    refine ChainMap.ext ?_ ?_
    all_goals
      refine LinearMap.ext fun z => ?_
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
      rfl

/-- The comparison `X / (U_{n+c}, 𝔞^{n+c} X₀) ⟶ X ⊗_S S/𝔞ⁿ`, for a family `U` with
`U_{n+c}` inside `𝔞ⁿ X₁`.  This is the backwards half of the interleaving, and the shift `c`
is where the Artin–Rees constant enters. -/
public def quotShiftToModIdeal (𝔞 : Ideal S) (c : ℕ) (U : ℕ → Submodule S X.X₁)
    (hU : Antitone U) (hd : ∀ n, U n ≤ (𝔞 ^ n • ⊤ : Submodule S X.X₀).comap X.d)
    (hhi : ∀ n, U (n + c) ≤ (𝔞 ^ n • ⊤ : Submodule S X.X₁)) :
    NatTrans (shiftedInverseSequence (X.quotTower 𝔞 U hU hd) c) (X.modIdealTower 𝔞) where
  app n := X.quotByMap _ _ (hhi n.unop)
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right n.unop c)))
  naturality _ _ _ := by
    refine ChainMap.ext ?_ ?_
    all_goals
      refine LinearMap.ext fun z => ?_
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
      rfl

/-- **The generic strict pro-isomorphism of a sandwich.**  Let `X` be a two-term complex of
`S`-modules, let `𝔞 ⊆ S` be an ideal, and let `U` be a decreasing family of submodules of `X₁`
carried into `𝔞ⁿ X₀` by the differential and sandwiched as
`𝔞ⁿ X₁ ⊆ Uₙ` and `U_{n+c} ⊆ 𝔞ⁿ X₁` for a uniform `c`.  Then the inverse system of quotients
`{X / (Uₙ, 𝔞ⁿ X₀)}` is isomorphic, in the strict pro-category, to the system of reductions
`{X ⊗_S S/𝔞ⁿ}`. -/
public theorem nonempty_iso_proObj_quotTower (𝔞 : Ideal S) (c : ℕ) (U : ℕ → Submodule S X.X₁)
    (hU : Antitone U) (hd : ∀ n, U n ≤ (𝔞 ^ n • ⊤ : Submodule S X.X₀).comap X.d)
    (hlo : ∀ n, (𝔞 ^ n • ⊤ : Submodule S X.X₁) ≤ U n)
    (hhi : ∀ n, U (n + c) ≤ (𝔞 ^ n • ⊤ : Submodule S X.X₁)) :
    Nonempty (proObj (X.modIdealTower 𝔞) ≅ proObj (X.quotTower 𝔞 U hU hd)) := by
  refine nonempty_iso_of_interleaved c (X.modIdealToQuot 𝔞 U hU hd hlo)
    (X.quotShiftToModIdeal 𝔞 c U hU hd hhi) (fun n => ?_) (fun n => ?_) <;>
    refine ChainMap.ext ?_ ?_ <;>
    exact LinearMap.ext fun z => by
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z; rfl

end TwoTerm

end NaiveCotangent

/-! ## Stacks 0AJS (1) -/

namespace Rig

open CategoryTheory Opposite Stacks.LocalCohomology NaiveCotangent

namespace CompletedPolynomialPresentation

universe u v

variable {A : Type u} [CommRing A] {I : Ideal A} {B : AdicFiniteTypeAlgebra.{u, v} A I}
  (P : CompletedPolynomialPresentation I B)

/-- The conormal submodules cut out by the ideals `J ∩ Iⁿ A⟨x⟩` decrease with `n`. -/
public theorem conormalSub_antitone : Antitone P.conormalSub := by
  intro m n hmn
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  refine P.mk_mem_conormalSub g (Ideal.map_mono (Ideal.pow_le_pow_right hmn) hg)

end CompletedPolynomialPresentation

namespace CompletedNaiveCotangentComplex

universe u v

variable {A : Type u} [CommRing A] {I : Ideal A} {B : AdicFiniteTypeAlgebra.{u, v} A I}
  {P : CompletedPolynomialPresentation I B}

/-- The inverse system `{NL^∧_{B/A} ⊗_B Bₙ}` of reductions of the completed naive cotangent
complex modulo the powers of `I`. -/
public noncomputable def completedReductionTower (K : CompletedNaiveCotangentComplex P) :
    Functor ℕᵒᵖ (TwoTerm.{v, u, v} B.carrier) :=
  K.twoTerm.modIdealTower B.adicIdeal

/-- The inverse system `{NL_{Bₙ/Aₙ}}`, with `NL_{Bₙ/Aₙ} = (Jₙ / Jₙ² ⟶ ⨁ᵢ Bₙ dxᵢ)` realised as
the quotient of `NL^∧_{B/A}` by the image of `J ∩ Iⁿ A⟨x⟩` in degree `-1` and by `IⁿB` in
degree `0`. -/
public noncomputable def reductionTower (K : CompletedNaiveCotangentComplex P) :
    Functor ℕᵒᵖ (TwoTerm.{v, u, v} B.carrier) :=
  K.twoTerm.quotTower B.adicIdeal P.conormalSub P.conormalSub_antitone
    K.conormalSub_le_comap_differential

/-- Level `n` of `{NL^∧_{B/A} ⊗_B Bₙ}` is the reduction of `NL^∧_{B/A}` modulo `IⁿB`. -/
public theorem completedReductionTower_obj (K : CompletedNaiveCotangentComplex P)
    (n : ℕ) :
    K.completedReductionTower.obj (op n) = K.twoTerm.modIdeal (B.adicIdeal ^ n) := rfl

/-- Level `n` of `{NL_{Bₙ/Aₙ}}` is the complex `Jₙ / Jₙ² ⟶ ⨁ᵢ Bₙ dxᵢ`. -/
public theorem reductionTower_obj (K : CompletedNaiveCotangentComplex P) (n : ℕ) :
    K.reductionTower.obj (op n) = K.reducedComplex n := rfl

/-- **Stacks 0AJS (1).**  Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `B` an object of
the category of Stacks 0AL4, presented as `B = A⟨x₁, …, x_r⟩ / J`.  Then the pro-objects
`{NL^∧_{B/A} ⊗_B Bₙ}` and `{NL_{Bₙ/Aₙ}}` are *strictly* isomorphic: there is one shift making
the two systems isomorphic in the strict pro-category, and at every level the second system is
the naive cotangent complex of the induced presentation `Bₙ = Aₙ[x₁, …, x_r] / Jₙ` — the
conormal modules and the degree-`0` terms agree and the two differentials correspond. -/
@[stacks 0AJS "part (1)"]
public theorem nonempty_iso_reductionTower [IsNoetherianRing A]
    (K : CompletedNaiveCotangentComplex P) :
    Nonempty (proObj K.completedReductionTower ≅ proObj K.reductionTower) ∧
      ∀ n : ℕ, ∃ (e₁ : (K.reductionTower.obj (op n)).X₁ ≃ₗ[B.carrier]
            (P.reductionGenerators n).toExtension.Cotangent)
          (e₀ : (K.reductionTower.obj (op n)).X₀ ≃ₗ[B.carrier]
            (P.reductionGenerators n).toExtension.CotangentSpace),
          ∀ x, e₀ ((K.reductionTower.obj (op n)).d x) =
            (P.reductionGenerators n).toExtension.cotangentComplex (e₁ x) := by
  refine ⟨?_, fun n => ⟨P.cotangentQuotConormalSubEquiv n, P.reductionCotangentSpaceEquiv n,
    K.reductionComparison_comm n⟩⟩
  obtain ⟨c, _, hc⟩ := P.exists_conormalSub_le_smul_top
  refine K.twoTerm.nonempty_iso_proObj_quotTower B.adicIdeal c P.conormalSub
    P.conormalSub_antitone K.conormalSub_le_comap_differential P.smul_top_le_conormalSub
    fun n => ?_
  have h := hc (n + c) (Nat.le_add_left c n)
  rw [Nat.add_sub_cancel] at h
  exact h

end CompletedNaiveCotangentComplex

end Rig

end
