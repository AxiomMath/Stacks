module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableFilteredApproximation.OpenSubrelations
import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 03K0: uniformly bounded fibres and the diagram of quotients

Uniform bounds on the cardinality of fibres of finite locally free morphisms, the bounded
quotient of a relation with universally bounded fibres, and the site-level diagram of quotient
sheaves `U / R'` indexed by the quasi-compact open subrelations `R' ⊆ R`, with its cocone and
the comparison morphisms between the stages.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] ReasonableApproximation.schemeCutoff_isClosedUnderIsomorphisms
  ReasonableApproximation.schemeCutoff_isClosedUnderLimitsOfShape_walkingCospan
  ReasonableApproximation.schemeCutoff_hasTerminal
  ReasonableApproximation.schemeCutoff_hasPullbacks

namespace ReasonableApproximation

universe u₁ u₂ v₁ v₂

/-- A sheaf of modules which is finite locally free of some rank is quasicoherent. -/
private lemma card_rank_quasicoherent {X : Scheme.{u}} (M : X.Modules) (r : ℕ)
    [h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] :
    M.IsQuasicoherent := by
  obtain ⟨q, hfree, _⟩ := h.exists_isFiniteLocallyFreeOfRankData
  let : q.IsLocallyFreeData := hfree
  exact q.quasiCoherentData.isQuasicoherent

/-- A module over a field which is finite locally free of rank `r` is a finite module of rank `r`:
rank is computed at a localisation away from a nonzero element of the spanning family. -/
private lemma finite_rank_field {k : Type u} [Field k] (M : Type u) [AddCommGroup M]
    [Module k M] {r : ℕ} (h : Module.IsFiniteLocallyFreeOfRank k M r) :
    Module.Finite k M ∧ Module.finrank k M = r := by
  classical
  rcases h with ⟨ι, f, hfspan, hbasis⟩
  have hfin : Module.Finite k M := by
    apply Module.Finite.of_localizationSpan (Set.range f) hfspan
    rintro ⟨g, ⟨i, rfl⟩⟩
    exact Module.Finite.of_basis (hbasis i).some
  have hnonempty : ∃ i, f i ≠ 0 := by
    by_contra hn
    push Not at hn
    have hz : Ideal.span (Set.range f) = (⊥ : Ideal k) :=
      (Ideal.span_eq_bot).2 (by rintro x ⟨i, rfl⟩; exact hn i)
    exact (bot_ne_top : (⊥ : Ideal k) ≠ ⊤) (hz.symm.trans hfspan)
  obtain ⟨i, hfi⟩ := hnonempty
  let S := Submonoid.powers (f i)
  let L := Localization.Away (f i)
  let Mloc := LocalizedModule S M
  let b : Module.Basis (Fin r) L Mloc := (hbasis i).some
  have hS : S ≤ nonZeroDivisors k := by
    intro x hx
    rcases (Submonoid.mem_powers_iff x (f i)).mp hx with ⟨n, rfl⟩
    simpa [mem_nonZeroDivisors_iff_ne_zero] using pow_ne_zero n hfi
  have : Nontrivial L := (IsLocalization.injective L hS).nontrivial
  have hloc : Module.finrank L Mloc = r := by simpa using Module.finrank_eq_card_basis b
  have hbase : Module.finrank L Mloc = Module.finrank k Mloc :=
    IsLocalization.finrank_eq L S hS
  exact ⟨hfin, (IsLocalizedModule.finrank_eq S (LocalizedModule.mkLinearMap S M) hS).symm.trans
    (hbase.symm.trans hloc)⟩


/-- For a morphism `p : Z ⟶ Spec k` to the spectrum of a field which is finite locally free of rank
`r`, the global sections `Γ(Z, ⊤)` form a finite `k`-algebra of rank `r`. -/
private lemma finite_rank_pushforward {k : Type u} [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) (r : ℕ) [hr : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r] :
    letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
    Module.Finite k Γ(Z, ⊤) ∧ Module.finrank k Γ(Z, ⊤) = r := by
  let : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
  let M : (Spec (.of k)).Modules := Stacks.Morphisms.pushforwardStructureSheaf p
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r :=
    hr.toIsFiniteLocallyFreeOfRank
  let : M.IsQuasicoherent := card_rank_quasicoherent M r
  have hIso : IsIso M.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ M).mp inferInstance
  let : IsIso (Scheme.Modules.fromTildeΓ (R := .of k) M) := hIso
  let e : M ≅ AlgebraicGeometry.tilde ((moduleSpecΓFunctor.obj M)) :=
    (asIso (Scheme.Modules.fromTildeΓ (R := .of k) M)).symm
  have htilde : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (AlgebraicGeometry.tilde ((moduleSpecΓFunctor.obj M))) r :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e inferInstance
  have htilde' : Scheme.Modules.IsFiniteLocallyFreeOfRank
      (AlgebraicGeometry.tilde ((moduleSpecΓFunctor.obj M))) r :=
    Scheme.Modules.isFiniteLocallyFreeOfRank_of_sheaf _ r
  have hmod : Module.IsFiniteLocallyFreeOfRank k ((moduleSpecΓFunctor.obj M)) r :=
    (tilde_isFiniteLocallyFreeOfRank_iff k ((moduleSpecΓFunctor.obj M)) r).mp htilde'
  have hfin := finite_rank_field (k := k) ((moduleSpecΓFunctor.obj M)) hmod
  show Module.Finite k Γ(Z, ⊤) ∧ Module.finrank k Γ(Z, ⊤) = r
  exact hfin


/-- The `k`-algebra homomorphism `Γ(Z, ⊤) →ₐ[k] k` attached to a section of `p : Z ⟶ Spec k`, given
by the action of the section on global sections. -/
private noncomputable def sectionToAlgHom
    {k : Type u} [Field k] {Z : Scheme.{u}} (p : Z ⟶ Spec (.of k)) :
    letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
    {g : Spec (.of k) ⟶ Z // g ≫ p = 𝟙 _} → (Γ(Z, ⊤) →ₐ[k] k) := by
  let : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
  intro g
  refine { __ := (g.val.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom).hom
           commutes' := ?_ }
  intro x
  have h : ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop) ≫
      (g.val.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom) = 𝟙 _ := by
    rw [Category.assoc, ← Scheme.Hom.comp_appTop_assoc, g.property,
      Scheme.Hom.id_appTop, Category.id_comp, Iso.inv_hom_id]
  exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of k => f.hom x) h

/-- For affine `Z`, a section of `p : Z ⟶ Spec k` is determined by the algebra homomorphism it
induces on global sections. -/
private theorem sectionToAlgHom_injective
    {k : Type u} [Field k] {Z : Scheme.{u}} [IsAffine Z]
    (p : Z ⟶ Spec (.of k)) : Function.Injective (sectionToAlgHom p) := by
  let : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
  intro g h hgh
  exact Subtype.ext <| ext_of_isAffine <| (cancel_mono (Scheme.ΓSpecIso (.of k)).hom).mp <|
    CommRingCat.hom_ext (congrArg AlgHom.toRingHom hgh)

/-- A type injecting into a finite type of cardinality at most `n` is finite of cardinality at
most `n`. -/
private theorem finite_card_le_of_injective {α β : Type*} (hβ : Finite β) {n : ℕ} {j : α → β}
    (hj : Function.Injective j) (hcard : Nat.card β ≤ n) : Finite α ∧ Nat.card α ≤ n :=
  have := hβ
  ⟨Finite.of_injective j hj, (Nat.card_le_card_of_injective j hj).trans hcard⟩

/-- A morphism `p : Z ⟶ Spec k` to the spectrum of a field which is finite locally free of rank `r`
has finitely many sections, at most `r` of them: sections inject into the `k`-algebra maps
`Γ(Z, ⊤) → k`, of which there are at most `dim_k Γ(Z, ⊤) = r`. -/
private theorem finite_card_sections_of_isFiniteLocallyFreeOfRank
    {k : Type u} [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) (r : ℕ) [hr : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r] :
    Finite {g : Spec (.of k) ⟶ Z // g ≫ p = 𝟙 _} ∧
      Nat.card {g : Spec (.of k) ⟶ Z // g ≫ p = 𝟙 _} ≤ r := by
  let : _root_.AlgebraicGeometry.IsAffineHom p := hr.toIsAffineHom
  let : IsAffine Z := isAffine_of_isAffineHom p
  let : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
  obtain ⟨hfin, hrank⟩ := finite_rank_pushforward p r
  let := hfin
  exact finite_card_le_of_injective inferInstance (sectionToAlgHom_injective p)
    ((card_algHom_le_finrank k Γ(Z, ⊤) k).trans_eq hrank)

/-- Counting the fibre of a morphism of presheaves through its representing pullback: if the
pullback of `f : yoneda.obj U ⟶ X` along a section `x` of `X` over `T` is represented by
`p : V ⟶ T`, then the fibre of `f` over `x` injects into the sections of `G.map p`, so it is
finite with at most as many elements. -/
private theorem finite_card_fiber_of_isPullback
    {C : Type*} [Category.{u} C] {D : Type*} [Category.{u} D]
    (G : C ⥤ D) [G.Faithful] {X : Cᵒᵖ ⥤ Type u}
    {U T V : C} (f : yoneda.obj U ⟶ X) (x : X.obj (op T))
    (p : V ⟶ T) (i : yoneda.obj V ⟶ yoneda.obj U)
    (h : IsPullback i (yoneda.map p) f (yonedaEquiv.symm x))
    (n : ℕ) (hfinite : Finite {g : G.obj T ⟶ G.obj V // g ≫ G.map p = 𝟙 _})
    (hcard : Nat.card {g : G.obj T ⟶ G.obj V // g ≫ G.map p = 𝟙 _} ≤ n) :
    Finite {a : T ⟶ U // f.app (op T) a = x} ∧
      Nat.card {a : T ⟶ U // f.app (op T) a = x} ≤ n := by
  classical
  let A := {a : T ⟶ U // f.app (op T) a = x}
  have hw (a : A) : yoneda.map a.val ≫ f = 𝟙 _ ≫ yonedaEquiv.symm x := by
    apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map, Category.id_comp,
      Equiv.apply_symm_apply] using a.property
  let l (a : A) : yoneda.obj T ⟶ yoneda.obj V := h.lift (yoneda.map a.val) (𝟙 _) (hw a)
  let q (a : A) : T ⟶ V := yoneda.preimage (l a)
  have hq (a : A) : yoneda.map (q a) = l a := yoneda.map_preimage _
  have hqp (a : A) : q a ≫ p = 𝟙 T := by
    apply yoneda.map_injective
    rw [Functor.map_comp, hq, show l a ≫ yoneda.map p = 𝟙 _ from h.lift_snd _ _ _]
    exact (yoneda.map_id T).symm
  let j : A → {g : G.obj T ⟶ G.obj V // g ≫ G.map p = 𝟙 _} :=
    fun a => ⟨G.map (q a), by rw [← G.map_comp, hqp, G.map_id]⟩
  have hj : Function.Injective j := by
    intro a b hab
    have hqeq : q a = q b := G.map_injective (congrArg Subtype.val hab)
    apply Subtype.ext
    apply yoneda.map_injective
    rw [← h.lift_fst (yoneda.map a.val) (𝟙 _) (hw a),
      ← h.lift_fst (yoneda.map b.val) (𝟙 _) (hw b)]
    show l a ≫ i = l b ≫ i
    rw [← hq a, ← hq b, hqeq]
  exact finite_card_le_of_injective hfinite hj hcard

/-- The test object of the big fppf site over `S` given by the spectrum of a field `k` with
structure morphism `a : Spec k ⟶ S`. -/
private noncomputable abbrev fieldTest
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (k : Type u) [Field k] (hK : B.Contains (Spec (.of k))) (a : Spec (.of k) ⟶ S) :
    AlgebraicGeometry.BigFppfOver B S hS :=
  Over.mk (⟨a⟩ : B.obj hK ⟶ B.obj hS)

/-- Universally bounded fibres yield one integer `N` bounding, uniformly in the field `k`, the
number of lifts through `f` of any section of `X` over a field test object. -/
private theorem exists_uniform_finite_card_field_fibers
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : AlgebraicGeometry.BigFppfOver B S hS) (f : yoneda.obj U ⟶ X)
    (hf : HasUniversallyBoundedFibers B S hS U f) :
    ∃ N : ℕ, ∀ (k : Type u) [Field k] (hK : B.Contains (Spec (.of k)))
      (a : Spec (.of k) ⟶ S) (x : X.obj (op (fieldTest B S hS k hK a))),
      Finite {g : fieldTest B S hS k hK a ⟶ U // f.app _ g = x} ∧
      Nat.card {g : fieldTest B S hS k hK a ⟶ U // f.app _ g = x} ≤ N := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n.toNat, ?_⟩
  intro k _ hK a x
  let T := fieldTest B S hS k hK a
  obtain ⟨V, p, i, r, hr, hp, hpb⟩ := hn k T (Iso.refl _) (yonedaEquiv.symm x)
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let := hp
  obtain ⟨hfinite, hcard⟩ := finite_card_sections_of_isFiniteLocallyFreeOfRank (G.map p) r
  apply finite_card_fiber_of_isPullback G f x p i hpb n.toNat hfinite
  exact hcard.trans (by omega)

/-- **The bound of Stacks 03JL in the form used here.** If `s : R ⟶ U` has universally bounded
fibres then one integer `N` bounds, for every field `k` in the site, the number of
`Spec k`-points of `R` lying over a given `Spec k`-point of `U`. -/
private theorem exists_uniform_finite_card_scheme_fibers
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (R U : AlgebraicGeometry.BigFppfOver B S hS) (s : R ⟶ U)
    (hs : HasUniversallyBoundedFibers B S hS R (yoneda.map s)) :
    ∃ N : ℕ, ∀ (k : Type u) [Field k] (_ : B.Contains (Spec (.of k)))
      (x : Spec (.of k) ⟶ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U),
      Finite {r : Spec (.of k) ⟶ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj R //
        r ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s = x} ∧
      Nat.card {r : Spec (.of k) ⟶ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj R //
        r ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s = x} ≤ N := by
  obtain ⟨N, hN⟩ := exists_uniform_finite_card_field_fibers B S hS R (yoneda.map s) hs
  refine ⟨N, ?_⟩
  intro k _ hK x
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let a : Spec (.of k) ⟶ S := x ≫ U.hom.hom
  let T := fieldTest B S hS k hK a
  let x' : T ⟶ U := Over.homMk (⟨x⟩ : B.obj hK ⟶ U.left) rfl
  have hbase : G.map s ≫ U.hom.hom = R.hom.hom :=
    congrArg (fun f => f.hom) s.w
  let V := {r : Spec (.of k) ⟶ G.obj R // r ≫ G.map s = x}
  let j₀ (r : V) : T ⟶ R := Over.homMk (⟨r.val⟩ : B.obj hK ⟶ R.left) (by
    apply B.inclusion.map_injective
    show r.val ≫ R.hom.hom = x ≫ U.hom.hom
    rw [← hbase, ← Category.assoc, r.property])
  have hj₀ (r : V) : j₀ r ≫ s = x' := G.map_injective r.property
  let j : V → {g : T ⟶ R // (yoneda.map s).app (op T) g = x'} :=
    fun r => ⟨j₀ r, hj₀ r⟩
  have hj : Function.Injective j := fun r q h =>
    Subtype.ext (congrArg (fun f : T ⟶ R => G.map f) (congrArg Subtype.val h))
  obtain ⟨hfin, hcard⟩ := hN k hK a x'
  exact finite_card_le_of_injective hfin hj hcard

/-- The relation cut out on `T`-points by the whole of `R` is an equivalence relation, directly
from the unit, symmetry and composition of the equivalence relation `(t, s)`. -/
private theorem equivalence_openRelationOn_top
    {R U : Scheme.{u}} (s t : R ⟶ U) (E : EquivalenceRelation t s) (T : Scheme.{u}) :
    Equivalence (openRelationOn s t ⊤ T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ⟨x ≫ E.r, Set.subset_univ _, by simp, by simp⟩
  · rintro x y ⟨r, _, rfl, rfl⟩
    exact ⟨r ≫ E.s, Set.subset_univ _,
      by rw [Category.assoc, E.symmetry₁], by rw [Category.assoc, E.symmetry₂]⟩
  · rintro x y z ⟨r, _, hr₁, hr₂⟩ ⟨q, _, hq₁, hq₂⟩
    let l : T ⟶ E.c.pt := E.isLimit.lift (PullbackCone.mk r q (hr₂.trans hq₁.symm))
    have hl₁ : l ≫ E.c.fst = r := E.isLimit.fac _ WalkingCospan.left
    have hl₂ : l ≫ E.c.snd = q := E.isLimit.fac _ WalkingCospan.right
    refine ⟨l ≫ E.t, Set.subset_univ _, ?_, ?_⟩
    · rw [Category.assoc, E.transitivity₁, ← Category.assoc, hl₁, hr₁]
    · rw [Category.assoc, E.transitivity₂, ← Category.assoc, hl₂, hq₂]

/-- The invariant with small fibres required by the subrelation statement: if every `T`-point of
`U` has at most `N` preimages under `s`, the quotient of the `T`-points of `U` by the full relation
is an invariant of the relation whose fibres are finite with at most `N` elements. -/
private theorem exists_bounded_quotient_of_bounded_relation
    {R U T : Scheme.{u}} (s t : R ⟶ U) (E : EquivalenceRelation t s) (N : ℕ)
    (hN : ∀ x : T ⟶ U, Finite {r : T ⟶ R // r ≫ s = x} ∧
      Nat.card {r : T ⟶ R // r ≫ s = x} ≤ N) :
    ∃ (β : Type u) (f : (T ⟶ U) → β),
      (∀ r : T ⟶ R, f (r ≫ t) = f (r ≫ s)) ∧
      (∀ x, Finite {a // f a = f x}) ∧ ∀ x, Nat.card {a // f a = f x} ≤ N := by
  let e : Setoid (T ⟶ U) := ⟨openRelationOn s t ⊤ T, equivalence_openRelationOn_top s t E T⟩
  let f : (T ⟶ U) → Quotient e := Quotient.mk e
  have hf (r : T ⟶ R) : f (r ≫ t) = f (r ≫ s) :=
    Quotient.sound ⟨r, Set.subset_univ _, rfl, rfl⟩
  have hbound (x : T ⟶ U) : Finite {a // f a = f x} ∧ Nat.card {a // f a = f x} ≤ N := by
    let j : {r : T ⟶ R // r ≫ s = x} → {a // f a = f x} :=
      fun r => ⟨r.val ≫ t, (hf r.val).trans (congrArg f r.property)⟩
    have hj : Function.Surjective j := by
      intro a
      obtain ⟨r, _, ht, hs⟩ := Quotient.exact a.property
      exact ⟨⟨r, hs⟩, Subtype.ext ht⟩
    let := (hN x).1
    exact ⟨Finite.of_surjective j hj, (Nat.card_le_card_of_surjective j hj).trans (hN x).2⟩
  exact ⟨Quotient e, f, hf, fun x => (hbound x).1, fun x => (hbound x).2⟩

/-- **The subrelation statement that makes the index set directed and cofinal.** For an étale
equivalence relation `(s, t)` on a quasi-compact quasi-separated `U` whose projection `s` has
universally bounded fibres, every quasi-compact open `A ⊆ R` is contained in a quasi-compact
open `A'` which is still an equivalence relation on `U`. The bound of Stacks 03JL is turned into
the geometric-fibre invariant by `exists_bounded_quotient_of_bounded_relation`. -/
theorem exists_compact_open_subrelation_of_hasUniversallyBoundedFibers
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (R U : AlgebraicGeometry.BigFppfOver B S hS) (s t : R ⟶ U)
    [Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s)]
    [Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map t)]
    [CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U)]
    [QuasiSeparatedSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U)]
    (E : EquivalenceRelation ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map t)
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s))
    (hs : HasUniversallyBoundedFibers B S hS R (yoneda.map s))
    (A : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj R).Opens)
    (hA : IsCompact (A : Set ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj R))) :
    ∃ A' : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj R).Opens,
      IsCompact (A' : Set ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj R)) ∧ A ≤ A' ∧
      IsEquivalenceRelation (A'.ι ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map t)
        (A'.ι ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s) := by
  obtain ⟨N, hN⟩ := exists_uniform_finite_card_scheme_fibers B S hS R U s hs
  let : CompactSpace U.left.obj :=
    ‹CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U)›
  let : QuasiSeparatedSpace U.left.obj :=
    ‹QuasiSeparatedSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U)›
  let : Etale s.left.hom := ‹Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s)›
  let : Etale t.left.hom := ‹Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map t)›
  refine exists_compact_open_subrelation_of_bounded_geometric_fibers_in_site
    B R.left.property U.left.property _ _ E N ?_ A hA
  intro K _ _ hK
  exact exists_bounded_quotient_of_bounded_relation _ _ E N (hN K hK)

/-- The identity of a presheaf has the relative form of any morphism property satisfied by all
isomorphisms. -/
theorem presheafProperty_id
    {C : Type*} [Category.{u} C] (P : MorphismProperty C)
    (hP : ∀ {U V : C} (f : U ⟶ V), IsIso f → P f) (F : Cᵒᵖ ⥤ Type u) : P.presheaf (𝟙 F) := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
  intro A D g fst snd hpb
  have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
  have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
  exact hP snd inferInstance

/-- An equivalence relation in a slice category `Over S` gives an equivalence relation on the
underlying objects, the two projections remaining jointly monic. -/
noncomputable def equivalenceRelation_forget
    {C : Type*} [Category.{v₁} C] [HasPullbacks C] {S : C} {R U : Over S}
    {t s : R ⟶ U} (E : EquivalenceRelation t s) : EquivalenceRelation t.left s.left := by
  let : JointlyMono₂ ((Over.forget S).map t) ((Over.forget S).map s) := {
    right_cancellation := by
      intro T a b ht hs
      change a ≫ t.left = b ≫ t.left at ht
      change a ≫ s.left = b ≫ s.left at hs
      let a' : Over.mk (a ≫ R.hom) ⟶ R := Over.homMk a rfl
      let b' : Over.mk (a ≫ R.hom) ⟶ R := Over.homMk b (by
        change b ≫ R.hom = a ≫ R.hom
        rw [← Over.w t, ← Category.assoc, ← Category.assoc, ht])
      have h : a' = b' := E.right_cancellation a' b'
        (Over.OverMorphism.ext ht) (Over.OverMorphism.ext hs)
      exact congrArg CommaMorphism.left h }
  exact {
    __ := E.toReflexiveRelation.map (Over.forget S)
    __ := E.toSymmetricRelation.map (Over.forget S)
    __ := E.toTransitiveRelation.map (Over.forget S) }

/-- Conversely, an equivalence relation on the underlying objects of a pair of objects of `Over S`
lifts to an equivalence relation in `Over S`. -/
noncomputable def equivalenceRelation_over
    {C : Type*} [Category.{v₁} C] [HasPullbacks C] {S : C} {R U : Over S}
    {t s : R ⟶ U} (E : EquivalenceRelation t.left s.left) : EquivalenceRelation t s := by
  let P := pullback s t
  let a := (pullback.fst s t).left
  let b := (pullback.snd s t).left
  have hab : a ≫ s.left = b ≫ t.left :=
    congrArg CommaMorphism.left (pullback.condition (f := s) (g := t))
  let l : P.left ⟶ E.c.pt := E.isLimit.lift (PullbackCone.mk a b hab)
  have hl₁ : l ≫ E.c.fst = a := E.isLimit.fac _ WalkingCospan.left
  have hl₂ : l ≫ E.c.snd = b := E.isLimit.fac _ WalkingCospan.right
  have hc₁ : (l ≫ E.t) ≫ t.left = a ≫ t.left := by
    rw [Category.assoc, E.transitivity₁, ← Category.assoc, hl₁]
  have hc₂ : (l ≫ E.t) ≫ s.left = b ≫ s.left := by
    rw [Category.assoc, E.transitivity₂, ← Category.assoc, hl₂]
  refine {
    right_cancellation := fun {_} f g ht hs => Over.OverMorphism.ext
      (E.right_cancellation f.left g.left (congrArg CommaMorphism.left ht)
        (congrArg CommaMorphism.left hs))
    r := Over.homMk E.r (by rw [← Over.w t, ← Category.assoc, E.reflexivity₁, Category.id_comp])
    reflexivity₁ := Over.OverMorphism.ext E.reflexivity₁
    reflexivity₂ := Over.OverMorphism.ext E.reflexivity₂
    s := Over.homMk E.s (by
      calc
        E.s ≫ R.hom = E.s ≫ (t.left ≫ U.hom) := congrArg (E.s ≫ ·) (Over.w t).symm
        _ = s.left ≫ U.hom := by rw [← Category.assoc, E.symmetry₁]
        _ = R.hom := Over.w s)
    symmetry₁ := Over.OverMorphism.ext E.symmetry₁
    symmetry₂ := Over.OverMorphism.ext E.symmetry₂
    c := pullback.cone s t
    isLimit := pullback.isLimit s t
    t := Over.homMk (l ≫ E.t) (by
      rw [← Over.w t, ← Category.assoc, hc₁, Category.assoc, Over.w t]
      exact Over.w (pullback.fst s t))
    transitivity₁ := Over.OverMorphism.ext hc₁
    transitivity₂ := Over.OverMorphism.ext hc₂ }

/-- If `yoneda.map s` is étale as a morphism of presheaves on the site, then `s` is étale as a
morphism of schemes. -/
theorem scheme_etale_of_isEtale_yoneda
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R U : AlgebraicGeometry.BigFppfOver B S hS} (s : R ⟶ U)
    (hs : AlgebraicGeometry.Space.IsEtale B S hS (yoneda.map s)) :
    Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s) := by
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) G
  let : P.IsStableUnderBaseChange := MorphismProperty.inverseImage_isStableUnderBaseChange G _
  have hid : P.presheaf (𝟙 (yoneda.obj R)) :=
    presheafProperty_id P (fun {_ _} f hf => by
      let := hf
      show Etale (G.map f)
      infer_instance) _
  apply (MorphismProperty.relative_map_iff (F := yoneda) (P := P)).mp
  simpa only [Category.id_comp] using hs R (𝟙 _) hid

/-- The sheaf on the big fppf site represented by an object `U` of the site. -/
noncomputable def sheafOfScheme
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS) :
    Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u) :=
  ⟨yoneda.obj U, (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U).isSheaf⟩

/-- A representable surjective étale morphism `q : yoneda.obj U ⟶ Y.obj` is locally surjective for
the fppf topology, surjective étale morphisms being flat, locally of finite presentation and
surjective. -/
theorem atlas_isLocallySurjective
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u)}
    {U : AlgebraicGeometry.BigFppfOver B S hS} (q : yoneda.obj U ⟶ Y.obj)
    (hq : (MorphismProperty.inverseImage (@Surjective.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q) :
    Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS) q := by
  apply isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective
    B S hS (show sheafOfScheme B S hS U ⟶ Y from ⟨q⟩)
  refine ⟨hq.1, ?_⟩
  intro T V f fst snd hp
  let : Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map snd) := he.2 f fst snd hp
  exact ⟨inferInstance, inferInstance, hq.2 f fst snd hp⟩

/-- A locally surjective morphism of sheaves `q : U ⟶ X` exhibits `X` as the coequalizer of its
kernel pair: `q` is an effective epimorphism, so `Cofork.ofπ q` is a colimit. -/
noncomputable def sheafKernelPairIsColimit
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    [HasSheafify J (Type u₂)]
    {R U X : Sheaf J (Type u₂)} (s t : R ⟶ U) (q : U ⟶ X)
    (hp : IsPullback s.hom t.hom q.hom q.hom)
    (hq : Presheaf.IsLocallySurjective J q.hom) :
    IsColimit (Cofork.ofπ q (show s ≫ q = t ≫ q from Sheaf.hom_ext hp.w)) := by
  let : Sheaf.IsLocallySurjective q := hq
  let : Epi q := Sheaf.epi_of_isLocallySurjective' q
  let : IsRegularEpi q := IsRegularEpiCategory.regularEpiOfEpi q
  let h : IsPullback s t q q := hp.of_map_of_faithful (sheafToPresheaf J _)
  exact isColimitCoforkOfEffectiveEpi q _ h.isLimit

/-- A representable surjective atlas of an algebraic space is surjective on points in the sense of
Stacks 03BU, the two notions agreeing by Stacks 03MD. -/
theorem atlas_isSurjective
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    {U : AlgebraicGeometry.BigFppfOver B S hS} (q : yoneda.obj U ⟶ Y)
    (hq : (MorphismProperty.inverseImage (@Surjective.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q) :
    IsSurjective B S hS q :=
  (AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective B S hS
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) hY q hq.1).mp hq

/-- The object of the big fppf site over `S` given by an open subscheme `A` of (the scheme
underlying) an object `R`, with structure morphism `A.ι ≫ R.hom`. -/
noncomputable def openObject
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (R : AlgebraicGeometry.BigFppfOver B S hS)
    (A : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj R).Opens) :
    AlgebraicGeometry.BigFppfOver B S hS :=
  Over.mk (Y := B.obj ((Scheme.size_coe_opens_le R.left.obj A).trans_lt R.left.property))
    (ObjectProperty.homMk (A.ι ≫ R.hom.hom))

/-- The open immersion `openObject B S hS R A ⟶ R` of the site induced by `A.ι`. -/
noncomputable def openObjectι
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (R : AlgebraicGeometry.BigFppfOver B S hS)
    (A : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj R).Opens) :
    openObject B S hS R A ⟶ R :=
  Over.homMk (ObjectProperty.homMk A.ι) rfl

/-- If an open `A` of `R` restricts `(s, t)` to an equivalence relation of schemes, then the pair
`(openObjectι ≫ s, openObjectι ≫ t)` is an étale equivalence relation on `U` in the site, so the
quotient sheaf `U / A` is an algebraic space by Stacks 02WW. -/
theorem openObject_isEtaleEquivalenceRelation
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R U : AlgebraicGeometry.BigFppfOver B S hS} (s t : R ⟶ U)
    [Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s)]
    [Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map t)]
    (A : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj R).Opens)
    (hA : IsEquivalenceRelation (A.ι ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map t)
      (A.ι ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s)) :
    Stacks.Groupoids.IsEtaleEquivalenceRelation (relation B S hS
      (openObjectι B S hS R A ≫ s) (openObjectι B S hS R A ≫ t)) := by
  have ht : (relation B S hS
      (openObjectι B S hS R A ≫ s) (openObjectι B S hS R A ≫ t)).target =
      (Over.post B.inclusion).map (openObjectι B S hS R A ≫ t) := prod.lift_fst _ _
  have hs : (relation B S hS
      (openObjectι B S hS R A ≫ s) (openObjectι B S hS R A ≫ t)).source =
      (Over.post B.inclusion).map (openObjectι B S hS R A ≫ s) := prod.lift_snd _ _
  refine { isEquivalenceRelation := ?_, etale_source := ?_, etale_target := ?_ }
  · rw [ht, hs]
    exact ⟨⟨equivalenceRelation_over hA.nonempty_equivalenceRelation.some⟩⟩
  · rw [hs]
    show Etale (A.ι ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s)
    infer_instance
  · rw [ht]
    show Etale (A.ι ≫ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map t)
    infer_instance

/-- If `s` is étale as a morphism of schemes, then `yoneda.map s` is étale as a morphism of
presheaves on the site. -/
theorem isEtale_yoneda_of_scheme_etale
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R U : AlgebraicGeometry.BigFppfOver B S hS} (s : R ⟶ U)
    [Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s)] :
    AlgebraicGeometry.Space.IsEtale B S hS (yoneda.map s) := by
  apply AlgebraicGeometry.Space.isEtale_of_presheaf_etale B S hS
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u}) G
  let : P.IsStableUnderBaseChange := MorphismProperty.inverseImage_isStableUnderBaseChange G _
  exact (MorphismProperty.relative_map_iff (F := yoneda) (P := P)).mpr
    (show Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s) from inferInstance)

/-- The diagram of quotients: given a diagram `R` of relations on a fixed object `U` and, for each
index, a coequalizer `Q i` of `(s.app i, t.app i)` with projection `q i`, the functor sending
`i` to `Q i` and a morphism to the map induced by the coequalizer property. -/
@[implicit_reducible] noncomputable def quotientDiagram
    {C : Type u₁} [Category.{v₁} C] {I : Type u₂} [Category.{v₂} I]
    (R : I ⥤ C) (U : C) (s t : R ⟶ (Functor.const I).obj U)
    (Q : I → C) (q : ∀ i, U ⟶ Q i) (hw : ∀ i, s.app i ≫ q i = t.app i ≫ q i)
    (hq : ∀ i, IsColimit (Cofork.ofπ (q i) (hw i))) : I ⥤ C where
  obj := Q
  map {i j} f := Cofork.IsColimit.desc (hq i) (q j) (by
    have hs := s.naturality f
    have ht := t.naturality f
    dsimp at hs ht
    rw [Category.comp_id] at hs ht
    rw [← hs, ← ht, Category.assoc, Category.assoc, hw])
  map_id i := by
    apply Cofork.IsColimit.hom_ext (hq i)
    change q i ≫ Cofork.IsColimit.desc (hq i) _ _ = q i ≫ 𝟙 _
    exact (Cofork.IsColimit.π_desc' (hq i) _ _).trans (Category.comp_id _).symm
  map_comp {i j k} f g := by
    apply Cofork.IsColimit.hom_ext (hq i)
    change q i ≫ Cofork.IsColimit.desc (hq i) _ _ =
      q i ≫ (Cofork.IsColimit.desc (hq i) _ _ ≫ Cofork.IsColimit.desc (hq j) _ _)
    apply (Cofork.IsColimit.π_desc' (hq i) _ _).trans
    symm
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (Cofork.IsColimit.π_desc' (hq i) _ _)).trans
        (Cofork.IsColimit.π_desc' (hq j) _ _))

/-- The transition maps of `quotientDiagram` are compatible with the quotient projections:
`q i ≫ map f = q j`. -/
theorem quotientDiagram_map
    {C : Type u₁} [Category.{v₁} C] {I : Type u₂} [Category.{v₂} I]
    (R : I ⥤ C) (U : C) (s t : R ⟶ (Functor.const I).obj U)
    (Q : I → C) (q : ∀ i, U ⟶ Q i) (hw : ∀ i, s.app i ≫ q i = t.app i ≫ q i)
    (hq : ∀ i, IsColimit (Cofork.ofπ (q i) (hw i))) {i j : I} (f : i ⟶ j) :
    q i ≫ (quotientDiagram R U s t Q q hw hq).map f = q j :=
  Cofork.IsColimit.π_desc' (hq i) _ _

/-- The cocone on `quotientDiagram` with vertex `X` induced by a morphism `p : U ⟶ X` coequalizing
every relation of the diagram. -/
@[implicit_reducible] noncomputable def quotientCocone
    {C : Type u₁} [Category.{v₁} C] {I : Type u₂} [Category.{v₂} I]
    (R : I ⥤ C) (U : C) (s t : R ⟶ (Functor.const I).obj U)
    (Q : I → C) (q : ∀ i, U ⟶ Q i) (hw : ∀ i, s.app i ≫ q i = t.app i ≫ q i)
    (hq : ∀ i, IsColimit (Cofork.ofπ (q i) (hw i)))
    {X : C} (p : U ⟶ X) (hp : ∀ i, s.app i ≫ p = t.app i ≫ p) :
    Cocone (quotientDiagram R U s t Q q hw hq) where
  pt := X
  ι := {
    app i := Cofork.IsColimit.desc (hq i) p (hp i)
    naturality {i j} f := by
      apply Cofork.IsColimit.hom_ext (hq i)
      change q i ≫ (_ ≫ _) = q i ≫ (_ ≫ 𝟙 X)
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) (quotientDiagram_map R U s t Q q hw hq f)).trans
          ((Cofork.IsColimit.π_desc' (hq j) _ _).trans
            ((Cofork.IsColimit.π_desc' (hq i) _ _).symm.trans
              (congrArg (q i ≫ ·) (Category.comp_id _).symm)))) }

/-- The coprojections of `quotientCocone` are compatible with the quotient projections:
`q i ≫ ι.app i = p`. -/
theorem quotientCocone_ι
    {C : Type u₁} [Category.{v₁} C] {I : Type u₂} [Category.{v₂} I]
    (R : I ⥤ C) (U : C) (s t : R ⟶ (Functor.const I).obj U)
    (Q : I → C) (q : ∀ i, U ⟶ Q i) (hw : ∀ i, s.app i ≫ q i = t.app i ≫ q i)
    (hq : ∀ i, IsColimit (Cofork.ofπ (q i) (hw i)))
    {X : C} (p : U ⟶ X) (hp : ∀ i, s.app i ≫ p = t.app i ≫ p) (i : I) :
    q i ≫ (quotientCocone R U s t Q q hw hq p hp).ι.app i = p :=
  Cofork.IsColimit.π_desc' (hq i) _ _

/-- `quotientCocone` is a colimit when the index category is filtered, `X` is the coequalizer of a
pair `(a, b)` with projection `p`, and the relations of the diagram jointly generate `(a, b)`.
This is what identifies `X = U / R` with the colimit of the stages `U / R'`. -/
noncomputable def quotientCoconeIsColimit
    {C : Type u₁} [Category.{v₁} C] {I : Type u₂} [Category.{v₂} I] [IsFiltered I]
    (R : I ⥤ C) (U : C) (s t : R ⟶ (Functor.const I).obj U)
    (Q : I → C) (q : ∀ i, U ⟶ Q i) (hw : ∀ i, s.app i ≫ q i = t.app i ≫ q i)
    (hq : ∀ i, IsColimit (Cofork.ofπ (q i) (hw i)))
    {X V : C} (p : U ⟶ X) (a b : V ⟶ U) (hp : a ≫ p = b ≫ p)
    (hcolim : IsColimit (Cofork.ofπ p hp))
    (hpi : ∀ i, s.app i ≫ p = t.app i ≫ p)
    (hgen : ∀ (Y : C) (f : U ⟶ Y),
      (∀ i, s.app i ≫ f = t.app i ≫ f) → a ≫ f = b ≫ f) :
    IsColimit (quotientCocone R U s t Q q hw hq p hpi) :=
  isColimit_of_common_quotient a b _ _ R.obj s.app t.app p q hp hw hcolim hq
    (quotientCocone_ι R U s t Q q hw hq p hpi)
    (quotientDiagram_map R U s t Q q hw hq) hgen

/-- A family of flat, locally of finite presentation morphisms `V i ⟶ T` of the site which is
jointly surjective on points generates a covering sieve of the big fppf topology. -/
theorem fppf_cover_sieve_mem
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T : AlgebraicGeometry.BigFppfOver B S hS} {I : Type (u + 1)}
    (V : I → AlgebraicGeometry.BigFppfOver B S hS) (f : ∀ i, V i ⟶ T)
    (hcov : ∀ x : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T,
      ∃ i y, ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (f i)) y = x)
    (hf : ∀ i, Flat ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (f i)) ∧
      LocallyOfFinitePresentation ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (f i))) :
    Sieve.ofArrows V f ∈ AlgebraicGeometry.BigFppfOver.topology B S hS T := by
  let E : Covering.{u + 1, u, u + 1} B.Schemes :=
    ⟨T.left, ⟨I, fun i => (V i).left, fun i => (f i).left⟩⟩
  have hE : _root_.AlgebraicGeometry.IsFppfCovering E := by
    show E.2.presieve₀.map B.inclusion ∈ Scheme.fppfPrecoverage T.left.obj
    rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows,
      Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨hcov, hf⟩
  obtain ⟨⟨T', E'⟩, hE', hcomb⟩ := B.fppf_has_representative E hE
  have hpre : E.2.presieve₀ ∈ B.precoverage T.left := by
    obtain ⟨he, hc⟩ := hcomb
    change T.left = T' at he
    cases he
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hc]
    exact ⟨E', rfl, hE'⟩
  rw [AlgebraicGeometry.BigFppfOver.topology, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck hpre

/-- Two morphisms from a representable presheaf to a sheaf which agree after composing with every
member of a covering family are equal. -/
private theorem sheaf_hom_ext_of_cover
    {C : Type u₁} [Category.{u₂} C] (J : GrothendieckTopology C)
    {R : C} {Y : Sheaf J (Type u₂)} {I : Type v₁}
    (V : I → C) (v : ∀ i, V i ⟶ R) (hcover : Sieve.ofArrows V v ∈ J R)
    (a b : yoneda.obj R ⟶ Y.obj)
    (h : ∀ i, yoneda.map (v i) ≫ a = yoneda.map (v i) ≫ b) : a = b := by
  apply yonedaEquiv.injective
  apply (((isSheaf_iff_isSheaf_of_type J Y.obj).mp Y.property _ hcover).isSeparatedFor).ext
  intro T f hf
  obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hf
  have hi := congrArg (fun k => k g) (congr_app (h i) (op T))
  simpa [yonedaEquiv, ← NatTrans.naturality_apply] using hi

/-- Two morphisms from the presheaf represented by `R` to a sheaf which agree on a family of opens
of `R` whose supremum is `⊤` are equal, such a family being an fppf cover. -/
theorem sheaf_hom_ext_of_open_cover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (R : AlgebraicGeometry.BigFppfOver B S hS) {I : Type u}
    (A : I → ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj R).Opens)
    (hA : (⨆ i, A i) = ⊤)
    (Y : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u))
    (a b : yoneda.obj R ⟶ Y.obj)
    (h : ∀ i, yoneda.map (openObjectι B S hS R (A i)) ≫ a =
      yoneda.map (openObjectι B S hS R (A i)) ≫ b) : a = b := by
  apply sheaf_hom_ext_of_cover (AlgebraicGeometry.BigFppfOver.topology B S hS)
    (fun i : ULift.{u + 1} I => openObject B S hS R (A i.down))
    (fun i => openObjectι B S hS R (A i.down)) ?_ a b (fun i => h i.down)
  apply fppf_cover_sieve_mem
  · intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show x ∈ ⨆ i, A i by rw [hA]; trivial)
    exact ⟨⟨i⟩, ⟨x, hi⟩, rfl⟩
  · intro i
    show Flat (A i.down).ι ∧ LocallyOfFinitePresentation (A i.down).ι
    exact ⟨inferInstance, inferInstance⟩

/-- The morphism of the site `openObject R A ⟶ openObject R A'` induced by an inclusion `A ≤ A'` of
opens of `R`. -/
noncomputable def openObjectMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (R : AlgebraicGeometry.BigFppfOver B S hS)
    {A A' : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj R).Opens} (h : A ≤ A') :
    openObject B S hS R A ⟶ openObject B S hS R A' :=
  Over.homMk (ObjectProperty.homMk (R.left.obj.homOfLE h)) (by
    apply ObjectProperty.hom_ext
    change R.left.obj.homOfLE h ≫ (A'.ι ≫ R.hom.hom) = A.ι ≫ R.hom.hom
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) (Scheme.homOfLE_ι R.left.obj h)))

/-- The maps between open objects are compatible with their immersions into `R`:
`openObjectMap h ≫ openObjectι A' = openObjectι A`. -/
theorem openObjectMap_ι
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (R : AlgebraicGeometry.BigFppfOver B S hS)
    {A A' : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj R).Opens} (h : A ≤ A') :
    openObjectMap B S hS R h ≫ openObjectι B S hS R A' = openObjectι B S hS R A := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact Scheme.homOfLE_ι _ h

/-- The functor sending an object of the big fppf site to the sheaf it represents. -/
@[implicit_reducible] noncomputable def sheafOfSchemeFunctor
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    AlgebraicGeometry.BigFppfOver B S hS ⥤
      Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type u) where
  obj U := sheafOfScheme B S hS U
  map f := ⟨yoneda.map f⟩
  map_id U := Sheaf.hom_ext (yoneda.map_id U)
  map_comp f g := Sheaf.hom_ext (yoneda.map_comp f g)

/-- A section `ξ : yoneda.obj T ⟶ X` over a quasi-compact `T` lifts along a surjective étale atlas
`q : yoneda.obj U ⟶ X` after a quasi-compact surjective étale cover `v : W ⟶ T`: shrink the
representing cover to a quasi-compact open that still surjects onto `T`. -/
theorem exists_compact_etale_lift
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U T : AlgebraicGeometry.BigFppfOver B S hS}
    (q : yoneda.obj U ⟶ X)
    (hq : (MorphismProperty.inverseImage (@Surjective.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf q)
    [CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T)]
    (ξ : yoneda.obj T ⟶ X) :
    ∃ (W : AlgebraicGeometry.BigFppfOver B S hS) (v : W ⟶ T) (w : W ⟶ U),
      CompactSpace ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj W) ∧
      Surjective ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map v) ∧
      Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map v) ∧
      yoneda.map w ≫ q = yoneda.map v ≫ ξ := by
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  obtain ⟨V, v, w, hpb⟩ := hq.1 ξ
  let w' : V ⟶ U := yoneda.preimage w
  have hw : yoneda.map w' = w := yoneda.map_preimage w
  let : Surjective (G.map v) := hq.2 ξ w v hpb
  let : Etale (G.map v) := he.2 ξ w v hpb
  obtain ⟨A, hAc, hA⟩ := IsOpenMap.exists_opens_image_eq_of_prespectralSpace
    (G.map v).continuous (G.map v).isOpenMap
    (show Set.univ ⊆ Set.range (G.map v) by rw [Surjective.surj.range_eq])
    isOpen_univ isCompact_univ
  let i := openObjectι B S hS V A
  refine ⟨openObject B S hS V A, i ≫ v, i ≫ w',
    isCompact_iff_compactSpace.mp hAc, ?_, ?_, ?_⟩
  · refine ⟨?_⟩
    intro x
    have hx : x ∈ (G.map v) '' (A : Set (G.obj V)) := hA.symm ▸ Set.mem_univ x
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨y, hy⟩, rfl⟩
  · show Etale ((Scheme.Opens.ι (X := G.obj V) A) ≫ G.map v)
    infer_instance
  · rw [yoneda.map_comp, yoneda.map_comp, Category.assoc, Category.assoc, hw, hpb.w]

end ReasonableApproximation

end AlgebraicGeometry.Space

end
