module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationExcisionCounitMono

/-!
# The counit of the dependent product is an isomorphism

Stacks 0BGY produces the inverse of the base-change functor as the dependent product
`X = Π_f Y`, and the second computation it makes with it is that `X ×_{g,W,f} V → Y` is an
isomorphism. `StacksFrontier/AlgebraicGeometry/Spaces/ModificationExcisionCounitMono.lean` proves
that this comparison — the counit of the dependent product — is injective on sections. This
file proves that it is surjective, and concludes that it is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.existsUnique_depProdValue`: the value a section of the dependent
  product must take at one index is uniquely determined, and exists.
* `AlgebraicGeometry.Space.exists_depProdSection_of_section`: every section of `Y` is the value
  at the identity of a section of the dependent product over its own image in `W`.
* `AlgebraicGeometry.Space.surjective_depProdCounitApp_of_diagonalComplement` and
  `AlgebraicGeometry.Space.surjective_depProdCounitApp`: the counit is surjective on sections.
* `AlgebraicGeometry.Space.isIso_depProdCounitApp_left` and
  `AlgebraicGeometry.Space.isIso_depProdCounitApp`: **the computation
  `X ×_{g,W,f} V = Y` of Stacks 0BGY**, as an isomorphism of presheaves and as an isomorphism
  in `CategoryTheory.Over V`.

## Implementation notes

Surjectivity is a gluing construction rather than a separation argument: given a section `z` of
`Y` over `A`, with image `v` in `V` and `w = f v` in `W`, the family of values witnessing it has
to be *built*.

The labour is concentrated in `AlgebraicGeometry.Space.existsUnique_depProdValue`, which
produces one value. At an index `(h, u)` — a morphism `h : A' ⟶ A` and a section `u` of `V`
over `A'` lying over `h^* w` — the pair `(v|_h, u)` is a section `s` of `V ×_W V`, and the
source proof's decomposition `V ×_W V = Δ(V) ⨿ U` covers `A'` by arrows `k` along which the
restriction of `s` lies either in the complementary piece `C`, where `u|_k` lies over `W⁰` and
has a *unique* lift to `Y`, or in the range of the diagonal, where `u|_k = v|_{k ≫ h}` and the
value is forced to be `z|_{k ≫ h}`. Those two prescriptions agree on a common refinement
because the `C` prescription is unique wherever it applies, so they amalgamate in the sheaf
`Y.left`.

The value is characterised by two properties: that it lies over `u`, and that it restricts to
`z|_{k ≫ h}` along every `k` for which `u|_k = v|_{k ≫ h}`. Those are stated without reference
to `s`, which is legitimate because a section of `V ×_W V` lies in the range of the diagonal
exactly when its two projections agree — the two projections determine the section, so the
candidate diagonal point is their common value. Stating the characterisation this way is what
makes the three laws of the resulting family short: `over` is the first property verbatim, and
`naturality` and the identity value follow from *uniqueness*, since in each case both sides
have the two properties for the same index. In particular the two-case analysis is done once,
inside this lemma, rather than once per law.

`V` is needed to be a sheaf as well as `Y.left`: the glued value lies over `u` only because
that can be checked locally, and locality for sections of `V` is separatedness of `V`.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Presheaf Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The value forced at one index -/

/-- **The value of a family of the dependent product is forced at every index, and exists.**
Let `z` be a section of `Y` over `A`, lying over `v`, and let `u` be a section of `V` over `A'`
with the same image in `W` as `v|_g`. Then there is exactly one section `t` of `Y` over `A'`
which lies over `u` and restricts to `z|_{k ≫ g}` along every `k` with `u|_k = v|_{k ≫ g}`.

The second condition is the diagonal prescription of Stacks 0BGY: `u|_k = v|_{k ≫ g}` says
exactly that the section `(v|_g, u)` of `V ×_W V`, restricted along `k`, lies in the range of
the relative diagonal. Where it does not, the decomposition puts the section in the piece
lying over the open complement of `T`, and there a lift of `u|_k` to `Y` is unique. -/
theorem existsUnique_depProdValue (f : V ⟶ W) (T : Subfunctor W) (Y : Over V)
    (hY : IsIso (((openComplement B S hS T).preimage f).fromPreimage Y.hom))
    (hVsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) V)
    (hYsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y.left)
    (C : Subfunctor (pullback f f))
    (hC : C ≤ (openComplement B S hS T).preimage (pullback.fst f f ≫ f))
    (hcov : (C ⊔ Subfunctor.range (pullback.diagonal f)).sheafify
      (BigFppfOver.topology B S hS) = ⊤)
    {A : BigFppfOver B S hS} (z : Y.left.obj (op A)) (v : V.obj (op A))
    (hzv : Y.hom.app (op A) z = v)
    {A' : BigFppfOver B S hS} (g : A' ⟶ A) (u : V.obj (op A'))
    (hu : f.app (op A') u = f.app (op A') (V.map g.op v)) :
    ∃! t : Y.left.obj (op A'),
      Y.hom.app (op A') t = u ∧
      ∀ (A'' : BigFppfOver B S hS) (k : A'' ⟶ A'),
        V.map k.op u = V.map (k ≫ g).op v →
        Y.left.map k.op t = Y.left.map (k ≫ g).op z := by
  classical
  have hVsq : ∀ A₀ : (BigFppfOver B S hS)ᵒᵖ,
      IsPullback ((pullback.fst f f).app A₀) ((pullback.snd f f).app A₀)
        (f.app A₀) (f.app A₀) := fun A₀ =>
    (IsPullback.of_hasPullback f f).map ((evaluation _ (Type u)).obj A₀)
  -- The pair `(v|_g, u)`, as a section of `V ×_W V`.
  obtain ⟨s, hs₁, hs₂⟩ := Types.exists_of_isPullback (hVsq (op A'))
    (V.map g.op v) u hu.symm
  have hrfst : ∀ (A'' : BigFppfOver B S hS) (k : A'' ⟶ A'),
      (pullback.fst f f).app (op A'') ((pullback f f).map k.op s)
        = V.map (k ≫ g).op v := by
    intro A'' k
    rw [NatTrans.naturality_apply, hs₁, ← Functor.map_comp_apply, ← op_comp]
  have hrsnd : ∀ (A'' : BigFppfOver B S hS) (k : A'' ⟶ A'),
      (pullback.snd f f).app (op A'') ((pullback f f).map k.op s) = V.map k.op u := by
    intro A'' k
    rw [NatTrans.naturality_apply, hs₂]
  -- Lying in the range of the diagonal is having equal projections.
  have hdiagIff : ∀ (A'' : BigFppfOver B S hS) (k : A'' ⟶ A'),
      (pullback f f).map k.op s
          ∈ (Subfunctor.range (pullback.diagonal f)).obj (op A'') ↔
        V.map k.op u = V.map (k ≫ g).op v := by
    intro A'' k
    constructor
    · intro hk
      obtain ⟨t, ht⟩ := hk
      have hd₁ : (pullback.fst f f).app (op A'') ((pullback f f).map k.op s) = t := by
        rw [← ht]
        exact ConcreteCategory.congr_hom
          (NatTrans.congr_app (pullback.diagonal_fst f) (op A'')) t
      have hd₂ : (pullback.snd f f).app (op A'') ((pullback f f).map k.op s) = t := by
        rw [← ht]
        exact ConcreteCategory.congr_hom
          (NatTrans.congr_app (pullback.diagonal_snd f) (op A'')) t
      rw [← hrsnd A'' k, ← hrfst A'' k, hd₁, hd₂]
    · intro hk
      refine ⟨(pullback.fst f f).app (op A'') ((pullback f f).map k.op s), ?_⟩
      refine Types.ext_of_isPullback (hVsq (op A'')) ?_ ?_
      · exact ConcreteCategory.congr_hom
          (NatTrans.congr_app (pullback.diagonal_fst f) (op A'')) _
      · refine Eq.trans (ConcreteCategory.congr_hom
          (NatTrans.congr_app (pullback.diagonal_snd f) (op A'')) _) ?_
        rw [hrfst A'' k, hrsnd A'' k, hk]
        simp
  -- On the complementary piece the index lies over the open complement of `T`.
  have hmemW₀ : ∀ (A'' : BigFppfOver B S hS) (k : A'' ⟶ A'),
      (pullback f f).map k.op s ∈ C.obj (op A'') →
      f.app (op A'') (V.map k.op u) ∈ (openComplement B S hS T).obj (op A'') := by
    intro A'' k hk
    have hmem₀ := hC _ hk
    change (pullback.fst f f ≫ f).app (op A'')
      ((pullback f f).map k.op s) ∈ (openComplement B S hS T).obj (op A'') at hmem₀
    rw [NatTrans.comp_app, ConcreteCategory.comp_apply] at hmem₀
    have hw := ConcreteCategory.congr_hom (hVsq (op A'')).w ((pullback f f).map k.op s)
    simp only [ConcreteCategory.comp_apply] at hw
    rw [← hrsnd A'' k, ← hw]
    exact hmem₀
  -- Hence a lift of the index to `Y` exists there, and is unique.
  have hlift : ∀ (A'' : BigFppfOver B S hS) (k : A'' ⟶ A'),
      (pullback f f).map k.op s ∈ C.obj (op A'') →
      ∃ t : Y.left.obj (op A''), Y.hom.app (op A'') t = V.map k.op u := by
    intro A'' k hk
    exact exists_app_eq_of_mem B S hS Y.hom ((openComplement B S hS T).preimage f) hY
      (hmemW₀ A'' k hk)
  have hsepC : ∀ (A'' : BigFppfOver B S hS) (k : A'' ⟶ A'),
      (pullback f f).map k.op s ∈ C.obj (op A'') →
      ∀ t₁ t₂ : Y.left.obj (op A''), Y.hom.app (op A'') t₁ = V.map k.op u →
        Y.hom.app (op A'') t₂ = V.map k.op u → t₁ = t₂ := by
    intro A'' k hk t₁ t₂ h₁ h₂
    refine eq_of_app_eq_of_mem B S hS Y.hom ((openComplement B S hS T).preimage f) hY
      (h₁.trans h₂.symm) ?_
    change f.app (op A'') (Y.hom.app (op A'') t₁) ∈ (openComplement B S hS T).obj (op A'')
    rw [h₁]
    exact hmemW₀ A'' k hk
  -- The decomposition covers `A'`.
  have hRmem : (C ⊔ Subfunctor.range (pullback.diagonal f)).sieveOfSection s
      ∈ BigFppfOver.topology B S hS A' := by
    have hs : s ∈ ((C ⊔ Subfunctor.range (pullback.diagonal f)).sheafify
        (BigFppfOver.topology B S hS)).obj (op A') := by
      rw [hcov]; trivial
    exact hs
  -- Uniqueness, from separatedness of `Y.left` on that covering.
  have huniq : ∀ t₁ t₂ : Y.left.obj (op A'),
      (Y.hom.app (op A') t₁ = u ∧ ∀ (A'' : BigFppfOver B S hS) (k : A'' ⟶ A'),
        V.map k.op u = V.map (k ≫ g).op v →
        Y.left.map k.op t₁ = Y.left.map (k ≫ g).op z) →
      (Y.hom.app (op A') t₂ = u ∧ ∀ (A'' : BigFppfOver B S hS) (k : A'' ⟶ A'),
        V.map k.op u = V.map (k ≫ g).op v →
        Y.left.map k.op t₂ = Y.left.map (k ≫ g).op z) →
      t₁ = t₂ := by
    intro t₁ t₂ ht₁ ht₂
    refine eq_of_locally_eq B S hS hYsheaf
      ((C ⊔ Subfunctor.range (pullback.diagonal f)).sieveOfSection s) hRmem ?_
    intro A'' k hk
    rcases hk with hkC | hkD
    · refine hsepC A'' k hkC _ _ ?_ ?_
      · rw [NatTrans.naturality_apply, ht₁.1]
      · rw [NatTrans.naturality_apply, ht₂.1]
    · rw [ht₁.2 A'' k ((hdiagIff A'' k).1 hkD), ht₂.2 A'' k ((hdiagIff A'' k).1 hkD)]
  -- The forced value on each member of the covering sieve.
  have hforced : ∀ (A'' : BigFppfOver B S hS) (k : A'' ⟶ A'),
      ((C ⊔ Subfunctor.range (pullback.diagonal f)).sieveOfSection s).arrows k →
      ∃ t : Y.left.obj (op A''),
        Y.hom.app (op A'') t = V.map k.op u ∧
        ((pullback f f).map k.op s ∉ C.obj (op A'') →
          t = Y.left.map (k ≫ g).op z) := by
    intro A'' k hk
    by_cases hc : (pullback f f).map k.op s ∈ C.obj (op A'')
    · exact ⟨(hlift A'' k hc).choose, (hlift A'' k hc).choose_spec, fun hcc => absurd hc hcc⟩
    · refine ⟨Y.left.map (k ≫ g).op z, ?_, fun _ => rfl⟩
      rcases hk with hkC | hkD
      · exact absurd hkC hc
      · rw [NatTrans.naturality_apply, hzv]
        exact ((hdiagIff A'' k).1 hkD).symm
  choose φ hφover hφelse using hforced
  -- The forced values are compatible.
  have hcompat : Presieve.FamilyOfElements.Compatible
      (P := Y.left)
      (R := ((C ⊔ Subfunctor.range (pullback.diagonal f)).sieveOfSection s).arrows)
      (fun A'' k hk => φ A'' k hk) := by
    intro A₁ A₂ Z g₁ g₂ k₁ k₂ hk₁ hk₂ hcomm
    change Y.left.map g₁.op (φ A₁ k₁ hk₁) = Y.left.map g₂.op (φ A₂ k₂ hk₂)
    by_cases hc : (pullback f f).map (g₁ ≫ k₁).op s ∈ C.obj (op Z)
    · refine hsepC Z (g₁ ≫ k₁) hc _ _ ?_ ?_
      · rw [NatTrans.naturality_apply, hφover A₁ k₁ hk₁, ← Functor.map_comp_apply, ← op_comp]
      · rw [NatTrans.naturality_apply, hφover A₂ k₂ hk₂, ← Functor.map_comp_apply, ← op_comp,
          hcomm]
    · have hc₁ : (pullback f f).map k₁.op s ∉ C.obj (op A₁) := fun hmem => hc (by
        rw [op_comp, Functor.map_comp_apply]
        exact C.map g₁.op hmem)
      have hc₂ : (pullback f f).map k₂.op s ∉ C.obj (op A₂) := fun hmem => hc (by
        rw [hcomm, op_comp, Functor.map_comp_apply]
        exact C.map g₂.op hmem)
      rw [hφelse A₁ k₁ hk₁ hc₁, hφelse A₂ k₂ hk₂ hc₂, ← Functor.map_comp_apply,
        ← Functor.map_comp_apply, ← op_comp, ← op_comp, ← Category.assoc, ← Category.assoc,
        hcomm]
  -- Amalgamate them.
  obtain ⟨t, ht⟩ : ∃ t : Y.left.obj (op A'), ∀ (A'' : BigFppfOver B S hS) (k : A'' ⟶ A')
      (hk : ((C ⊔ Subfunctor.range (pullback.diagonal f)).sieveOfSection s).arrows k),
      Y.left.map k.op t = φ A'' k hk := by
    refine ⟨(((isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) Y.left).1 hYsheaf
      ((C ⊔ Subfunctor.range (pullback.diagonal f)).sieveOfSection s) hRmem).amalgamate
      _ hcompat), fun A'' k hk => ?_⟩
    exact ((isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) Y.left).1 hYsheaf
      ((C ⊔ Subfunctor.range (pullback.diagonal f)).sieveOfSection s) hRmem).valid_glue
      hcompat k hk
  -- The amalgamation lies over `u`, which is checked locally in the sheaf `V`.
  have hto : Y.hom.app (op A') t = u := by
    refine eq_of_locally_eq B S hS hVsheaf
      ((C ⊔ Subfunctor.range (pullback.diagonal f)).sieveOfSection s) hRmem ?_
    intro A'' k hk
    rw [← NatTrans.naturality_apply, ht A'' k hk, hφover A'' k hk]
  -- And it satisfies the diagonal prescription.
  have htd : ∀ (A'' : BigFppfOver B S hS) (k : A'' ⟶ A'),
      V.map k.op u = V.map (k ≫ g).op v →
      Y.left.map k.op t = Y.left.map (k ≫ g).op z := by
    intro A'' k hk
    have hkR : ((C ⊔ Subfunctor.range (pullback.diagonal f)).sieveOfSection s).arrows k :=
      Or.inr ((hdiagIff A'' k).2 hk)
    rw [ht A'' k hkR]
    by_cases hc : (pullback f f).map k.op s ∈ C.obj (op A'')
    · refine hsepC A'' k hc _ _ (hφover A'' k hkR) ?_
      rw [NatTrans.naturality_apply, hzv]
      exact hk.symm
    · exact hφelse A'' k hkR hc
  exact ⟨t, ⟨hto, htd⟩, fun t' ht' => huniq t' t ht' ⟨hto, htd⟩⟩

/-! ### The section of the dependent product witnessing a section of `Y` -/

/-- **Every section of `Y` is the value at the identity of a section of the dependent
product.** Given a section `z` of `Y` over `A`, lying over `v` in `V` with image `w` in `W`,
the family of values forced by `AlgebraicGeometry.Space.existsUnique_depProdValue` is a section
of the dependent product of `Y` along `f` over `w`, and its value at the identity and at `v` is
`z`.

Both the fact that the values lie over `V` and their compatibility with restriction come from
the characterisation: the first is one of the two characterising properties, and the second
holds because the restriction of the value at an index also has those two properties for the
restricted index, so uniqueness identifies it with the value there. -/
theorem exists_depProdSection_of_section (f : V ⟶ W) (T : Subfunctor W) (Y : Over V)
    (hY : IsIso (((openComplement B S hS T).preimage f).fromPreimage Y.hom))
    (hVsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) V)
    (hYsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y.left)
    (C : Subfunctor (pullback f f))
    (hC : C ≤ (openComplement B S hS T).preimage (pullback.fst f f ≫ f))
    (hcov : (C ⊔ Subfunctor.range (pullback.diagonal f)).sheafify
      (BigFppfOver.topology B S hS) = ⊤)
    {A : BigFppfOver B S hS} (z : Y.left.obj (op A)) (v : V.obj (op A))
    (hzv : Y.hom.app (op A) z = v) (w : W.obj (op A)) (hvw : f.app (op A) v = w) :
    ∃ y : DepProdSection f Y A w,
      ∀ hid : f.app (op A) v = W.map (𝟙 A).op w, y.app (𝟙 A) v hid = z := by
  classical
  have hval : ∀ {A' : BigFppfOver B S hS} (g : A' ⟶ A) (u : V.obj (op A'))
      (_ : f.app (op A') u = W.map g.op w),
      ∃! t : Y.left.obj (op A'),
        Y.hom.app (op A') t = u ∧
        ∀ (A'' : BigFppfOver B S hS) (k : A'' ⟶ A'),
          V.map k.op u = V.map (k ≫ g).op v →
          Y.left.map k.op t = Y.left.map (k ≫ g).op z := fun g u hu =>
    existsUnique_depProdValue B S hS f T Y hY hVsheaf hYsheaf C hC hcov z v hzv g u
      (by rwa [NatTrans.naturality_apply, hvw])
  refine ⟨DepProdSection.mk' (fun g u hu => (hval g u hu).choose) (fun g u hu => ?_)
    (fun k g u hu => ?_), fun hid => ?_⟩
  · exact (hval g u hu).choose_spec.1.1
  · -- Compatibility with restriction, from uniqueness at the restricted index.
    refine (hval (k ≫ g) (V.map k.op u) (map_compat f k g hu)).choose_spec.2 _ ⟨?_, ?_⟩
    · rw [NatTrans.naturality_apply, (hval g u hu).choose_spec.1.1]
    · intro A₃ m hm
      have hm' : V.map (m ≫ k).op u = V.map ((m ≫ k) ≫ g).op v := by
        rw [op_comp, Functor.map_comp_apply, hm, Category.assoc]
      refine Eq.trans ?_ (Eq.trans ((hval g u hu).choose_spec.1.2 A₃ (m ≫ k) hm') ?_)
      · rw [← Functor.map_comp_apply, ← op_comp]
      · rw [← Category.assoc]
  · -- The value at the identity is `z` itself, again by uniqueness.
    rw [DepProdSection.mk'_app]
    refine ((hval (𝟙 A) v hid).choose_spec.2 z ⟨hzv, fun A'' k _ => ?_⟩).symm
    rw [Category.comp_id]

/-! ### Surjectivity, and the isomorphism -/

/-- **The counit of the dependent product is surjective on sections**, given the decomposition
`V ×_W V = Δ(V) ⨿ U` of Stacks 0BGY in the form of a subfunctor `C` playing the role of `U`. -/
theorem surjective_depProdCounitApp_of_diagonalComplement (f : V ⟶ W) (T : Subfunctor W)
    (Y : Over V)
    (hY : IsIso (((openComplement B S hS T).preimage f).fromPreimage Y.hom))
    (hVsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) V)
    (hYsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y.left)
    (C : Subfunctor (pullback f f))
    (hC : C ≤ (openComplement B S hS T).preimage (pullback.fst f f ≫ f))
    (hcov : (C ⊔ Subfunctor.range (pullback.diagonal f)).sheafify
      (BigFppfOver.topology B S hS) = ⊤)
    (A : (BigFppfOver B S hS)ᵒᵖ) :
    Function.Surjective ((depProdCounitApp f Y).left.app A) := by
  classical
  intro z
  have hXsq : IsPullback ((pullback.fst (depProdπ f Y) f).app A)
      ((pullback.snd (depProdπ f Y) f).app A) ((depProdπ f Y).app A) (f.app A) :=
    (IsPullback.of_hasPullback (depProdπ f Y) f).map ((evaluation _ (Type u)).obj A)
  obtain ⟨y, hy⟩ := exists_depProdSection_of_section B S hS f T Y hY hVsheaf hYsheaf C hC hcov
    (A := A.unop) z (Y.hom.app A z) rfl (f.app A (Y.hom.app A z)) rfl
  obtain ⟨e, he₁, he₂⟩ := Types.exists_of_isPullback hXsq
    (⟨f.app A (Y.hom.app A z), y⟩ : (depProdObj f Y).obj A) (Y.hom.app A z) rfl
  have hid : f.app (op A.unop) (Y.hom.app A z)
      = W.map (𝟙 A.unop).op (f.app A (Y.hom.app A z)) := by simp
  refine ⟨e, ?_⟩
  rw [depProdCounitApp_left_app]
  exact (depProdSection_app_congr f he₁ rfl he₂ (counit_compat f Y e) hid).trans (hy hid)

/-- **The counit of the dependent product is surjective on sections.** -/
theorem surjective_depProdCounitApp (hV : IsAlgebraicSpace B S hS V)
    (hW : IsAlgebraicSpace B S hS W) (f : V ⟶ W) (hf : IsEtale B S hS f)
    (hsep : IsSeparated B S hS f) (T : Subfunctor W) (hfT : IsIso (T.fromPreimage f))
    (Y : Over V)
    (hY : IsIso (((openComplement B S hS T).preimage f).fromPreimage Y.hom))
    (hYsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y.left)
    (A : (BigFppfOver B S hS)ᵒᵖ) :
    Function.Surjective ((depProdCounitApp f Y).left.app A) := by
  obtain ⟨C, hcov, hC, -⟩ := exists_subfunctor_sheafify_sup_range_diagonal_eq_top B S hS hV hW f
    hf hsep T hfT
  rw [sup_comm] at hcov
  exact surjective_depProdCounitApp_of_diagonalComplement B S hS f T Y hY hV.isSheaf hYsheaf
    C hC hcov A

/-- **The computation `X ×_{g,W,f} V = Y` of Stacks 0BGY**, given the decomposition
`V ×_W V = Δ(V) ⨿ U` of the source proof: the counit of the dependent product is an
isomorphism of presheaves. -/
theorem isIso_depProdCounitApp_left_of_diagonalComplement (f : V ⟶ W) (T : Subfunctor W)
    (Y : Over V)
    (hY : IsIso (((openComplement B S hS T).preimage f).fromPreimage Y.hom))
    (hVsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) V)
    (hYsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y.left)
    (C : Subfunctor (pullback f f))
    (hC : C ≤ (openComplement B S hS T).preimage (pullback.fst f f ≫ f))
    (hcov : (C ⊔ Subfunctor.range (pullback.diagonal f)).sheafify
      (BigFppfOver.topology B S hS) = ⊤) :
    IsIso ((depProdCounitApp f Y).left) := by
  have (A : (BigFppfOver B S hS)ᵒᵖ) : IsIso ((depProdCounitApp f Y).left.app A) :=
    (isIso_iff_bijective _).2
      ⟨injective_depProdCounitApp_of_diagonalComplement B S hS f T Y hY hYsheaf C hC hcov A,
        surjective_depProdCounitApp_of_diagonalComplement B S hS f T Y hY hVsheaf hYsheaf C hC
          hcov A⟩
  exact NatIso.isIso_of_isIso_app _

/-- **The computation `X ×_{g,W,f} V = Y` of Stacks 0BGY**: for a separated étale morphism
`f : V ⟶ W` of algebraic spaces over `S`, a subfunctor `T` of `W` over which `f` is an
isomorphism, and an fppf sheaf `Y ⟶ V` which is an isomorphism over `f⁻¹W⁰`, the counit
`(Π_f Y) ×_{g,W,f} V ⟶ Y` is an isomorphism of presheaves. -/
theorem isIso_depProdCounitApp_left (hV : IsAlgebraicSpace B S hS V)
    (hW : IsAlgebraicSpace B S hS W) (f : V ⟶ W) (hf : IsEtale B S hS f)
    (hsep : IsSeparated B S hS f) (T : Subfunctor W) (hfT : IsIso (T.fromPreimage f))
    (Y : Over V)
    (hY : IsIso (((openComplement B S hS T).preimage f).fromPreimage Y.hom))
    (hYsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y.left) :
    IsIso ((depProdCounitApp f Y).left) := by
  obtain ⟨C, hcov, hC, -⟩ := exists_subfunctor_sheafify_sup_range_diagonal_eq_top B S hS hV hW f
    hf hsep T hfT
  rw [sup_comm] at hcov
  exact isIso_depProdCounitApp_left_of_diagonalComplement B S hS f T Y hY hV.isSheaf hYsheaf
    C hC hcov

/-- **The computation `X ×_{g,W,f} V = Y` of Stacks 0BGY**, as an isomorphism in
`CategoryTheory.Over V`: the base change of the dependent product of `Y` along `f` is `Y`. -/
theorem isIso_depProdCounitApp (hV : IsAlgebraicSpace B S hS V)
    (hW : IsAlgebraicSpace B S hS W) (f : V ⟶ W) (hf : IsEtale B S hS f)
    (hsep : IsSeparated B S hS f) (T : Subfunctor W) (hfT : IsIso (T.fromPreimage f))
    (Y : Over V)
    (hY : IsIso (((openComplement B S hS T).preimage f).fromPreimage Y.hom))
    (hYsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y.left) :
    IsIso (depProdCounitApp f Y) := by
  have : IsIso ((Over.forget V).map (depProdCounitApp f Y)) :=
    isIso_depProdCounitApp_left B S hS hV hW f hf hsep T hfT Y hY hYsheaf
  exact isIso_of_reflects_iso _ (Over.forget V)

end AlgebraicGeometry.Space

end
