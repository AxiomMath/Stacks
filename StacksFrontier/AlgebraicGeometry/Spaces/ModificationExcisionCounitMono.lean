module

public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedEtaleDiagonalComplementRange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationExcisionRigid
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphism

/-!
# The counit of the dependent product is injective on sections

Stacks 0BGY produces the inverse of the base-change functor as the dependent product
`X = Π_f Y`, and the second computation it makes with it is that `X ×_{g,W,f} V → Y` is an
isomorphism. This file proves that this comparison — the counit of the dependent product — is
injective on sections.

## Main results

* `AlgebraicGeometry.Space.depProdSection_app_of_restrict`: the value of a section of the
  dependent product at a diagonal index is the restriction of its value at the identity.
* `AlgebraicGeometry.Space.injective_depProdCounitApp_of_diagonalComplement`: the counit is
  injective on sections, given the decomposition `V ×_W V = Δ(V) ⨿ U` of the source proof.
* `AlgebraicGeometry.Space.injective_depProdCounitApp`: the same with that decomposition
  discharged, so under the tag's own hypotheses on `f`.

## Implementation notes

A section of `X ×_W V` over `A` is a pair `((w, y), v)` with `f v = w`, and the counit sends
it to `y.app (𝟙 A) v`. Two such sections with the same image therefore have the same `v`,
since `y.app (𝟙 A) v` lies over `v`, and hence the same `w`; what has to be shown is that the
two families `y` agree.

That is where the decomposition `V ×_W V = Δ(V) ⨿ U` enters. A value `y.app h v'` is indexed
by a second section `v'` of `V` over the same section of `W`; the pair `(v|_h, v')` is a section
of `V ×_W V`, which locally lies either in the range of the diagonal, where `v' = v|_h` and both
families are forced to `Y.left.map h (y.app (𝟙 A) v)` by their own naturality, or in the
complementary piece, where the base section lies in `W⁰` and the two values are separated by
`AlgebraicGeometry.Space.eq_of_app_eq_of_mem`. Since `Y.left` is a sheaf, local agreement is
agreement.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Presheaf Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The value of a section of the dependent product at a *diagonal* index — one of the form
`(g, v|_g)` for a section `v` over the whole of `A` — is the restriction along `g` of its
value at the identity. -/
theorem depProdSection_app_of_restrict (f : V ⟶ W) (Y : Over V)
    {A : (BigFppfOver B S hS)ᵒᵖ} (p : DepProdSections f Y A)
    {A' : BigFppfOver B S hS} (g : A' ⟶ A.unop) (v : V.obj (op A.unop))
    (hid : f.app (op A.unop) v = W.map (𝟙 A.unop).op p.1)
    (hg : f.app (op A') (V.map g.op v) = W.map g.op p.1) :
    p.2.app g (V.map g.op v) hg = Y.left.map g.op (p.2.app (𝟙 A.unop) v hid) :=
  ((p.2.naturality g (𝟙 A.unop) v hid).trans
    (p.2.app_congr (Category.comp_id g) (V.map g.op v)
      (map_compat f g (𝟙 A.unop) hid) hg)).symm

/-- **The counit of the dependent product is injective on sections**, given the decomposition
`V ×_W V = Δ(V) ⨿ U` of Stacks 0BGY in the form of a subfunctor `C` playing the role of `U`:
`hC` says that `C` lies over the open complement of `T` (the step `U ×_W T = ∅`), and `hcov`
says that `C` and the diagonal cover the fibre square locally. -/
theorem injective_depProdCounitApp_of_diagonalComplement (f : V ⟶ W) (T : Subfunctor W)
    (Y : Over V)
    (hY : IsIso (((openComplement B S hS T).preimage f).fromPreimage Y.hom))
    (hYsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y.left)
    (C : Subfunctor (pullback f f))
    (hC : C ≤ (openComplement B S hS T).preimage (pullback.fst f f ≫ f))
    (hcov : (C ⊔ Subfunctor.range (pullback.diagonal f)).sheafify
      (BigFppfOver.topology B S hS) = ⊤)
    (A : (BigFppfOver B S hS)ᵒᵖ) :
    Function.Injective ((depProdCounitApp f Y).left.app A) := by
  classical
  have hVsq : ∀ A' : (BigFppfOver B S hS)ᵒᵖ,
      IsPullback ((pullback.fst f f).app A') ((pullback.snd f f).app A')
        (f.app A') (f.app A') := fun A' =>
    (IsPullback.of_hasPullback f f).map ((evaluation _ (Type u)).obj A')
  have hXsq : ∀ A' : (BigFppfOver B S hS)ᵒᵖ,
      IsPullback ((pullback.fst (depProdπ f Y) f).app A')
        ((pullback.snd (depProdπ f Y) f).app A')
        ((depProdπ f Y).app A') (f.app A') := fun A' =>
    (IsPullback.of_hasPullback (depProdπ f Y) f).map ((evaluation _ (Type u)).obj A')
  have hover : ∀ e : (pullback (depProdπ f Y) f).obj A,
      Y.hom.app A ((depProdCounitApp f Y).left.app A e)
        = (pullback.snd (depProdπ f Y) f).app A e := by
    intro e
    rw [depProdCounitApp_left_app]
    exact ((pullback.fst (depProdπ f Y) f).app A e).2.over _ _ _
  have hbase : ∀ e : (pullback (depProdπ f Y) f).obj A,
      ((pullback.fst (depProdπ f Y) f).app A e).1
        = f.app A ((pullback.snd (depProdπ f Y) f).app A e) := by
    intro e
    simpa only [ConcreteCategory.comp_apply, types_comp_apply, depProdπ_app] using
      ConcreteCategory.congr_hom (hXsq A).w e
  have hdata : ∀ e : (pullback (depProdπ f Y) f).obj A, ∃ (p : DepProdSections f Y A)
      (v : V.obj (op A.unop)) (hid : f.app (op A.unop) v = W.map (𝟙 A.unop).op p.1),
      (pullback.fst (depProdπ f Y) f).app A e = p ∧
        (pullback.snd (depProdπ f Y) f).app A e = v ∧ f.app (op A.unop) v = p.1 ∧
        (depProdCounitApp f Y).left.app A e = p.2.app (𝟙 A.unop) v hid := by
    intro e
    obtain ⟨p, hp⟩ : ∃ p, (pullback.fst (depProdπ f Y) f).app A e = p := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v, (pullback.snd (depProdπ f Y) f).app A e = v := ⟨_, rfl⟩
    have hfv : f.app (op A.unop) v = p.1 := by
      rw [← hv, ← hp]; exact (hbase e).symm
    have hid : f.app (op A.unop) v = W.map (𝟙 A.unop).op p.1 := by rw [hfv]; simp
    exact ⟨p, v, hid, hp, hv, hfv, (depProdCounitApp_left_app f Y e).trans
      (depProdSection_app_congr f hp rfl hv (counit_compat f Y e) hid)⟩
  intro e₁ e₂ heq
  obtain ⟨p₁, v₁, hid₁, hp₁, hv₁, hfv₁, hcu₁⟩ := hdata e₁
  obtain ⟨p₂, v₂, hid₂, hp₂, hv₂, hfv₂, hcu₂⟩ := hdata e₂
  have hvv : v₁ = v₂ := by
    rw [← hv₁, ← hv₂, ← hover e₁, ← hover e₂, heq]
  have hww : p₁.1 = p₂.1 := by rw [← hfv₁, ← hfv₂, hvv]
  have hz : p₁.2.app (𝟙 A.unop) v₁ hid₁ = p₂.2.app (𝟙 A.unop) v₂ hid₂ :=
    hcu₁.symm.trans (heq.trans hcu₂)
  have hstep : ∀ (p : DepProdSections f Y A) (v : V.obj (op A.unop))
      (hid : f.app (op A.unop) v = W.map (𝟙 A.unop).op p.1) {A' : BigFppfOver B S hS}
      (h : A' ⟶ A.unop) (v' : V.obj (op A')) (hv' : f.app (op A') v' = W.map h.op p.1)
      {A'' : BigFppfOver B S hS} (k : A'' ⟶ A')
      (hvk : V.map k.op v' = V.map (k ≫ h).op v),
      p.2.app (k ≫ h) (V.map k.op v') (map_compat f k h hv')
        = Y.left.map (k ≫ h).op (p.2.app (𝟙 A.unop) v hid) := by
    intro p v hid A' h v' hv' A'' k hvk
    have hcompat : f.app (op A'') (V.map (k ≫ h).op v) = W.map (k ≫ h).op p.1 := by
      rw [← hvk]; exact map_compat f k h hv'
    exact (depProdSection_app_congr f rfl rfl hvk (map_compat f k h hv') hcompat).trans
      (depProdSection_app_of_restrict B S hS f Y p (k ≫ h) v hid hcompat)
  have hpair : p₁ = p₂ := by
    refine depProdMk_ext f hww ?_
    intro A' h v' hv' hv''
    have hcompat : f.app (op A') (V.map h.op v₁) = f.app (op A') v' := by
      rw [NatTrans.naturality_apply, hfv₁]; exact hv'.symm
    obtain ⟨s, hs₁, hs₂⟩ := Types.exists_of_isPullback (hVsq (op A'))
      (V.map h.op v₁) v' hcompat
    have hmem : (C ⊔ Subfunctor.range (pullback.diagonal f)).sieveOfSection s
        ∈ BigFppfOver.topology B S hS A' := by
      change s ∈ ((C ⊔ Subfunctor.range (pullback.diagonal f)).sheafify
        (BigFppfOver.topology B S hS)).obj (op A')
      rw [hcov]; trivial
    refine eq_of_locally_eq B S hS hYsheaf
      ((C ⊔ Subfunctor.range (pullback.diagonal f)).sieveOfSection s) hmem ?_
    intro A'' k hk
    rw [p₁.2.naturality k h v' hv', p₂.2.naturality k h v' hv'']
    have hrfst : (pullback.fst f f).app (op A'') ((pullback f f).map k.op s)
        = V.map (k ≫ h).op v₁ := by
      rw [NatTrans.naturality_apply, hs₁, ← Functor.map_comp_apply, ← op_comp]
    have hrsnd : (pullback.snd f f).app (op A'') ((pullback f f).map k.op s)
        = V.map k.op v' := by
      rw [NatTrans.naturality_apply, hs₂]
    have hval : f.app (op A'') (V.map (k ≫ h).op v₁)
        = f.app (op A'') (V.map k.op v') := by
      have hw := ConcreteCategory.congr_hom (hVsq (op A'')).w ((pullback f f).map k.op s)
      simp only [ConcreteCategory.comp_apply] at hw
      rwa [hrfst, hrsnd] at hw
    rcases hk with hkC | hkD
    · have hmem₀ := hC _ hkC
      change (pullback.fst f f ≫ f).app (op A'')
        ((pullback f f).map k.op s) ∈ (openComplement B S hS T).obj (op A'') at hmem₀
      rw [NatTrans.comp_app, ConcreteCategory.comp_apply, hrfst] at hmem₀
      refine eq_of_app_eq_of_mem B S hS Y.hom ((openComplement B S hS T).preimage f) hY ?_ ?_
      · rw [p₁.2.over, p₂.2.over]
      · change f.app (op A'') (Y.hom.app (op A'') _)
          ∈ (openComplement B S hS T).obj (op A'')
        rwa [p₁.2.over, ← hval]
    · obtain ⟨t, ht⟩ := hkD
      have hdiag : ∀ (i : (pullback f f ⟶ V)) (hi : pullback.diagonal f ≫ i = 𝟙 V),
          i.app (op A'') ((pullback f f).map k.op s) = t := fun i hi => by
        rw [← ht]
        exact ConcreteCategory.congr_hom (NatTrans.congr_app hi (op A'')) t
      have hvk : V.map k.op v' = V.map (k ≫ h).op v₁ := by
        rw [← hrsnd, ← hrfst, hdiag _ (pullback.diagonal_snd f),
          hdiag _ (pullback.diagonal_fst f)]
      have hvk₂ : V.map k.op v' = V.map (k ≫ h).op v₂ := by rw [hvk, hvv]
      rw [hstep p₁ v₁ hid₁ h v' hv' k hvk, hstep p₂ v₂ hid₂ h v' hv'' k hvk₂, hz]
  exact Types.ext_of_isPullback (hXsq A) (hp₁.trans (hpair.trans hp₂.symm))
    (hv₁.trans (hvv.trans hv₂.symm))

/-- **The counit of the dependent product is injective on sections.** Let `f : V ⟶ W` be a
separated étale morphism of algebraic spaces over `S`, let `T` be a subfunctor of `W` over
which `f` is an isomorphism, and let `Y ⟶ V` be an fppf sheaf which is an isomorphism over
`f⁻¹W⁰`, where `W⁰` is the open complement of `T`. Then the counit
`(Π_f Y) ×_{g,W,f} V ⟶ Y` of Stacks 0BGY is injective on sections. -/
theorem injective_depProdCounitApp (hV : IsAlgebraicSpace B S hS V)
    (hW : IsAlgebraicSpace B S hS W) (f : V ⟶ W) (hf : IsEtale B S hS f)
    (hsep : IsSeparated B S hS f) (T : Subfunctor W) (hfT : IsIso (T.fromPreimage f))
    (Y : Over V)
    (hY : IsIso (((openComplement B S hS T).preimage f).fromPreimage Y.hom))
    (hYsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y.left)
    (A : (BigFppfOver B S hS)ᵒᵖ) :
    Function.Injective ((depProdCounitApp f Y).left.app A) := by
  obtain ⟨C, hcov, hC, -⟩ := exists_subfunctor_sheafify_sup_range_diagonal_eq_top B S hS hV hW f
    hf hsep T hfT
  rw [sup_comm] at hcov
  exact injective_depProdCounitApp_of_diagonalComplement B S hS f T Y hY hYsheaf C hC hcov A

end AlgebraicGeometry.Space

end
