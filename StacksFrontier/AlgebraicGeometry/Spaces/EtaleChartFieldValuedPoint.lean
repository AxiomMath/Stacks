module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldPointGaloisDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteMorphismLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration

/-!
# An affine étale chart through a field-valued point

Let `X` be an algebraic space over `S` and let `p` be a field-valued point of `X`, that is a
morphism `Spec K ⟶ X` from the spectrum of a field which is an object of the big fppf site.
Then `p` factors through an affine étale chart of `X`: there are an object `U` of the site with
affine underlying scheme, an étale morphism `U ⟶ X`, and a morphism `Spec K ⟶ U` over `S`
through which `p` factors.

No decency, quasi-compactness or quasi-separatedness hypothesis is needed.

## Main results

* `AlgebraicGeometry.Space.exists_affine_etale_chart_of_fieldValuedPoint`: a field-valued point
  of an algebraic space lifts along some affine étale chart.
* `AlgebraicGeometry.Space.hom_ext_of_surjective_flat_locallyOfFinitePresentation`: two
  morphisms from a representable presheaf to an fppf sheaf agreeing after restriction along a
  single fppf covering morphism are equal.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open scoped Cardinal

universe u

namespace AlgebraicGeometry.Space

/-- **Descent of an equality of sections along a one-element fppf covering.** Two morphisms
from a representable presheaf to an fppf sheaf which agree after restriction along a
surjective, flat and locally finitely presented morphism of the site are equal. -/
theorem hom_ext_of_surjective_flat_locallyOfFinitePresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {W V : BigFppfOver B S hS} (q : W ⟶ V)
    (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hflat : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q))
    {g₁ g₂ : yoneda.obj V ⟶ F} (h : yoneda.map q ≫ g₁ = yoneda.map q ≫ g₂) : g₁ = g₂ := by
  have hcompat : ∀ {Z : BigFppfOver B S hS} (p₁ p₂ : Z ⟶ W), p₁ ≫ q = p₂ ≫ q →
      F.map p₁.op (F.map q.op (yonedaEquiv g₁)) =
        F.map p₂.op (F.map q.op (yonedaEquiv g₁)) := by
    intro Z p₁ p₂ hp
    rw [← types_comp_apply (F.map q.op) (F.map p₁.op), ← F.map_comp, ← op_comp, hp,
      op_comp, F.map_comp, types_comp_apply]
  obtain ⟨y₀, -, huniq⟩ := existsUnique_map_eq_of_surjective_flat_locallyOfFinitePresentation
    B S hS F hF q hsurj hflat hfp (F.map q.op (yonedaEquiv g₁)) hcompat
  refine yonedaEquiv.injective ((huniq _ rfl).trans (huniq _ ?_).symm)
  exact ((yonedaEquiv_naturality g₂ q).trans (congrArg yonedaEquiv h.symm)).trans
    (yonedaEquiv_naturality g₁ q).symm

/-- **Every field-valued point of an algebraic space lifts along an affine étale chart.**
Given a field-valued point `p` of an algebraic space `Y` over `S` there are an object `U` of
the big fppf site over `S` with affine underlying scheme, an étale morphism
`ι : h_U ⟶ Y`, and a morphism `t` from the object of the site carrying `p` to `U`, such that
the morphism `h_{Spec K} ⟶ Y` presented by `p` is `h_t` followed by `ι`. -/
theorem exists_affine_etale_chart_of_fieldValuedPoint
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (p : FieldValuedPoint B S hS Y) :
    ∃ (U : BigFppfOver B S hS) (ι : yoneda.obj U ⟶ Y)
      (t : FieldValuedPoint.siteObject B S hS Y p ⟶ U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      IsEtale B S hS ι ∧
      yoneda.map t ≫ ι = fieldMorphism B S hS Y p := by
  classical
  obtain ⟨A, aA, yA, hAaff, hAet, hyA⟩ :=
    exists_affine_etale_chart_of_point B S hS Y hY (p.class B S hS Y)
  set P : BigFppfOver B S hS := FieldValuedPoint.siteObject B S hS Y p with hPdef
  set xP : yoneda.obj P ⟶ Y := fieldMorphism B S hS Y p with hxPdef
  have haRep : yoneda.relativelyRepresentable aA := hAet.rep
  set T : BigFppfOver B S hS := haRep.pullback xP with hTdef
  have hsnd : _root_.AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (haRep.snd xP)) :=
    hAet.property xP (haRep.fst xP) (haRep.snd xP) (haRep.isPullback xP)
  have hTne : Nonempty ((BigFppfOver.toScheme B S hS).obj T) := by
    obtain ⟨w, -, -⟩ := exists_points_of_isPullback B S hS (haRep.isPullback xP) yA
      ((p.tautologicalPoint B S hS Y).class B S hS (yoneda.obj P))
      (hyA.trans (pointsMap_fieldMorphism_tautologicalPoint B S hS Y p).symm)
    exact ⟨pointsToScheme B S hS T w⟩
  let : _root_.AlgebraicGeometry.Etale
    ((BigFppfOver.toScheme B S hS).map (haRep.snd xP)) := hsnd
  obtain ⟨E, instE, instAlgE, instFinE, instSepE, fE, hfE⟩ :=
    AlgebraicGeometry.Etale.exists_finiteSeparable_point p.carrier
      ((BigFppfOver.toScheme B S hS).map (haRep.snd xP)) hTne
  obtain ⟨L, instL, instAlgL, instFinL, instGalL, ⟨φ⟩⟩ :=
    exists_isGalois_of_finiteDimensional_of_isSeparable p.carrier E
  have hLcard : #L ≤ max ℵ₀ #p.carrier := by
    obtain ⟨σ, hσ, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp
      (inferInstance : Algebra.FiniteType p.carrier L)
    refine (Cardinal.mk_le_of_surjective hψ).trans (MvPolynomial.cardinalMk_le_max.trans ?_)
    have hs : #σ ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite σ).le
    simp only [max_le_iff]
    exact ⟨⟨le_max_right _ _, hs.trans (le_max_left _ _)⟩, le_max_left _ _⟩
  have hLsite : B.Contains (Spec (CommRingCat.of L)) :=
    Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      p.contained hLcard
  set algKL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of p.carrier) :=
    Spec.map (CommRingCat.ofHom (algebraMap p.carrier L)) with halgKL
  set Q : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (algKL ≫ p.toBase) : B.obj hLsite ⟶ B.obj hS) with hQdef
  have hPsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj P) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  have hQsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj Q) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of L)))
  have hQne : Nonempty ((BigFppfOver.toScheme B S hS).obj Q) :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of L)))
  let r : Q ⟶ P := Over.homMk (ObjectProperty.homMk algKL) (by
    apply ObjectProperty.hom_ext
    rfl)
  have hrmap : (BigFppfOver.toScheme B S hS).map r = algKL := rfl
  let aut : (L ≃ₐ[p.carrier] L) → (Q ⟶ Q) := fun γ =>
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom γ.toRingHom))) (by
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom γ.toRingHom) ≫ algKL ≫ p.toBase = algKL ≫ p.toBase
      rw [← Category.assoc, halgKL, specMap_algEquiv_comp_specMap_algebraMap])
  have hautmap : ∀ γ : L ≃ₐ[p.carrier] L, (BigFppfOver.toScheme B S hS).map (aut γ) =
      Spec.map (CommRingCat.ofHom γ.toRingHom) := fun _ => rfl
  have hautr : ∀ γ : L ≃ₐ[p.carrier] L, aut γ ≫ r = r := by
    intro γ
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, hautmap, hrmap, halgKL,
      specMap_algEquiv_comp_specMap_algebraMap]
  have hautcomp : ∀ γ δ : L ≃ₐ[p.carrier] L, aut γ ≫ aut δ = aut (δ.trans γ) := by
    intro γ δ
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, hautmap, hautmap, hautmap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun _ => rfl))
  have hautrefl : aut (AlgEquiv.refl : L ≃ₐ[p.carrier] L) = 𝟙 Q := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [hautmap, CategoryTheory.Functor.map_id, show CommRingCat.ofHom
        (AlgEquiv.refl : L ≃ₐ[p.carrier] L).toRingHom = 𝟙 (CommRingCat.of L) from
      CommRingCat.hom_ext (RingHom.ext fun _ => rfl), Spec.map_id]
    rfl
  have hautcancel : ∀ (γ : L ≃ₐ[p.carrier] L) {Z : BigFppfOver B S hS} (s₁ s₂ : Q ⟶ Z),
      aut γ ≫ s₁ = aut γ ≫ s₂ → s₁ = s₂ := by
    intro γ Z s₁ s₂ hs
    have hc := congrArg (fun k => aut γ.symm ≫ k) hs
    simp only [← Category.assoc, hautcomp, AlgEquiv.self_trans_symm, hautrefl,
      Category.id_comp] at hc
    exact hc
  have hφalg : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap p.carrier E)) = algKL := by
    rw [halgKL, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => φ.commutes a))
  have hTw : (BigFppfOver.toScheme B S hS).map (haRep.snd xP) ≫ p.toBase = T.hom.hom :=
    congrArg (fun k => k.hom) (Over.w (haRep.snd xP))
  let i₀ : Q ⟶ T := Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ fE)) (by
      apply ObjectProperty.hom_ext
      change (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ fE) ≫ T.hom.hom = algKL ≫ p.toBase
      calc (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ fE) ≫ T.hom.hom
          = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
              (fE ≫ (BigFppfOver.toScheme B S hS).map (haRep.snd xP)) ≫ p.toBase := by
            rw [← hTw]; simp only [Category.assoc]
        _ = algKL ≫ p.toBase := by rw [hfE, ← Category.assoc, hφalg])
  have hi₀map : (BigFppfOver.toScheme B S hS).map i₀ =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ fE := rfl
  have hi₀r : i₀ ≫ haRep.snd xP = r := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, hi₀map, hrmap, Category.assoc, hfE, hφalg]
  set orbit : Set (Q ⟶ T) := Set.range (fun γ : L ≃ₐ[p.carrier] L => aut γ ≫ i₀) with horbit
  have hsame : ∀ s ∈ orbit, s ≫ haRep.snd xP = r := by
    rintro - ⟨γ, rfl⟩
    rw [Category.assoc, hi₀r, hautr]
  obtain ⟨n, ⟨e⟩⟩ : ∃ n : ℕ, Nonempty (Fin (n + 1) ≃ orbit) := by
    have : Fintype orbit := (Set.finite_range _).fintype
    have : Nonempty orbit := ⟨⟨aut AlgEquiv.refl ≫ i₀, Set.mem_range_self _⟩⟩
    refine ⟨Fintype.card orbit - 1, ⟨?_⟩⟩
    exact (finCongr (Nat.succ_pred_eq_of_pos Fintype.card_pos)).trans
      (Fintype.equivFin orbit).symm
  set c : Fin (n + 1) → (Q ⟶ A) := fun i => (e i).1 ≫ haRep.fst' xP with hc
  have hinj : Function.Injective c := by
    intro i j hij
    refine e.injective (Subtype.ext (haRep.hom_ext' ?_ ?_))
    · exact hij
    · rw [hsame _ (e i).2, hsame _ (e j).2]
  have hover : ∀ i, yoneda.map (c i) ≫ aA = yoneda.map r ≫ xP := by
    intro i
    change yoneda.map ((e i).1 ≫ haRep.fst' xP) ≫ aA = yoneda.map r ≫ xP
    rw [Functor.map_comp, Category.assoc, haRep.map_fst', haRep.w,
      ← Category.assoc, ← Functor.map_comp, hsame _ (e i).2]
  have hequiv : ∀ γ : L ≃ₐ[p.carrier] L, ∃ τ : Equiv.Perm (Fin (n + 1)),
      ∀ i, aut γ ≫ c i = c (τ i) := by
    intro γ
    have hmem : ∀ i : Fin (n + 1), aut γ ≫ (e i).1 ∈ orbit := by
      intro i
      obtain ⟨δ, hδ⟩ := (e i).2
      refine ⟨δ.trans γ, ?_⟩
      change aut (δ.trans γ) ≫ i₀ = aut γ ≫ (e i).1
      rw [← hautcomp, Category.assoc]
      exact congrArg (fun k => aut γ ≫ k) hδ
    let σ : Fin (n + 1) → Fin (n + 1) := fun i => e.symm ⟨aut γ ≫ (e i).1, hmem i⟩
    have hσ : ∀ i, aut γ ≫ c i = c (σ i) := by
      intro i
      have hval : (e (σ i)).1 = aut γ ≫ (e i).1 :=
        congrArg Subtype.val (e.apply_symm_apply ⟨aut γ ≫ (e i).1, hmem i⟩)
      change aut γ ≫ (e i).1 ≫ haRep.fst' xP = (e (σ i)).1 ≫ haRep.fst' xP
      rw [hval, Category.assoc]
    refine ⟨Equiv.ofBijective σ (Finite.injective_iff_bijective.mp ?_), hσ⟩
    intro i j hij
    refine hinj (hautcancel γ (c i) (c j) ?_)
    rw [hσ, hσ, hij]
  obtain ⟨V, W, π, g, pr, act, hgEtale, hprg, hactπ, hactpr, hext, hlift⟩ :=
    exists_symmetricPower_etaleChart B S hS hY aA hAaff
      (isEtale_of_presheaf_inverseImage_etale B S hS aA hAet) n
  obtain ⟨l, hl⟩ := hlift Q (yoneda.map r ≫ xP) c hQsub hinj hover
  have hinv : ∀ γ : L ≃ₐ[p.carrier] L, aut γ ≫ l ≫ π = l ≫ π := by
    intro γ
    obtain ⟨τ, hτ⟩ := hequiv γ
    have hcoord : aut γ ≫ l = l ≫ act τ := by
      refine hext Q _ _ fun i => ?_
      rw [Category.assoc, hl, hτ, Category.assoc, hactpr, hl]
    rw [← Category.assoc, hcoord, Category.assoc, hactπ]
  set f : Spec (CommRingCat.of L) ⟶ (BigFppfOver.toScheme B S hS).obj V :=
    (BigFppfOver.toScheme B S hS).map (l ≫ π) with hf
  have hfw : f ≫ V.hom.hom = algKL ≫ p.toBase :=
    congrArg (fun k => k.hom) (Over.w (l ≫ π))
  set f' : Spec (CommRingCat.of L) ⟶ pullback V.hom.hom p.toBase :=
    pullback.lift f algKL hfw with hf'
  have hf'inv : ∀ γ : L ≃ₐ[p.carrier] L,
      Spec.map (CommRingCat.ofHom γ.toRingHom) ≫ f' = f' := by
    intro γ
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hf', pullback.lift_fst, hf, ← hautmap, ← Functor.map_comp, hinv]
    · rw [Category.assoc, hf', pullback.lift_snd, halgKL,
        specMap_algEquiv_comp_specMap_algebraMap]
  obtain ⟨G, hG⟩ := AlgebraicGeometry.exists_specMap_comp_eq_of_isGaloisInvariant p.carrier L
    (pullback V.hom.hom p.toBase) f' hf'inv
  have hGsnd : G ≫ pullback.snd V.hom.hom p.toBase = 𝟙 _ := by
    have hkey : algKL ≫ G ≫ pullback.snd V.hom.hom p.toBase = algKL := by
      rw [← Category.assoc, hG, hf', pullback.lift_snd]
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective (G ≫ pullback.snd V.hom.hom p.toBase)
    have hring : ψ ≫ CommRingCat.ofHom (algebraMap p.carrier L) =
        CommRingCat.ofHom (algebraMap p.carrier L) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hψ, ← halgKL]
      exact hkey
    have hid : ψ.hom = RingHom.id (CommRingCat.of p.carrier) := by
      ext a
      exact (algebraMap p.carrier L).injective
        (congrArg (fun k : CommRingCat.of p.carrier ⟶ CommRingCat.of L => k.hom a) hring)
    rw [← hψ, show ψ = 𝟙 _ from CommRingCat.hom_ext hid, Spec.map_id]
  set t₀ : Spec (CommRingCat.of p.carrier) ⟶ (BigFppfOver.toScheme B S hS).obj V :=
    G ≫ pullback.fst V.hom.hom p.toBase with ht₀
  have ht₀base : t₀ ≫ V.hom.hom = p.toBase := by
    rw [ht₀, Category.assoc, pullback.condition, ← Category.assoc, hGsnd, Category.id_comp]
  have ht₀f : algKL ≫ t₀ = f := by
    rw [ht₀, ← Category.assoc, hG, hf', pullback.lift_fst]
  obtain ⟨t₁, ht₁⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS (X := P) (Y := V) t₀ ht₀base
  have hrt₁ : r ≫ t₁ = l ≫ π := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, hrmap, ht₁, ht₀f, hf]
  have hsurjr : Surjective ((BigFppfOver.toScheme B S hS).map r) :=
    ⟨fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have : _root_.AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map r) := by
    rw [hrmap, halgKL]
    exact etale_specMap_algebraMap p.carrier L
  have ht₁g : yoneda.map t₁ ≫ g = xP := by
    refine hom_ext_of_surjective_flat_locallyOfFinitePresentation B S hS hY.isSheaf r
      hsurjr inferInstance inferInstance ?_
    rw [← Category.assoc, ← Functor.map_comp, hrt₁, Functor.map_comp, Category.assoc,
      ← hprg 0, ← Category.assoc, ← Functor.map_comp, hl, hover]
  obtain ⟨-, ⟨D, hD, rfl⟩, hmem, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj V).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (t₀ (default : Spec (CommRingCat.of p.carrier)))) isOpen_univ
  obtain ⟨U, u, huOpen, huRange, hUaff⟩ :=
    BigFppfOver.exists_affineOpen_restrict B S hS V ⟨D, hD⟩
  have hrange : Set.range ((BigFppfOver.toScheme B S hS).map t₁) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map u) := by
    rw [huRange]
    rintro - ⟨z, rfl⟩
    rw [ht₁, show z = (default : Spec (CommRingCat.of p.carrier)) from Subsingleton.elim _ _]
    exact hmem
  obtain ⟨t, ht⟩ := exists_comp_eq_of_isOpenImmersion_of_range_subset B S hS u t₁ huOpen hrange
  have : _root_.AlgebraicGeometry.IsOpenImmersion
    ((BigFppfOver.toScheme B S hS).map u) := huOpen
  refine ⟨U, yoneda.map u ≫ g, t, hUaff, isEtale_comp B S hS ?_ hgEtale, ?_⟩
  · exact isEtale_of_presheaf_inverseImage_etale B S hS (yoneda.map u)
      (presheaf_inverseImage_yoneda_map B S hS
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) u inferInstance)
  · rw [← Category.assoc, ← Functor.map_comp, ht, ht₁g]

end AlgebraicGeometry.Space

end
