module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitQcqsComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitCohomologyRestriction
public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.Basic

/-!
# Stacks 09YQ for quasi-compact and quasi-separated levels: the induction

For a directed inverse system `(X_i)` of schemes with affine transition morphisms, a least index
`⊥` and limit `X`, this file proves that for every abelian sheaf `G` on `X_⊥` the comparison of
`colim_i H^m(X_i, f_i⁻¹G)` with `H^m(X, f⁻¹G)` is an isomorphism (every class on `X` comes from a
stage, and a class at a stage vanishing on `X` vanishes at a later stage) as soon as `X_⊥` is
quasi-compact and quasi-separated. The proof runs the induction principle of Stacks 08DR over the
opens of `X_⊥`: the affine case is `Stacks.EtaleCohomology.LimitSiteBridge`, and the step uses the
Mayer–Vietoris short exact sequence of extensions by zero, the five lemma, and the transfer of the
comparison to an open (`good_of_restrict`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.LimitExt

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

section MayerVietoris

variable {J : Type u} [Preorder J] [OrderBot J] [IsDirected J (· ≤ ·)]

/-- The comparison is an isomorphism for every sheaf, on `Ext` out of `ℤ`. -/
abbrev GoodZ (E : Jᵒᵖ ⥤ Scheme.{u}) (c : Cone E) : Prop :=
  ∀ G : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1},
    Good E c (zSheaf (E.obj (op ⊥))) G

variable {E : Jᵒᵖ ⥤ Scheme.{u}} {c : Cone E}

/-- `ℤ` on the least stage of the restricted system is the pull back of `ℤ|_W`. -/
def zSheafRestrictIso {W : Scheme.{u}} (ι : W ⟶ E.obj (op ⊥)) [Etale ι] :
    zSheaf ((restrictSystem E ι).obj (op ⊥)) ≅
      (etaleAbelianInverseImage.{u, 0} (rsnd E ι ⊥)).obj
        ((etaleRestriction.{u, 0} ι).obj (zSheaf (E.obj (op ⊥)))) :=
  ((etaleAbelianInverseImageConstantIso.{u, 0} (rsnd E ι ⊥ ≫ ι)).app
      (AddCommGrpCat.of (ULift ℤ))).symm ≪≫
    (K (rsnd E ι ⊥) ι (rsnd E ι ⊥ ≫ ι) rfl).app (zSheaf (E.obj (op ⊥))) ≪≫
    (etaleAbelianInverseImage.{u, 0} (rsnd E ι ⊥)).mapIso
      ((etaleAbelianInverseImageRestrictionIso.{u, 0} ι).app (zSheaf (E.obj (op ⊥))))

omit [IsDirected J (· ≤ ·)] in
/-- **The comparison for an extension by zero from an open.** -/
theorem good_extensionByZero {W : Scheme.{u}} (ι : W ⟶ E.obj (op ⊥)) [IsOpenImmersion ι]
    (hW : GoodZ (restrictSystem E ι) (restrictCone E ι c))
    (G : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Good E c ((extensionByZeroOfRestriction.{u, 0} ι).obj (zSheaf (E.obj (op ⊥)))) G := by
  let A := (etaleRestriction.{u, 0} ι).obj (zSheaf (E.obj (op ⊥)))
  refine good_of_restrict ι ((extAdj ι).unit.app A) ?_ ?_
  · rw [Adjunction.homEquiv_counit]
    change IsIso ((extensionByZero.{u, 0} ι).map ((extAdj ι).unit.app A) ≫
      (extAdj ι).counit.app ((extensionByZero.{u, 0} ι).obj A))
    rw [(extAdj ι).left_triangle_components A]
    exact IsIso.id _
  · exact good_of_iso (zSheafRestrictIso ι) (hW _)

/-- **The Mayer–Vietoris step.** -/
theorem goodZ_of_cover (U V : (E.obj (op ⊥)).Opens) (hUV : U ⊔ V = ⊤)
    (hU : GoodZ (restrictSystem E U.ι) (restrictCone E U.ι c))
    (hV : GoodZ (restrictSystem E V.ι) (restrictCone E V.ι c))
    (hUV' : GoodZ (restrictSystem E (U ⊓ V).ι) (restrictCone E (U ⊓ V).ι c)) :
    GoodZ E c := fun G =>
  good_of_shortExact (shortExact_coverShortComplex.{u, 0} U V hUV (zSheaf (E.obj (op ⊥)))) G
    (good_extensionByZero _ hUV' G)
    (good_biprod (good_extensionByZero _ hU G) (good_extensionByZero _ hV G))

end MayerVietoris

section Affine

variable {J : Type u} [Preorder J] [OrderBot J] [IsDirected J (· ≤ ·)]
  {E : Jᵒᵖ ⥤ Scheme.{u}} {c : Cone E}

/-- For `y' = f ≫ y`, a class `x` of `Ext^n(y⁻¹ℤ, y⁻¹G)` restricts to zero along `f` if and only
if the restriction along `f` of its cohomology class `toH y G n x` vanishes. -/
theorem toH_resK_eq_zero_iff {S X Y : Scheme.{u}} (f : Y ⟶ X) (y : X ⟶ S) (y' : Y ⟶ S)
    (h : y' = f ≫ y) (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) (x) :
    resK f y y' h (zSheaf S) G n x = 0 ↔
      etaleCohomologyRestrictionMap.{u, 0, u + 1} f _ n (toH y G n x) = 0 := by
  rw [← (toH_bijective y' G n).1.eq_iff, map_zero, toH_resK]
  exact Stacks.ExtTransport.comp_mk₀_eq_zero_iff (Iso.app (K f y y' h) G).symm _

/-- **The affine case.** -/
theorem goodZ_of_isAffine [IsAffine (E.obj (op ⊥))]
    [∀ {i j : Jᵒᵖ} (a : i ⟶ j), IsAffineHom (E.map a)] (hc : IsLimit c) : GoodZ E c := by
  have : ∀ i, IsAffine (E.obj i) := fun ⟨i⟩ => isAffine_of_isAffineHom (toBot E i)
  have : Nonempty J := ⟨⊥⟩
  intro G m
  refine ⟨fun y => ?_, fun i x hx => ?_⟩
  · obtain ⟨i, h, z, hz⟩ := LimitSiteBridge.exists_le_restriction_eq E c hc ⊥ G m
      (toH (c.π.app (op ⊥)) G m y)
    obtain ⟨w, hw⟩ := (toH_bijective (toBot E i) G m).2 z
    refine ⟨i, w, (toH_bijective (c.π.app (op ⊥)) G m).1 ?_⟩
    change toH (c.π.app (op ⊥)) G m (resK (c.π.app (op i)) (toBot E i) (c.π.app (op ⊥))
      (cone_toBot E c i) (zSheaf _) G m w) = _
    rwa [toH_resK, hw]
  · have hx' := (toH_resK_eq_zero_iff (c.π.app (op i)) (toBot E i) (c.π.app (op ⊥))
      (cone_toBot E c i) G m x).1 hx
    obtain ⟨i', h, hi'⟩ := LimitSiteBridge.exists_le_restriction_eq_zero E c hc i _ m _ hx'
    exact ⟨i', h, (toH_resK_eq_zero_iff (trans E h) (toBot E i) (toBot E i') (toBot_eq E h) G m
      x).2 hi'⟩

end Affine

section Induction

/-- The map `toBot E ⊥` from the least stage of a system to itself is an isomorphism. -/
theorem isIso_toBot_bot {J : Type u} [Preorder J] [OrderBot J] (E : Jᵒᵖ ⥤ Scheme.{u}) :
    IsIso (toBot E (⊥ : J)) := by
  have h : ((homOfLE bot_le).op : op (⊥ : J) ⟶ op ⊥) = 𝟙 _ := Subsingleton.elim _ _
  change IsIso (E.map ((homOfLE bot_le).op : op (⊥ : J) ⟶ op ⊥))
  rw [h, E.map_id]
  infer_instance

/-- The range of the composite of an open immersion `ψ : X_⊥ ⟶ X₀` with the least stage of the
system restricted to `ψ⁻¹U` is `U`, for `U ≤ range ψ`. -/
theorem opensRange_restrict {J : Type u} [Preorder J] [OrderBot J] [IsDirected J (· ≤ ·)]
    {E : Jᵒᵖ ⥤ Scheme.{u}} {X₀ : Scheme.{u}} (ψ : E.obj (op ⊥) ⟶ X₀) [IsOpenImmersion ψ]
    (U : X₀.Opens) (hU : U ≤ ψ.opensRange) :
    haveI := isIso_toBot_bot E
    (rsnd E (ψ ⁻¹ᵁ U).ι ⊥ ≫ (ψ ⁻¹ᵁ U).ι ≫ ψ).opensRange = U := by
  have := isIso_toBot_bot E
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
    Scheme.Hom.image_preimage_eq_opensRange_inf]
  exact inf_eq_right.2 hU

/-- **Stacks 09YQ, quasi-compact and quasi-separated least stage, on `Ext` out of `ℤ`.** -/
theorem goodZ_of_qcqs {J : Type u} [Preorder J] [OrderBot J] [IsDirected J (· ≤ ·)]
    {E : Jᵒᵖ ⥤ Scheme.{u}} {c : Cone E} (hc : IsLimit c)
    [∀ {i j : Jᵒᵖ} (a : i ⟶ j), IsAffineHom (E.map a)] [CompactSpace (E.obj (op ⊥))]
    [QuasiSeparatedSpace (E.obj (op ⊥))] : GoodZ E c := by
  let X₀ := E.obj (op ⊥)
  let P : X₀.Opens → Prop := fun W => ∀ (J' : Type u) [Preorder J'] [OrderBot J']
    [IsDirected J' (· ≤ ·)] (E' : J'ᵒᵖ ⥤ Scheme.{u}) (c' : Cone E'), IsLimit c' →
    (∀ {i j : J'ᵒᵖ} (a : i ⟶ j), IsAffineHom (E'.map a)) →
    ∀ (ψ : E'.obj (op ⊥) ⟶ X₀) [IsOpenImmersion ψ], ψ.opensRange = W → GoodZ E' c'
  have haff : ∀ W : X₀.Opens, IsAffineOpen W → P W := by
    intro W hW J' _ _ _ E' c' hc' _ ψ _ hψ
    have : IsAffine (ψ.opensRange : Scheme.{u}) := by rwa [hψ]
    have : IsAffine (E'.obj (op ⊥)) := IsAffine.of_isIso ψ.isoOpensRange.hom
    exact goodZ_of_isAffine hc'
  have hsup : ∀ U V : X₀.Opens, IsCompact (U : Set X₀) → IsAffineOpen V → P U → P V →
      P (U ⊓ V) → P (U ⊔ V) := by
    intro U V _ _ hU hV hUV J' _ _ _ E' c' hc' _ ψ _ hψ
    have := isIso_toBot_bot E'
    have key : ∀ O : X₀.Opens, O ≤ U ⊔ V → P O →
        GoodZ (restrictSystem E' (ψ ⁻¹ᵁ O).ι) (restrictCone E' (ψ ⁻¹ᵁ O).ι c') :=
      fun O hO hP => hP J' _ _ (isLimitRestrictCone E' c' _ hc') (fun a => inferInstance)
        (rsnd E' (ψ ⁻¹ᵁ O).ι ⊥ ≫ (ψ ⁻¹ᵁ O).ι ≫ ψ) (opensRange_restrict ψ O (hψ ▸ hO))
    refine goodZ_of_cover (ψ ⁻¹ᵁ U) (ψ ⁻¹ᵁ V) ?_ (key U le_sup_left hU) (key V le_sup_right hV) ?_
    · rw [← Scheme.Hom.preimage_sup, ← hψ, Scheme.Hom.preimage_opensRange]
    · rw [← Scheme.Hom.preimage_inf]
      exact key _ (inf_le_left.trans le_sup_left) hUV
  exact Stacks.AlgebraicGeometry.InductionPrinciple.induction_top P haff hsup J E c hc
    (fun a => inferInstance) (𝟙 X₀) (Scheme.Hom.opensRange_of_isIso _)

end Induction

end Stacks.EtaleCohomology.LimitExt
