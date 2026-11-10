module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj.Charts
import all StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj.Charts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lifted étale presentations and essential surjectivity at a surjective closed immersion

Part of `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj`. Unique descent
along a surjective étale chart, the lifted-presentation datum `LiftedEtalePresentation` and its
quotient, the existence of a lifted étale presentation from the charts, and essential surjectivity
and the equivalence of spaces-étale sites along a surjective closed immersion and along the
inclusion of a first-order thickening.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site is deep
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_LiftedEtalePresentation :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_LiftedEtalePresentation
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Unique descent along a surjective étale chart -/

/-- A surjective étale chart `q` of an algebraic space whose kernel pair is representable is an
epimorphism onto sheaves: every morphism out of the chart into a sheaf which identifies the two
projections of the kernel pair factors uniquely through `q`. -/
private theorem existsUnique_desc_of_surjectiveEtale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A E : BigFppfOver B S hS}
    (q : yoneda.obj A ⟶ F) (p₁ p₂ : E ⟶ A)
    (hq : IsPullback (yoneda.map p₁) (yoneda.map p₂) q q)
    (hF : IsAlgebraicSpace B S hS F)
    (hqSurj : (SurjSite B S hS).presheaf q)
    (hqEtale : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf q)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (g : yoneda.obj A ⟶ G) (hg : yoneda.map p₁ ≫ g = yoneda.map p₂ ≫ g) :
    ∃! e : F ⟶ G, q ≫ e = g := by
  obtain ⟨hEsh, hAsh, ⟨hcol⟩⟩ :=
    isCoequalizer_of_surjectiveEtale B S hS q p₁ p₂ hq hF hqSurj hqEtale
  let AF : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨yoneda.obj A, hAsh⟩
  let EF : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨yoneda.obj E, hEsh⟩
  let FF : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨F, hF.isSheaf⟩
  let GF : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨G, hG⟩
  let sp₁ : EF ⟶ AF := ⟨yoneda.map p₁⟩
  let sp₂ : EF ⟶ AF := ⟨yoneda.map p₂⟩
  let sg : AF ⟶ GF := ⟨g⟩
  have hg' : sp₁ ≫ sg = sp₂ ≫ sg := Sheaf.hom_ext hg
  have hpd := Cofork.IsColimit.π_desc hcol (t := Cofork.ofπ sg hg')
  have hdesc : q ≫ (hcol.desc (Cofork.ofπ sg hg')).hom = g :=
    congrArg (fun k : AF ⟶ GF ↦ k.hom) hpd
  refine ⟨(hcol.desc (Cofork.ofπ sg hg')).hom, hdesc, fun e he ↦ ?_⟩
  have hsh : (⟨e⟩ : FF ⟶ GF) = hcol.desc (Cofork.ofπ sg hg') :=
    Cofork.IsColimit.hom_ext hcol (Sheaf.hom_ext (he.trans hdesc.symm))
  exact congrArg (fun k : FF ⟶ GF ↦ k.hom) hsh

/-- A surjective étale chart `q` of an algebraic space whose kernel pair is representable is an
epimorphism onto sheaves: two morphisms out of the target which agree after precomposing with `q`
are equal. -/
private theorem hom_ext_of_surjectiveEtale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A E : BigFppfOver B S hS}
    (q : yoneda.obj A ⟶ F) (p₁ p₂ : E ⟶ A)
    (hq : IsPullback (yoneda.map p₁) (yoneda.map p₂) q q)
    (hF : IsAlgebraicSpace B S hS F)
    (hqSurj : (SurjSite B S hS).presheaf q)
    (hqEtale : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf q)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (e₁ e₂ : F ⟶ G) (h : q ≫ e₁ = q ≫ e₂) : e₁ = e₂ := by
  obtain ⟨_, -, hu⟩ := existsUnique_desc_of_surjectiveEtale B S hS q p₁ p₂ hq hF hqSurj hqEtale
    hG (q ≫ e₁) (by rw [← Category.assoc, ← Category.assoc, hq.w])
  exact (hu e₁ rfl).trans (hu e₂ h.symm).symm

/-! ### Lifted étale presentations -/

/-- A *lifted étale presentation* of an object `C` of the spaces-étale site of `X` across a
morphism `f : X ⟶ Y`: an étale equivalence relation `(k₁, k₂)` on a site object `V` étale over
`Y`, together with an identification of its base change along `f` with a surjective étale chart
`c` of `C` and with the kernel pair of `c`. -/
structure LiftedEtalePresentation {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (C : SpacesEtale B S hS X) where
  /-- A site object étale over `Y`, the chart downstairs. -/
  V : BigFppfOver B S hS
  /-- A site object étale over `Y`, the relation downstairs. -/
  W : BigFppfOver B S hS
  /-- The base change of `V` along `f`, which charts `C`. -/
  U : BigFppfOver B S hS
  /-- The base change of `W` along `f`, which is the kernel pair of that chart. -/
  R : BigFppfOver B S hS
  /-- The structure morphism of `V` over `Y`. -/
  v : yoneda.obj V ⟶ Y.1
  /-- The structure morphism of `W` over `Y`. -/
  w : yoneda.obj W ⟶ Y.1
  /-- `V` is étale over `Y`. -/
  isEtale_v : IsEtale B S hS v
  /-- `W` is étale over `Y`. -/
  isEtale_w : IsEtale B S hS w
  /-- The two maps of the relation. -/
  k₁ : W ⟶ V
  /-- The two maps of the relation. -/
  k₂ : W ⟶ V
  /-- The first map lies over `Y`. -/
  comp_k₁ : yoneda.map k₁ ≫ v = w
  /-- The second map lies over `Y`. -/
  comp_k₂ : yoneda.map k₂ ≫ v = w
  /-- The relation is an étale equivalence relation. -/
  isEtaleEquivalenceRelation : Stacks.Groupoids.IsEtaleEquivalenceRelation (relation B S hS k₁ k₂)
  /-- The chart of `C`. -/
  c : yoneda.obj U ⟶ C.1.left.1
  /-- The chart is étale. -/
  isEtale_c : IsEtale B S hS c
  /-- The chart is surjective. -/
  surjective_c : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) c
  /-- The projection of the base change of `V`. -/
  a : U ⟶ V
  /-- The projection of the base change of `W`. -/
  b : R ⟶ W
  /-- The first projection of the kernel pair of the chart. -/
  s : R ⟶ U
  /-- The second projection of the kernel pair of the chart. -/
  t : R ⟶ U
  /-- `U` is the base change of `V` along `f`. -/
  isPullback_a : IsPullback (yoneda.map a) (c ≫ C.1.hom.hom) v f.hom
  /-- `R` is the base change of `W` along `f`, as a space over `U`. -/
  isPullback_b : IsPullback (yoneda.map b) (yoneda.map t) (yoneda.map k₁) (yoneda.map a)
  /-- The second projection is compatible with the second map of the relation. -/
  comp_b_k₂ : b ≫ k₂ = s ≫ a
  /-- `(s, t)` is the kernel pair of the chart. -/
  isPullback_c : IsPullback (yoneda.map t) (yoneda.map s) c c

namespace LiftedEtalePresentation

variable {B S hS}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {C : SpacesEtale B S hS X}
  (P : LiftedEtalePresentation B S hS f C)

/-- The quotient sheaf of the lifted étale equivalence relation. -/
noncomputable def quotient : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  letI := BigFppfOver.hasSheafify_type B S hS
  (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
    (Over.post B.inclusion) (relation B S hS P.k₁ P.k₂)).obj

/-- The canonical map from the chart downstairs to the quotient sheaf. -/
noncomputable def toQuotient : yoneda.obj P.V ⟶ P.quotient :=
  letI := BigFppfOver.hasSheafify_type B S hS
  quotientMap B S hS P.k₁ P.k₂

/-- The quotient sheaf is an algebraic space over `S`. -/
private theorem isAlgebraicSpace_quotient : IsAlgebraicSpace B S hS P.quotient :=
  let := BigFppfOver.hasSheafify_type B S hS
  let := P.isEtaleEquivalenceRelation
  isAlgebraicSpace_quotient_unconditional B S hS P.k₁ P.k₂

/-- The quotient map is surjective. -/
private theorem surjective_toQuotient : (SurjSite B S hS).presheaf P.toQuotient :=
  let := BigFppfOver.hasSheafify_type B S hS
  let := P.isEtaleEquivalenceRelation
  quotientMap_surjective_unconditional B S hS P.k₁ P.k₂

/-- The quotient map is étale. -/
private theorem etale_toQuotient :
    (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf P.toQuotient :=
  let := BigFppfOver.hasSheafify_type B S hS
  let := P.isEtaleEquivalenceRelation
  quotientMap_etale_unconditional B S hS P.k₁ P.k₂

/-- The relation is the kernel pair of the quotient map. -/
private theorem isPullback_toQuotient :
    IsPullback (yoneda.map P.k₂) (yoneda.map P.k₁) P.toQuotient P.toQuotient :=
  let := BigFppfOver.hasSheafify_type B S hS
  let := P.isEtaleEquivalenceRelation
  quotientMap_isPullback B S hS P.k₁ P.k₂

end LiftedEtalePresentation

/-! ### Existence of a lifted étale presentation from the charts -/

/-- Given the data and the three cartesian squares produced by
`exists_liftedEtalePresentation_charts_of_isClosedImmersion_of_isSurjective`, an integral,
universally injective and surjective `f` admits a lifted étale presentation of `C`. -/
theorem nonempty_liftedEtalePresentation_of_charts (f : X ⟶ Y)
    (hint : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) (C : SpacesEtale B S hS X)
    {V W U R : BigFppfOver B S hS} {v : yoneda.obj V ⟶ Y.1} {w : yoneda.obj W ⟶ Y.1}
    {c : yoneda.obj U ⟶ C.1.left.1} {a : U ⟶ V} {b : R ⟶ W} {s t : R ⟶ U}
    (hv : IsEtale B S hS v) (hw : IsEtale B S hS w) (hc : IsEtale B S hS c)
    (hcS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) c)
    (hA : IsPullback (yoneda.map a) (c ≫ C.1.hom.hom) v f.hom)
    (hC : IsPullback (yoneda.map t) (yoneda.map s) c c)
    (hB : IsPullback (yoneda.map b) (yoneda.map t ≫ c ≫ C.1.hom.hom) w f.hom) :
    Nonempty (LiftedEtalePresentation B S hS f C) := by
  have hVas := isAlgebraicSpace_yoneda B S hS V
  have hWas := isAlgebraicSpace_yoneda B S hS W
  have hUas := isAlgebraicSpace_yoneda B S hS U
  have hRas := isAlgebraicSpace_yoneda B S hS R
  have hd₁ : (yoneda.map t ≫ yoneda.map a) ≫ v = yoneda.map b ≫ w := by
    rw [Category.assoc, hA.w, hB.w]
    simp only [Category.assoc]
  obtain ⟨κ₁, ⟨hκ₁b, hκ₁v⟩, -⟩ :=
    existsUnique_hom_presheaf_of_isIntegralHom_of_universallyInjective B S hS f hint hui hsurj
      hWas hVas hRas hB v hv (yoneda.map t ≫ yoneda.map a) hd₁
  have hd₂ : (yoneda.map s ≫ yoneda.map a) ≫ v = yoneda.map b ≫ w := by
    rw [Category.assoc, hA.w, hB.w]
    simp only [← Category.assoc]
    rw [← hC.w]
  obtain ⟨κ₂, ⟨hκ₂b, hκ₂v⟩, -⟩ :=
    existsUnique_hom_presheaf_of_isIntegralHom_of_universallyInjective B S hS f hint hui hsurj
      hWas hVas hRas hB v hv (yoneda.map s ≫ yoneda.map a) hd₂
  obtain ⟨k₁, rfl⟩ := yoneda.map_surjective κ₁
  obtain ⟨k₂, rfl⟩ := yoneda.map_surjective κ₂
  have hbk₁ : b ≫ k₁ = t ≫ a :=
    yoneda.map_injective (by rwa [Functor.map_comp, Functor.map_comp])
  have hbk₂ : b ≫ k₂ = s ≫ a :=
    yoneda.map_injective (by rwa [Functor.map_comp, Functor.map_comp])
  have hPB : IsPullback (yoneda.map b) (yoneda.map t) (yoneda.map k₁) (yoneda.map a) := by
    refine IsPullback.of_bot ?_ ?_ hA
    · rwa [hκ₁v]
    · rw [← Functor.map_comp, ← Functor.map_comp, hbk₁]
  have hbk₂' : yoneda.map b ≫ yoneda.map k₂ = yoneda.map s ≫ yoneda.map a := by
    rw [← Functor.map_comp, ← Functor.map_comp, hbk₂]
  have hwP : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf w :=
    etalePresheaf_of_isEtale_yonedaDomain B S hS w hw
  have hvP : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf v :=
    etalePresheaf_of_isEtale_yonedaDomain B S hS v hv
  have hk₁E : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k₁) :=
    etale_of_comp_etale_chart B S hS hwP hvP hκ₁v
  have hk₂E : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map k₂) :=
    etale_of_comp_etale_chart B S hS hwP hvP hκ₂v
  have hQex : ∀ (T : BigFppfOver B S hS) (z : yoneda.obj T ⟶ Y.1),
      ∃ (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (πQ : Q ⟶ yoneda.obj T) (qQ : Q ⟶ X.1),
        IsAlgebraicSpace B S hS Q ∧ IsPullback πQ qQ z f.hom := fun T z =>
    ⟨_, _, _, isAlgebraicSpace_pullback B S hS _ f.hom
      (isAlgebraicSpace_yoneda B S hS T) X.property Y.property,
      IsPullback.of_hasPullback _ _⟩
  have hleg : ∀ {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (qQ : Q ⟶ X.1) (ξ : Q ⟶ yoneda.obj R)
      (p : R ⟶ U), yoneda.map p ≫ c = yoneda.map t ≫ c →
      ξ ≫ (yoneda.map t ≫ c ≫ C.1.hom.hom) = qQ → (ξ ≫ yoneda.map p) ≫ c ≫ C.1.hom.hom = qQ := by
    intro Q qQ ξ p hpc hξX
    rw [← hξX]
    simp only [Category.assoc, reassoc_of% hpc]
  have hjm : ∀ (T : BigFppfOver B S hS) (x y : T ⟶ W), x ≫ k₂ = y ≫ k₂ → x ≫ k₁ = y ≫ k₁ →
      x = y := by
    intro T x y h₂ h₁
    apply yoneda.map_injective
    have hyw : yoneda.map y ≫ w = yoneda.map x ≫ w := by
      rw [← hκ₁v]
      simp only [← Category.assoc, ← Functor.map_comp]
      rw [h₁]
    obtain ⟨Q, πQ, qQ, hQas, hQ⟩ := hQex T (yoneda.map x ≫ w)
    have hxQ : (πQ ≫ yoneda.map x) ≫ w = qQ ≫ f.hom := by
      rw [Category.assoc]; exact hQ.w
    have hyQ : (πQ ≫ yoneda.map y) ≫ w = qQ ≫ f.hom := by
      rw [Category.assoc, hyw]; exact hQ.w
    obtain ⟨ξx, hξx, hξxX⟩ := hB.exists_lift _ _ hxQ
    obtain ⟨ξy, hξy, hξyX⟩ := hB.exists_lift _ _ hyQ
    have hkey : ∀ (k : W ⟶ V) (p : R ⟶ U),
        yoneda.map b ≫ yoneda.map k = yoneda.map p ≫ yoneda.map a →
        yoneda.map p ≫ c = yoneda.map t ≫ c → x ≫ k = y ≫ k →
        ξx ≫ yoneda.map p = ξy ≫ yoneda.map p := by
      intro k p hkp hpc hxy
      refine hA.hom_ext ?_ ((hleg qQ ξx p hpc hξxX).trans (hleg qQ ξy p hpc hξyX).symm)
      calc (ξx ≫ yoneda.map p) ≫ yoneda.map a
          = (ξx ≫ yoneda.map b) ≫ yoneda.map k := by
            simp only [Category.assoc, hkp]
        _ = (πQ ≫ yoneda.map x) ≫ yoneda.map k := by rw [hξx]
        _ = (πQ ≫ yoneda.map y) ≫ yoneda.map k := by
            simp only [Category.assoc, ← Functor.map_comp]
            rw [hxy]
        _ = (ξy ≫ yoneda.map b) ≫ yoneda.map k := by rw [hξy]
        _ = (ξy ≫ yoneda.map p) ≫ yoneda.map a := by
            simp only [Category.assoc, hkp]
    have hξ : ξx = ξy :=
      hC.hom_ext (hkey k₁ t hPB.w rfl h₁) (hkey k₂ s hbk₂' hC.w.symm h₂)
    refine hom_ext_presheaf_of_isSurjective B S hS f hsurj
      (isAlgebraicSpace_yoneda B S hS T) hWas hQas hQ w hw (yoneda.map x) (yoneda.map y)
      rfl hyw ?_
    rw [← hξx, ← hξy, hξ]
  obtain ⟨ρ, hρt, hρs⟩ : ∃ ρ : U ⟶ R, ρ ≫ t = 𝟙 U ∧ ρ ≫ s = 𝟙 U := by
    refine ⟨yoneda.preimage (hC.lift (𝟙 _) (𝟙 _) rfl), yoneda.map_injective ?_,
      yoneda.map_injective ?_⟩
    · rw [Functor.map_comp, yoneda.map_preimage, hC.lift_fst, CategoryTheory.Functor.map_id]
    · rw [Functor.map_comp, yoneda.map_preimage, hC.lift_snd, CategoryTheory.Functor.map_id]
  obtain ⟨μ, hμt, hμs⟩ : ∃ μ : R ⟶ R, μ ≫ t = s ∧ μ ≫ s = t := by
    refine ⟨yoneda.preimage (hC.lift (yoneda.map s) (yoneda.map t) hC.w.symm),
      yoneda.map_injective ?_, yoneda.map_injective ?_⟩
    · rw [Functor.map_comp, yoneda.map_preimage, hC.lift_fst]
    · rw [Functor.map_comp, yoneda.map_preimage, hC.lift_snd]
  have hdr : yoneda.map (ρ ≫ b) ≫ w = yoneda.map a ≫ v := by
    rw [Functor.map_comp, Category.assoc, hB.w, hA.w]
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [hρt, CategoryTheory.Functor.map_id, Category.id_comp]
  obtain ⟨r₀, ⟨hr₀a, hr₀w⟩, -⟩ :=
    existsUnique_hom_presheaf_of_isIntegralHom_of_universallyInjective B S hS f hint hui hsurj
      hVas hWas hUas hA w hw (yoneda.map (ρ ≫ b)) hdr
  obtain ⟨rr, rfl⟩ := yoneda.map_surjective r₀
  have hrefl : ∀ (k : W ⟶ V) (p : R ⟶ U),
      yoneda.map b ≫ yoneda.map k = yoneda.map p ≫ yoneda.map a →
      ρ ≫ p = 𝟙 U → yoneda.map k ≫ v = w → rr ≫ k = 𝟙 V := by
    intro k p hkp hρp hkv
    apply yoneda.map_injective
    refine hom_ext_presheaf_of_isSurjective B S hS f hsurj hVas hVas hUas hA v hv
      (yoneda.map (rr ≫ k)) (yoneda.map (𝟙 V)) ?_ ?_ ?_
    · rw [Functor.map_comp, Category.assoc, hkv]
      exact hr₀w
    · rw [CategoryTheory.Functor.map_id, Category.id_comp]
    · rw [CategoryTheory.Functor.map_id, Category.comp_id, Functor.map_comp, ← Category.assoc, hr₀a]
      simp only [Functor.map_comp, Category.assoc, hkp]
      simp only [← Category.assoc, ← Functor.map_comp]
      rw [hρp, Category.id_comp]
  have hds : yoneda.map (μ ≫ b) ≫ w = yoneda.map b ≫ w := by
    rw [Functor.map_comp, Category.assoc, hB.w]
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [hμt, hC.w]
  obtain ⟨σ₀, ⟨hσ₀b, hσ₀w⟩, -⟩ :=
    existsUnique_hom_presheaf_of_isIntegralHom_of_universallyInjective B S hS f hint hui hsurj
      hWas hWas hRas hB w hw (yoneda.map (μ ≫ b)) hds
  obtain ⟨σ, rfl⟩ := yoneda.map_surjective σ₀
  have hsymm : ∀ (k k' : W ⟶ V) (p p' : R ⟶ U),
      yoneda.map b ≫ yoneda.map k = yoneda.map p ≫ yoneda.map a →
      yoneda.map b ≫ yoneda.map k' = yoneda.map p' ≫ yoneda.map a →
      μ ≫ p = p' → yoneda.map k ≫ v = w → yoneda.map k' ≫ v = w → σ ≫ k = k' := by
    intro k k' p p' hkp hkp' hμp hkv hkv'
    apply yoneda.map_injective
    refine hom_ext_presheaf_of_isSurjective B S hS f hsurj hWas hVas hRas hB v hv
      (yoneda.map (σ ≫ k)) (yoneda.map k') ?_ hkv' ?_
    · rw [Functor.map_comp, Category.assoc, hkv]
      exact hσ₀w
    · rw [Functor.map_comp, ← Category.assoc, hσ₀b]
      simp only [Functor.map_comp, Category.assoc, hkp, hkp']
      simp only [← Category.assoc, ← Functor.map_comp]
      rw [hμp]
  let : HasPullbacks (BigFppfOver B S hS) := inferInstance
  obtain ⟨Q, πQ, qQ, hQas, hQ⟩ := hQex (pullback k₁ k₂) (yoneda.map (pullback.fst k₁ k₂) ≫ w)
  have hπ₂w : yoneda.map (pullback.snd k₁ k₂) ≫ w = yoneda.map (pullback.fst k₁ k₂) ≫ w :=
    calc yoneda.map (pullback.snd k₁ k₂) ≫ w
        = yoneda.map (pullback.snd k₁ k₂ ≫ k₂) ≫ v := by
          rw [← hκ₂v, Functor.map_comp, Category.assoc]
      _ = yoneda.map (pullback.fst k₁ k₂ ≫ k₁) ≫ v := by rw [← pullback.condition]
      _ = yoneda.map (pullback.fst k₁ k₂) ≫ w := by
          rw [← hκ₁v, Functor.map_comp, Category.assoc]
  have hQ₁ : (πQ ≫ yoneda.map (pullback.fst k₁ k₂)) ≫ w = qQ ≫ f.hom := by
    rw [Category.assoc]; exact hQ.w
  have hQ₂ : (πQ ≫ yoneda.map (pullback.snd k₁ k₂)) ≫ w = qQ ≫ f.hom := by
    rw [Category.assoc, hπ₂w]; exact hQ.w
  obtain ⟨ζ₁, hζ₁b, hζ₁x⟩ := hB.exists_lift _ _ hQ₁
  obtain ⟨ζ₂, hζ₂b, hζ₂x⟩ := hB.exists_lift _ _ hQ₂
  have hcross : ζ₁ ≫ yoneda.map t = ζ₂ ≫ yoneda.map s := by
    refine hA.hom_ext ?_ ?_
    · calc (ζ₁ ≫ yoneda.map t) ≫ yoneda.map a
          = (ζ₁ ≫ yoneda.map b) ≫ yoneda.map k₁ := by simp only [Category.assoc, hPB.w]
        _ = πQ ≫ yoneda.map (pullback.fst k₁ k₂ ≫ k₁) := by
            rw [hζ₁b, Functor.map_comp, Category.assoc]
        _ = πQ ≫ yoneda.map (pullback.snd k₁ k₂ ≫ k₂) := by rw [pullback.condition]
        _ = (ζ₂ ≫ yoneda.map b) ≫ yoneda.map k₂ := by
            rw [hζ₂b, Functor.map_comp, Category.assoc]
        _ = (ζ₂ ≫ yoneda.map s) ≫ yoneda.map a := by simp only [Category.assoc, hbk₂']
    · exact (hleg qQ ζ₁ t rfl hζ₁x).trans (hleg qQ ζ₂ s hC.w.symm hζ₂x).symm
  have hzc : (ζ₂ ≫ yoneda.map t) ≫ c = (ζ₁ ≫ yoneda.map s) ≫ c := by
    simp only [Category.assoc, ← hC.w]
    rw [← Category.assoc, ← Category.assoc, hcross]
    simp only [Category.assoc, hC.w]
  obtain ⟨ζ, hζt, hζs⟩ : ∃ ζ : Q ⟶ yoneda.obj R,
      ζ ≫ yoneda.map t = ζ₂ ≫ yoneda.map t ∧ ζ ≫ yoneda.map s = ζ₁ ≫ yoneda.map s :=
    ⟨hC.lift _ _ hzc, hC.lift_fst _ _ hzc, hC.lift_snd _ _ hzc⟩
  have hζx : ζ ≫ yoneda.map t ≫ c ≫ C.1.hom.hom = qQ := by
    rw [← Category.assoc ζ (yoneda.map t) (c ≫ C.1.hom.hom), hζt, Category.assoc]
    exact hζ₂x
  have hdt : (ζ ≫ yoneda.map b) ≫ w = πQ ≫ yoneda.map (pullback.fst k₁ k₂) ≫ w := by
    rw [Category.assoc, hB.w, ← Category.assoc, hζx]
    exact hQ.w.symm
  obtain ⟨τ₀, ⟨hτ₀Q, hτ₀w⟩, -⟩ :=
    existsUnique_hom_presheaf_of_isIntegralHom_of_universallyInjective B S hS f hint hui hsurj
      (isAlgebraicSpace_yoneda B S hS (pullback k₁ k₂)) hWas hQas hQ w hw
      (ζ ≫ yoneda.map b) hdt
  obtain ⟨τ, rfl⟩ := yoneda.map_surjective τ₀
  have htrans : ∀ (k : W ⟶ V) (p : R ⟶ U) (π : pullback k₁ k₂ ⟶ W) (ζ' : Q ⟶ yoneda.obj R),
      yoneda.map b ≫ yoneda.map k = yoneda.map p ≫ yoneda.map a →
      ζ ≫ yoneda.map p = ζ' ≫ yoneda.map p →
      ζ' ≫ yoneda.map b = πQ ≫ yoneda.map π →
      yoneda.map k ≫ v = w → yoneda.map π ≫ w = yoneda.map (pullback.fst k₁ k₂) ≫ w →
      τ ≫ k = π ≫ k := by
    intro k p π ζ' hkp hζp hζ'b hkv hπw
    apply yoneda.map_injective
    refine hom_ext_presheaf_of_isSurjective B S hS f hsurj
      (isAlgebraicSpace_yoneda B S hS (pullback k₁ k₂)) hVas hQas hQ v hv
      (yoneda.map (τ ≫ k)) (yoneda.map (π ≫ k)) ?_ ?_ ?_
    · rwa [Functor.map_comp, Category.assoc, hkv]
    · rwa [Functor.map_comp, Category.assoc, hkv]
    · rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc, hτ₀Q]
      rw [Category.assoc, hkp, ← Category.assoc, hζp, Category.assoc, ← hkp, ← Category.assoc,
        hζ'b]
  have esite : EquivalenceRelation k₂ k₁ :=
    { right_cancellation := hjm
      r := rr
      reflexivity₁ := hrefl k₂ s hbk₂' hρs hκ₂v
      reflexivity₂ := hrefl k₁ t hPB.w hρt hκ₁v
      s := σ
      symmetry₁ := hsymm k₂ k₁ s t hbk₂' hPB.w hμs hκ₂v hκ₁v
      symmetry₂ := hsymm k₁ k₂ t s hPB.w hbk₂' hμt hκ₁v hκ₂v
      c := pullback.cone k₁ k₂
      isLimit := pullback.isLimit k₁ k₂
      t := τ
      transitivity₁ := htrans k₂ s (pullback.fst k₁ k₂) ζ₁ hbk₂' hζs hζ₁b hκ₂v rfl
      transitivity₂ := htrans k₁ t (pullback.snd k₁ k₂) ζ₂ hPB.w hζt hζ₂b hκ₁v hπ₂w }
  refine ⟨{
    V := V
    W := W
    U := U
    R := R
    v := v
    w := w
    isEtale_v := hv
    isEtale_w := hw
    k₁ := k₁
    k₂ := k₂
    comp_k₁ := hκ₁v
    comp_k₂ := hκ₂v
    c := c
    isEtale_c := hc
    surjective_c := hcS
    a := a
    b := b
    s := s
    t := t
    isPullback_a := hA
    isPullback_b := hPB
    comp_b_k₂ := hbk₂
    isPullback_c := hC
    isEtaleEquivalenceRelation := ?_ }⟩
  have htarget : (relation B S hS k₁ k₂).target = (Over.post B.inclusion).map k₂ :=
    prod.lift_fst _ _
  have hsource : (relation B S hS k₁ k₂).source = (Over.post B.inclusion).map k₁ :=
    prod.lift_snd _ _
  refine { isEquivalenceRelation := ?_, etale_source := ?_, etale_target := ?_ }
  · rw [htarget, hsource]
    exact isEquivalenceRelation_post_inclusion B S hS esite
  · rwa [hsource]
  · rwa [htarget]

/-- Every object of the spaces-étale site of `X` admits a lifted étale presentation across a
surjective closed immersion `f`. -/
theorem nonempty_liftedEtalePresentation_of_isClosedImmersion_of_isSurjective (f : X ⟶ Y)
    (hci : IsClosedImmersion B S hS f.hom) (hsurj : IsSurjective B S hS f.hom)
    (C : SpacesEtale B S hS X) :
    Nonempty (LiftedEtalePresentation B S hS f C) := by
  obtain ⟨hint, hui⟩ := isIntegralHom_universallyInjective_of_isClosedImmersion B S hS f.hom hci
  obtain ⟨V, W, U, R, v, w, c, a, b, s, t, hv, hw, hc, hcS, hA, hC, hB⟩ :=
    exists_liftedEtalePresentation_charts_of_isClosedImmersion_of_isSurjective B S hS f hci
      hsurj C
  exact nonempty_liftedEtalePresentation_of_charts B S hS f hint hui hsurj C
    hv hw hc hcS hA hC hB

/-- Every object of the spaces-étale site of `X` admits a lifted étale presentation across the
inclusion `f` of a first-order thickening. -/
theorem nonempty_liftedEtalePresentation (f : X ⟶ Y) [Mono f.hom]
    (hT : IsFirstOrderThickening B S hS Y (Subfunctor.range f.hom))
    (C : SpacesEtale B S hS X) :
    Nonempty (LiftedEtalePresentation B S hS f C) :=
  have h := isClosedImmersion_isSurjective_of_isThickening_range B S hS f
    (hT.isThickening B S hS)
  nonempty_liftedEtalePresentation_of_isClosedImmersion_of_isSurjective B S hS f h.1 h.2 C


variable {f : X ⟶ Y} {C : SpacesEtale B S hS X}

/-! ### From a lifted étale presentation to an object of the spaces-étale site of `Y` -/

/-- The quotient of a lifted étale presentation of `C` is an object of the spaces-étale site of
`Y` whose base change along `f` is `C`. -/
theorem exists_iso_functor_obj_of_liftedEtalePresentation
    (P : LiftedEtalePresentation B S hS f C) :
    ∃ D : SpacesEtale B S hS Y,
      Nonempty ((spacesBaseChange B S hS f).functor.obj D ≅ C) := by
  have hcP : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf P.c :=
    etalePresheaf_of_isEtale_yonedaDomain B S hS P.c P.isEtale_c
  obtain ⟨d, hd, -⟩ := existsUnique_desc_of_surjectiveEtale B S hS P.toQuotient P.k₂ P.k₁
    P.isPullback_toQuotient P.isAlgebraicSpace_quotient P.surjective_toQuotient
    P.etale_toQuotient Y.2.isSheaf P.v (by rw [P.comp_k₁, P.comp_k₂])
  have hdEtale : IsEtale B S hS d := by
    refine (isEtale_iff_exists_source_chart B S hS P.isAlgebraicSpace_quotient Y.2 d).2
      ⟨P.V, P.toQuotient, P.surjective_toQuotient, P.etale_toQuotient, ?_⟩
    rw [hd]
    exact P.isEtale_v
  refine ⟨⟨Over.mk (ObjectProperty.homMk d :
    (⟨P.quotient, P.isAlgebraicSpace_quotient⟩ : AlgebraicSpaces B S hS) ⟶ Y), hdEtale⟩, ?_⟩
  set D : SpacesEtale B S hS Y := ⟨Over.mk (ObjectProperty.homMk d :
    (⟨P.quotient, P.isAlgebraicSpace_quotient⟩ : AlgebraicSpaces B S hS) ⟶ Y), hdEtale⟩ with hD
  set FD := (spacesBaseChange B S hS f).functor.obj D with hFD
  have hDpb : IsPullback ((spacesBaseChange B S hS f).projection.app D).hom FD.1.hom.hom
      d f.hom :=
    AlgebraicSpaces.isPullback_hom B S hS ((spacesBaseChange B S hS f).isPullback D)
  have hlift : (yoneda.map P.a ≫ P.toQuotient) ≫ d = (P.c ≫ C.1.hom.hom) ≫ f.hom := by
    rw [Category.assoc, hd]
    exact P.isPullback_a.w
  set aC := hDpb.lift (yoneda.map P.a ≫ P.toQuotient) (P.c ≫ C.1.hom.hom) hlift with haC
  have haCfst : aC ≫ ((spacesBaseChange B S hS f).projection.app D).hom
      = yoneda.map P.a ≫ P.toQuotient := hDpb.lift_fst _ _ _
  have haCsnd : aC ≫ FD.1.hom.hom = P.c ≫ C.1.hom.hom := hDpb.lift_snd _ _ _
  have hAC : IsPullback (yoneda.map P.a) aC P.toQuotient
      ((spacesBaseChange B S hS f).projection.app D).hom := by
    refine IsPullback.of_bot ?_ haCfst.symm hDpb
    rw [haCsnd, hd]
    exact P.isPullback_a
  have haCsurj : (SurjSite B S hS).presheaf aC :=
    surjectivePresheaf_of_isPullback B S hS hAC P.surjective_toQuotient
  have haCetale : (AlgebraicGeometry.FormalSpace.etaleProperty B S hS).presheaf aC :=
    etalePresheaf_of_isPullback B S hS hAC P.etale_toQuotient
  have hta : yoneda.map P.t ≫ yoneda.map P.a = yoneda.map P.b ≫ yoneda.map P.k₁ :=
    P.isPullback_b.w.symm
  have hsa : yoneda.map P.s ≫ yoneda.map P.a = yoneda.map P.b ≫ yoneda.map P.k₂ := by
    rw [← yoneda.map_comp, ← yoneda.map_comp, P.comp_b_k₂]
  have hp : yoneda.map P.t ≫ aC = yoneda.map P.s ≫ aC := by
    refine hDpb.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, haCfst, ← Category.assoc, ← Category.assoc, hta, hsa,
        Category.assoc, Category.assoc, P.isPullback_toQuotient.w]
    · rw [Category.assoc, Category.assoc, haCsnd, ← Category.assoc, ← Category.assoc,
        P.isPullback_c.w]
  have hstep : IsPullback (yoneda.map P.t) (yoneda.map P.s ≫ yoneda.map P.a)
      (aC ≫ ((spacesBaseChange B S hS f).projection.app D).hom) P.toQuotient := by
    rw [hsa, haCfst]
    exact P.isPullback_b.flip.paste_vert P.isPullback_toQuotient.flip
  have hkerAC : IsPullback (yoneda.map P.t) (yoneda.map P.s) aC aC :=
    IsPullback.of_bot hstep hp hAC.flip
  obtain ⟨e, he, -⟩ := existsUnique_desc_of_surjectiveEtale B S hS P.c P.t P.s P.isPullback_c
    C.1.left.2 P.surjective_c hcP FD.1.left.2.isSheaf aC hp
  obtain ⟨e', he', -⟩ := existsUnique_desc_of_surjectiveEtale B S hS aC P.t P.s hkerAC
    FD.1.left.2 haCsurj haCetale C.1.left.2.isSheaf P.c P.isPullback_c.w
  have hee' : e ≫ e' = 𝟙 _ :=
    hom_ext_of_surjectiveEtale B S hS P.c P.t P.s P.isPullback_c C.1.left.2 P.surjective_c hcP
      C.1.left.2.isSheaf _ _ (by rw [← Category.assoc, he, he', Category.comp_id])
  have he'e : e' ≫ e = 𝟙 _ :=
    hom_ext_of_surjectiveEtale B S hS aC P.t P.s hkerAC FD.1.left.2 haCsurj haCetale
      FD.1.left.2.isSheaf _ _ (by rw [← Category.assoc, he', he, Category.comp_id])
  have hcomm : e ≫ FD.1.hom.hom = C.1.hom.hom :=
    hom_ext_of_surjectiveEtale B S hS P.c P.t P.s P.isPullback_c C.1.left.2 P.surjective_c hcP
      X.2.isSheaf _ _ (by rw [← Category.assoc, he, haCsnd])
  exact ⟨(ObjectProperty.isoMk _ (Over.isoMk
    (ObjectProperty.isoMk _ ⟨e, e', hee', he'e⟩) (ObjectProperty.hom_ext _ hcomm))).symm⟩


/-! ### Essential surjectivity, and the equivalence -/

/-- Base change `V ↦ X ×_Y V` is essentially surjective from the spaces-étale site of `Y` to that
of `X`, for a surjective closed immersion `f`. -/
theorem essSurj_spacesBaseChange_of_isClosedImmersion_of_isSurjective (f : X ⟶ Y)
    (hci : IsClosedImmersion B S hS f.hom) (hsurj : IsSurjective B S hS f.hom) :
    (spacesBaseChange B S hS f).functor.EssSurj where
  mem_essImage C := by
    obtain ⟨P⟩ :=
      nonempty_liftedEtalePresentation_of_isClosedImmersion_of_isSurjective B S hS f hci hsurj C
    exact exists_iso_functor_obj_of_liftedEtalePresentation B S hS P

/-- Base change `V ↦ X ×_Y V` is an equivalence from the spaces-étale site of `Y` to that of `X`,
for a surjective closed immersion `f`. -/
@[stacks 05ZL "the identification of the two spaces-étale sites: base change along the \
inclusion of a thickening of arbitrary order is an equivalence of categories"]
theorem isEquivalence_spacesBaseChange_of_isClosedImmersion_of_isSurjective (f : X ⟶ Y)
    (hci : IsClosedImmersion B S hS f.hom) (hsurj : IsSurjective B S hS f.hom) :
    (spacesBaseChange B S hS f).functor.IsEquivalence :=
  have hiu := isIntegralHom_universallyInjective_of_isClosedImmersion B S hS f.hom hci
  let := full_spacesBaseChange_of_isIntegralHom_of_universallyInjective B S hS f hiu.1 hiu.2
    hsurj
  let := faithful_spacesBaseChange_of_isIntegralHom_of_universallyInjective B S hS f hiu.1
    hiu.2 hsurj
  let := essSurj_spacesBaseChange_of_isClosedImmersion_of_isSurjective B S hS f hci hsurj
  ⟨inferInstance, inferInstance, inferInstance⟩

/-! ### The first-order case -/

/-- Base change `V ↦ X ×_Y V` is essentially surjective from the spaces-étale site of `Y` to that
of `X`, for the inclusion `f` of a first-order thickening. -/
@[stacks 05ZH "essential surjectivity at a first-order thickening"]
theorem essSurj_spacesBaseChange_of_isFirstOrderThickening (f : X ⟶ Y) [Mono f.hom]
    (hT : IsFirstOrderThickening B S hS Y (Subfunctor.range f.hom)) :
    (spacesBaseChange B S hS f).functor.EssSurj :=
  have h := isClosedImmersion_isSurjective_of_isThickening_range B S hS f
    (hT.isThickening B S hS)
  essSurj_spacesBaseChange_of_isClosedImmersion_of_isSurjective B S hS f h.1 h.2

/-- Base change `V ↦ X ×_Y V` is an equivalence from the spaces-étale site of `Y` to that of `X`,
for the inclusion `f` of a first-order thickening. -/
@[stacks 05ZH "the first-order thickening case, not the integral universally injective one"]
theorem isEquivalence_spacesBaseChange_of_isFirstOrderThickening (f : X ⟶ Y) [Mono f.hom]
    (hT : IsFirstOrderThickening B S hS Y (Subfunctor.range f.hom)) :
    (spacesBaseChange B S hS f).functor.IsEquivalence :=
  have h := isClosedImmersion_isSurjective_of_isThickening_range B S hS f
    (hT.isThickening B S hS)
  isEquivalence_spacesBaseChange_of_isClosedImmersion_of_isSurjective B S hS f h.1 h.2

end AlgebraicGeometry.Space

end
