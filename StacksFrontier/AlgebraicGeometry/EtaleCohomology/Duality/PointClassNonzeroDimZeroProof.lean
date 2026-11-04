module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PointClassNonzeroPointwise
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.StratumShortExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleOpens

/-!
# The class of a point is nonzero in relative dimension zero

Let `k` be a field, `ℓ` a prime and `Λ = ℤ/ℓ`. For `W` smooth irreducible of relative dimension
zero over `k` with a compactification `j : W → X̄`, and a `k`-point `i : P → N` closed in an open
`n : N → W`, some `γ₀` and some `z : Λ_X̄ → (n ≫ j)_! i_* Λ_P` have `z ∘ (n ≫ j)_! γ₀ ≠ 0` in
`H⁰_c(W) = Ext⁰_X̄(Λ, j_! Λ_W)` (`Stacks.EtaleCohomology.pointClassNonzeroDimZero`).

The proof is the one of `Stacks.EtaleCohomology.curvePointClassNonzero` in degree zero. The
scheme `W` is a single point, the image of `P`. With `V = X̄ ∖ {P}`, the short exact sequence
`0 → V_! Λ_V → Λ_X̄ → (n ≫ j)_! i_* Λ_P → 0` gives the exact sequence
`Ext⁰((n ≫ j)_! i_* Λ_P, j_! Λ_W) → H⁰_c(W) → Ext⁰(V_! Λ_V, j_! Λ_W)`, and the last group is zero
since `V` misses `W`, so that `j_! Λ_W` restricts to zero on `V`. And `H⁰_c(W) ≅ Λ ≠ 0`
(`Stacks.EtaleCohomology.nonempty_ext_zero_addEquiv_zmod_of_smoothOfRelativeDimension_zero`).

## Main results

* `Stacks.EtaleCohomology.pointClassNonzeroDimZero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-- If `V` is the complement of the image of `g ≫ h`, that image is the image of `h` minus `V`. -/
theorem range_comp_base_eq_diff_of_coe_eq_compl {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (V : Z.Opens) (hV : (V : Set Z) = (Set.range (g ≫ h).base)ᶜ) :
    Set.range (g ≫ h).base = Set.range h.base \ (V : Set Z) := by
  rw [hV]
  ext y
  refine ⟨fun hy => ⟨?_, fun hyV => hyV hy⟩, fun hy => of_not_not hy.2⟩
  obtain ⟨p, rfl⟩ := hy
  exact ⟨g.base p, (Scheme.Hom.comp_apply g h p).symm⟩

/-- If `V` is the complement of the image of `g ≫ h`, then `V` and the image of `h` cover `Z`. -/
theorem sup_opensRange_eq_top_of_coe_eq_compl {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    [IsOpenImmersion h] (V : Z.Opens) (hV : (V : Set Z) = (Set.range (g ≫ h).base)ᶜ) :
    V ⊔ h.opensRange = ⊤ := by
  refine eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_sup.2 ?_
  by_cases hy : y ∈ Set.range (g ≫ h).base
  · obtain ⟨p, rfl⟩ := hy
    exact Or.inr ⟨g.base p, (Scheme.Hom.comp_apply g h p).symm⟩
  · exact Or.inl (by rw [← SetLike.mem_coe, hV]; exact hy)

/-- Given a short exact sequence `0 → S₁ → S₂ → S₃ → 0` with `Ext⁰(S₁, G) = 0` and
`Ext⁰(A, G) ≠ 0` for `A ≅ S₂`, some `x ∈ Ext⁰(B, G)` for `B ≅ S₃` has a nonzero pullback to `A`. -/
theorem exists_mk₀_comp_ne_zero_of_shortExact.{w, v, w'} {C : Type w'} [Category.{v} C]
    [Abelian C] [HasExt.{w} C] {S : ShortComplex C} (hS : S.ShortExact) {A B : C} (G : C)
    (eY : S.X₂ ≅ A) (eC : S.X₃ ≅ B) (h₁ : Subsingleton (Ext.{w} S.X₁ G 0))
    [Nontrivial (Ext.{w} A G 0)] :
    ∃ x : Ext.{w} B G 0, (Ext.mk₀ (eY.inv ≫ S.g ≫ eC.hom)).comp x (zero_add 0) ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_ne (0 : Ext.{w} A G 0)
  obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₂ hS G ((Ext.mk₀ eY.hom).comp z (zero_add 0))
    (@Subsingleton.elim _ h₁ _ _)
  refine ⟨(Ext.mk₀ eC.inv).comp x (zero_add 0), ?_⟩
  rwa [Ext.mk₀_comp_mk₀_assoc, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    ← Ext.mk₀_comp_mk₀_assoc, hx, Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id, Ext.mk₀_id_comp]

/-- If the open `V` misses the image of the open immersion `j`, then
`Ext⁰(V_! Λ_V, j_! Λ_W) = 0`, since `j_! Λ_W` restricts to zero on `V`. -/
theorem subsingleton_ext_zero_extensionByZero_of_disjoint (ℓ : ℕ) [Fact ℓ.Prime]
    {X W : Scheme.{u}} (V : X.Opens) (j : W ⟶ X) [IsOpenImmersion j]
    (hdisj : Disjoint (Set.range V.ι.base) (Set.range j.base)) :
    Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) V.ι).obj
      ((etaleModuleRestriction.{u, 0} (ZMod ℓ) V.ι).obj (unitSheaf (X := X) ℓ)))
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj (unitSheaf (X := W) ℓ)) 0) := by
  have hzero : IsZero ((etaleModuleRestriction.{u, 0} (ZMod ℓ) V.ι).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj (unitSheaf (X := W) ℓ))) :=
    IsZero.of_iso (isZero_etaleModuleInverseImage_extensionByZero_of_disjoint (ZMod ℓ) V.ι
      j hdisj _) ((etaleModuleInverseImageRestrictionIso (ZMod ℓ) V.ι).app _).symm
  have hvan₀ : Subsingleton (Ext ((etaleModuleRestriction.{u, 0} (ZMod ℓ) V.ι).obj
      (unitSheaf (X := X) ℓ)) ((etaleModuleRestriction.{u, 0} (ZMod ℓ) V.ι).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj (unitSheaf (X := W) ℓ))) 0) :=
    subsingleton_of_forall_eq 0 fun x => by
      rw [← Ext.comp_mk₀_id x, hzero.eq_of_src (𝟙 _) 0, Ext.mk₀_zero, Ext.comp_zero]
  exact @Function.Surjective.subsingleton _ _ _ hvan₀
    (Stacks.ExtAdjunction.extMap_bijective (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) V.ι)
      _ ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj (unitSheaf (X := W) ℓ)) 0).2

/-- **The class of a point is nonzero in relative dimension zero**:
`Stacks.EtaleCohomology.PointClassNonzeroDimZero ℓ k` holds for every field `k`. -/
theorem pointClassNonzeroDimZero (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] :
    PointClassNonzeroDimZero ℓ k := by
  intro W f _ _ _ jc N P n _ i _ _ _
  have : TopologicalSpace.NoetherianSpace N := n.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (n ≫ f) := ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : TopologicalSpace.NoetherianSpace P := (i ≫ n).isEmbedding.isInducing.noetherianSpace
  have : IsProper (i ≫ n ≫ f) :=
    isProper_of_smoothOfRelativeDimension_zero (i ≫ n ≫ f) ((jc.restrictOpen n).restrictClosed i)
  have hsub : Subsingleton W := subsingleton_of_smoothOfRelativeDimension_zero f
  have hPcl : IsClosed (Set.range (i ≫ n ≫ jc.immersion).base) := by
    have : IsProper ((i ≫ n ≫ jc.immersion) ≫ jc.toBase) := by
      rw [Category.assoc, Category.assoc, CompactificationOf.immersion_toBase]
      infer_instance
    have : IsProper (i ≫ n ≫ jc.immersion) := IsProper.of_comp _ jc.toBase
    exact (i ≫ n ≫ jc.immersion).isClosedMap.isClosed_range
  let V : jc.space.Opens := ⟨(Set.range (i ≫ n ≫ jc.immersion).base)ᶜ, hPcl.isOpen_compl⟩
  obtain ⟨p₀⟩ := (inferInstance : IrreducibleSpace P).toNonempty
  have hdisj : Disjoint (Set.range V.ι.base) (Set.range jc.immersion.base) := by
    rw [Scheme.Opens.range_ι, Set.disjoint_right]
    rintro _ ⟨w, rfl⟩ hw
    refine (hw : jc.immersion.base w ∉ Set.range (i ≫ n ≫ jc.immersion).base) ⟨p₀, ?_⟩
    simp [@Subsingleton.elim W hsub w (n.base (i.base p₀))]
  obtain ⟨S, hS, ⟨e₁'⟩, ⟨e₂'⟩, ⟨e₃'⟩⟩ := exists_shortExact_extensionByZero_sup_stratum (ZMod ℓ) V
    (n ≫ jc.immersion) i (range_comp_base_eq_diff_of_coe_eq_compl i (n ≫ jc.immersion) V rfl)
    (unitSheaf (X := jc.space) ℓ)
  rw [sup_opensRange_eq_top_of_coe_eq_compl i (n ≫ jc.immersion) V rfl] at e₂'
  have := isIso_etaleModuleExtensionByZeroAdj_counit_app_top (ZMod ℓ) (unitSheaf (X := jc.space) ℓ)
  let eY : S.X₂ ≅ unitSheaf (X := jc.space) ℓ := e₂' ≪≫
    asIso ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) (⊤ : jc.space.Opens).ι).counit.app
      (unitSheaf (X := jc.space) ℓ))
  let eC : S.X₃ ≅ (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
      ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := P) ℓ)) :=
    e₃' ≪≫ (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).mapIso
      ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).mapIso
        (unitSheafRestrictionIdInverseImageIso (ℓ := ℓ) (i ≫ n ≫ jc.immersion)))
  have h₁ := @Function.Surjective.subsingleton _ _ _
    (subsingleton_ext_zero_extensionByZero_of_disjoint ℓ V jc.immersion hdisj)
    (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso e₁'.hom 0).2
  obtain ⟨eH⟩ := nonempty_ext_zero_addEquiv_zmod_of_smoothOfRelativeDimension_zero ℓ f jc
  have : Nontrivial (Ext (unitSheaf (X := jc.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        (2 * 0)) := eH.toEquiv.nontrivial
  obtain ⟨x, hx⟩ := exists_mk₀_comp_ne_zero_of_shortExact hS
    ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ)) eY eC h₁
  obtain ⟨γ₀, hγ₀⟩ := (Stacks.ExtAdjunction.extMap_bijective
    (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)) _
    ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
    (2 * 0)).2 x
  exact ⟨γ₀, Ext.mk₀ (eY.inv ≫ S.g ≫ eC.hom), by rwa [hγ₀]⟩

end Stacks.EtaleCohomology

end
