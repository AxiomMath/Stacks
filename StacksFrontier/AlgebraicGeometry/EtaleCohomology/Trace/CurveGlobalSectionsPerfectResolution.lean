module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectSections
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Global sections of an injective resolution and sheaf cohomology

Let `Y` be a scheme, `Λ` a ring, not necessarily commutative, `G` a sheaf of `Λ`-modules on the
small étale site of `Y` and `I` an injective resolution of `G` concentrated in degrees `≥ 0`. The
underlying abelian sheaves of the terms of `I` are acyclic
(`Stacks.InjectiveAcyclic.subsingleton_H_forget₂`) and forgetting the `Λ`-module structure is
exact, so the underlying complex of abelian sheaves is an acyclic resolution of the underlying
abelian sheaf of `G`. Dimension shifting then embeds `Hⁱ(Γ(Y, I))` into the sheaf cohomology
`Hⁱ(Y, G)` of Mathlib (`CategoryTheory.Sheaf.H`) of the underlying abelian sheaf. This is how
the proof of [Stacks, Tag 03TV] obtains the finiteness and the vanishing in high degrees of
`RΓ(X_k̄, -)` from Tag 03SC.

## Main results

* `Stacks.EtaleResolution.preservesHomology_sheafForget`: forgetting to abelian sheaves is exact.
* `Stacks.EtaleResolution.exists_injective_homology_sections`: `Hⁱ(Γ(Y, I)) ↪ Hⁱ(Y, G)`.

## References

* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Abelian AlgebraicGeometry HomologicalComplex

universe w u r

namespace Stacks.EtaleResolution

/-! ### Forgetting to abelian groups is exact -/

section Forget

variable (Λ : Type r) [Ring Λ]

/-- Forgetting a `ℤ`-module to its abelian group is left adjoint to reading an abelian group as a
`ℤ`-module. -/
def forgetOfAbAdj :
    forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w} ⊣ Stacks.InjectiveAcyclic.ofAb.{w} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M A =>
        { toFun := fun f => ModuleCat.ofHom (StacksDraft.Perfect.intLinearMapOfAddHom f.hom)
          invFun := fun g => AddCommGrpCat.ofHom g.hom.toAddMonoidHom
          left_inv := fun f => rfl
          right_inv := fun g => rfl }
      homEquiv_naturality_left_symm := fun _ _ => rfl
      homEquiv_naturality_right := fun _ _ => rfl }

/-- Coinduction `A ↦ Hom_ℤ(Λ, A)` from abelian groups to `Λ`-modules. -/
abbrev coind : AddCommGrpCat.{max r w} ⥤ ModuleCat.{max r w} Λ :=
  (Stacks.InjectiveAcyclic.ofAb : AddCommGrpCat.{max r w} ⥤ ModuleCat.{max r w} ℤ) ⋙
    (ModuleCat.coextendScalars (Int.castRingHom Λ) : ModuleCat.{max r w} ℤ ⥤ ModuleCat.{max r w} Λ)

/-- Forgetting a `Λ`-module to its abelian group. -/
abbrev forgetAb : ModuleCat.{max r w} Λ ⥤ AddCommGrpCat.{max r w} :=
  (ModuleCat.restrictScalars (Int.castRingHom Λ) : ModuleCat.{max r w} Λ ⥤ ModuleCat.{max r w} ℤ) ⋙
    forget₂ (ModuleCat.{max r w} ℤ) AddCommGrpCat.{max r w}

/-- Forgetting a `Λ`-module to its abelian group is left adjoint to coinduction. -/
def forgetCoextendAdj : forgetAb.{w} Λ ⊣ coind.{w} Λ :=
  (ModuleCat.restrictCoextendScalarsAdj (Int.castRingHom Λ) :
      (ModuleCat.restrictScalars (Int.castRingHom Λ) :
        ModuleCat.{max r w} Λ ⥤ ModuleCat.{max r w} ℤ) ⊣ _).comp forgetOfAbAdj

variable (Y : Scheme.{u})

/-- Coinduction `coind Λ` carries sheaves of abelian groups on the small étale site of `Y` to
sheaves of `Λ`-modules. -/
instance hasSheafCompose_coind :
    Y.smallEtaleTopology.HasSheafCompose (coind.{u + 1} Λ) := by
  have : (coind.{u + 1} Λ).IsRightAdjoint := (forgetCoextendAdj.{u + 1} Λ).isRightAdjoint
  have : PreservesLimitsOfSize.{u, u + 1} (coind.{u + 1} Λ) :=
    preservesLimitsOfSize_shrink.{u + 1, max (u + 1) r, u, max (u + 1) r} _
  infer_instance

/-- The underlying abelian sheaf of a sheaf of `Λ`-modules on the small étale site of `Y`. -/
abbrev sheafForget : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y ⥤
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) r} :=
  sheafCompose Y.smallEtaleTopology (forgetAb.{u + 1} Λ)

/-- Forgetting to the underlying abelian sheaf is left adjoint to sheafified coinduction. -/
def sheafForgetAdj :
    sheafForget Λ Y ⊣ sheafCompose Y.smallEtaleTopology (coind.{u + 1} Λ) :=
  Adjunction.restrictFullyFaithful
    ((forgetCoextendAdj.{u + 1} Λ).whiskerRight Y.Etaleᵒᵖ)
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _) (Iso.refl _) (Iso.refl _)

/-- Forgetting to the underlying abelian sheaf is a left adjoint. -/
instance sheafForget_isLeftAdjoint : (sheafForget Λ Y).IsLeftAdjoint :=
  (sheafForgetAdj Λ Y).isLeftAdjoint

/-- Forgetting to the underlying abelian sheaf is a right adjoint, to extension of scalars. -/
instance sheafForget_isRightAdjoint : (sheafForget Λ Y).IsRightAdjoint :=
  (Stacks.InjectiveAcyclic.sheafExtendScalarsAdj Y.smallEtaleTopology Λ :
    _ ⊣ sheafForget Λ Y).isRightAdjoint

/-- Forgetting to the underlying abelian sheaf is an additive functor. -/
instance sheafForget_additive : (sheafForget Λ Y).Additive where
  map_add := rfl

/-- **Forgetting to the underlying abelian sheaf is exact.** It is both a left and a right
adjoint. -/
instance preservesHomology_sheafForget : (sheafForget Λ Y).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

end Forget

/-! ### Cohomology of the global sections of an injective resolution -/

section Resolution

variable (Λ : Type r) [Ring Λ] (Y : Scheme.{u})

/-- Postcomposition with an isomorphism is injective on `Ext`. -/
lemma injective_comp_mk₀_hom {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C] {X A B : C}
    (e : A ≅ B) (n : ℕ) :
    Function.Injective ((Ext.mk₀ e.hom).postcomp X (add_zero n)) := by
  have key : ∀ z : Ext X A n,
      (z.comp (Ext.mk₀ e.hom) (add_zero n)).comp (Ext.mk₀ e.inv) (add_zero n) = z := by
    intro z
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, e.hom_inv_id, Ext.comp_mk₀_id]
  intro x y h
  change x.comp (Ext.mk₀ e.hom) (add_zero n) = y.comp (Ext.mk₀ e.hom) (add_zero n) at h
  rw [← key x, ← key y, h]

/-- An isomorphism of abelian groups gives an injective additive map. -/
lemma exists_injective_of_iso {A B : AddCommGrpCat.{w}} (e : A ≅ B) :
    ∃ φ : A →+ B, Function.Injective φ :=
  ⟨e.hom.hom, (AddCommGrpCat.mono_iff_injective _).1 inferInstance⟩

/-- Global sections of a sheaf of `Λ`-modules, read as an abelian group, are the sections over `Y`
of the underlying abelian sheaf. -/
def globalSectionsForgetIso :
    Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, r} Λ Y ⋙
        forgetAb.{u + 1} Λ ≅
      sheafForget Λ Y ⋙ Stacks.EtaleSections.sections.{r} Y :=
  Functor.isoWhiskerRight (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology _
    (Stacks.EtaleCohomology.etaleMkIdIsTerminal Y)) (forgetAb.{u + 1} Λ)

variable [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) r})]

/-- **The cohomology of the global sections of an injective resolution embeds into sheaf
cohomology.** For an injective resolution `G[0] ⟶ I` of a sheaf of `Λ`-modules by a complex
concentrated in degrees `≥ 0`, `Hⁿ⁺¹(Γ(Y, I))` embeds into `Hⁿ⁺¹(Y, G)` of the underlying abelian
sheaf. -/
lemma exists_injective_homology_sections (G : Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y)
    (I : CochainComplex (Stacks.EtaleCohomology.EtaleModules.{u, r} Λ Y) ℤ) [I.IsStrictlyGE 0]
    [∀ n, Injective (I.X n)]
    (ι : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G ⟶ I) [QuasiIso ι] (n : ℕ) :
    ∃ f : AddMonoidHom ((((Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, r} Λ Y ⋙
        forgetAb.{u + 1} Λ).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology
          ((n : ℤ) + 1))
        (Ext.{w} (Stacks.EtaleSections.zSheaf.{r} Y) ((sheafForget Λ Y).obj G) (n + 1)),
        Function.Injective f := by
  let T := ((sheafForget Λ Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have hIex (j : ℤ) (hj : j ≠ 0) : I.ExactAt j :=
    (exactAt_iff_of_quasiIsoAt ι j).1 (exactAt_single_obj _ _ _ _ hj)
  have hex : ∀ k : ℕ, k ≤ n → T.ExactAt (0 + 1 + k) := fun k _ =>
    (hIex _ (by omega)).map (sheafForget Λ Y)
  have hac : ∀ k : ℕ, k < n → ∀ q : ℕ,
      Subsingleton (Ext (Stacks.EtaleSections.zSheaf.{r} Y) (T.X (0 + k)) (q + 1)) := fun k _ q =>
    Stacks.InjectiveAcyclic.subsingleton_H_forget₂.{u, u + 1, u + 1, r, w} Y.smallEtaleTopology Λ
      (I.X (0 + k)) q
  obtain ⟨f, hf⟩ := StacksDraft.DimensionShift.exists_injective_homology_ext
    (Stacks.EtaleSections.zSheaf.{r} Y) n T 0 hex hac
  -- the cycles of `T` in degree `0` are the underlying abelian sheaf of `G`
  have hd : I.d ((ComplexShape.up ℤ).prev 0) 0 = 0 :=
    (I.isZero_of_isStrictlyGE 0 _ (by simp)).eq_of_src _ _
  let eG : I.cycles 0 ≅ G :=
    I.isoHomologyπ _ 0 rfl hd ≪≫ (asIso (homologyMap ι 0)).symm ≪≫
      HomologicalComplex.singleObjHomologySelfIso _ 0 G
  let eT : T.cycles 0 ≅ (sheafForget Λ Y).obj G :=
    (I.sc 0).mapCyclesIso (sheafForget Λ Y) ≪≫ (sheafForget Λ Y).mapIso eG
  -- the complex of global sections is the complex of morphisms out of `ℤ`
  let eC : ((Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, r} Λ Y ⋙
      forgetAb.{u + 1} Λ).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ≅
      StacksDraft.DimensionShift.homComplex (Stacks.EtaleSections.zSheaf.{r} Y) T :=
    (NatIso.mapHomologicalComplex (globalSectionsForgetIso Λ Y) (ComplexShape.up ℤ)).app I ≪≫
      (Functor.mapHomologicalComplexCompIso (F := sheafForget Λ Y)
        (G := Stacks.EtaleSections.sections.{r} Y) (Iso.refl _) (ComplexShape.up ℤ)).symm.app I ≪≫
      Stacks.EtaleSections.sectionsComplexIso.{r} Y T
  let e₁ := HomologicalComplex.homologyMapIso eC ((n : ℤ) + 1)
  let e₂ : (StacksDraft.DimensionShift.homComplex (Stacks.EtaleSections.zSheaf.{r} Y) T).homology
      ((n : ℤ) + 1) ≅
      (StacksDraft.DimensionShift.homComplex (Stacks.EtaleSections.zSheaf.{r} Y) T).homology
        (0 + 1 + (n : ℤ)) :=
    eqToIso (by rw [show (n : ℤ) + 1 = 0 + 1 + n by ring])
  obtain ⟨φ₁, h₁⟩ := exists_injective_of_iso.{max (u + 1) r} e₁
  obtain ⟨φ₂, h₂⟩ := exists_injective_of_iso.{max (u + 1) r} e₂
  exact ⟨((Ext.mk₀ eT.hom).postcomp (Stacks.EtaleSections.zSheaf.{r} Y)
    (add_zero (n + 1))).comp (f.comp (φ₂.comp φ₁)),
    (injective_comp_mk₀_hom.{w} eT (n + 1)).comp (hf.comp (h₂.comp h₁))⟩

end Resolution

end Stacks.EtaleResolution

end
