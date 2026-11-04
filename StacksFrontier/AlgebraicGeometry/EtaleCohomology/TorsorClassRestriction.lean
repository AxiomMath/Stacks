module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DenseSubsiteCohomology

/-!
# Restriction of the class of a torsor

Let `G : (C, J) ⥤ (D, K)` be a continuous functor of sites and `P ⊣ G^s` an exact left adjoint of
the restriction of abelian sheaves along `G` (for a morphism of schemes `π : X ⟶ Y` and
`G = Stacks.EtaleCohomology.smallEtaleBaseChange π`, `P = π^{-1}`). Let `T` be a torsor under an
abelian sheaf `H` on `C`, let `T'` be a torsor under an abelian sheaf `H'` on `D`, and let
`c : P H ⟶ H'` be a morphism. Suppose given a map of presheaves `α : T ⟶ G^s T'` equivariant along
the transpose `H ⟶ G^s H'` of `c`: this is how a pulled back torsor is recognised, e.g. the
torsor of local generators of the pullback of an invertible module, or the torsor of sections of
the base change of a finite étale torsor. Then **the class of `T'` in `H¹(D, H')` is the image of
the class of `T` in `H¹(C, H)` under `P` and `c`**:

`c_*(P([T])) = τ_*([T'])`, `τ : P ℤ_C ⟶ ℤ_D` the canonical comparison of constant sheaves.

For the small étale sites this reads `c_*(π^*[T]) = [T']` with `π^*` the restriction map
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap`
(`Stacks.EtaleCohomology.sheafHMap_etaleCohomologyRestrictionMap_torsorClass`).

The proof compares the extensions defining the two classes
(`Stacks.Cohomology.Torsors.torsorPushoutComplex`): `α` followed by the generator of the
extension of `T'` embeds `T` equivariantly into the restriction along `G` of the extension of
`T'`, so the extension of `T` maps to that restriction
(`Stacks.Cohomology.Torsors.torsorPushoutComparison`), and its transpose is a morphism from `P`
of the extension of `T` to the extension of `T'` which is `c` on the subobjects and `τ` on the
quotients. Naturality of extension classes concludes.

## Main results

* `Stacks.Cohomology.Torsors.extClass_torsorPushoutComplex_map_comp`: the general statement.
* `Stacks.EtaleCohomology.sheafHMap_etaleCohomologyRestrictionMap_torsorClass`: the statement for
  the small étale sites of a morphism of schemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w t v₁ u₁ v₂ u₂ u

namespace Stacks.Cohomology.Torsors

section General

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{t}]
  (G : C ⥤ D) [G.IsContinuous J K]
  {P : Sheaf J AddCommGrpCat.{t} ⥤ Sheaf K AddCommGrpCat.{t}}
  (adj : P ⊣ G.sheafPushforwardContinuous AddCommGrpCat.{t} J K)

/-- The sheafification unit of the constant presheaf `ℤ` on `D`, restricted to `C`: a map from
the constant presheaf `ℤ` on `C` to the sections of `G^s ℤ_D`. -/
def constantIntRestrictionUnit :
    (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶
      ((G.sheafPushforwardContinuous AddCommGrpCat.{t} J K).obj
        ((presheafToSheaf K AddCommGrpCat.{t}).obj
          ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))))).obj :=
  Functor.whiskerLeft G.op (toSheafify K
    ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))))

/-- The map `ℤ_C ⟶ G^s ℤ_D` of sheaves on `C` induced by
`Stacks.Cohomology.Torsors.constantIntRestrictionUnit`. -/
def constantIntRestriction :
    (constantSheaf J AddCommGrpCat.{t}).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶
      (G.sheafPushforwardContinuous AddCommGrpCat.{t} J K).obj
        ((presheafToSheaf K AddCommGrpCat.{t}).obj
          ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)))) :=
  ((sheafificationAdjunction J AddCommGrpCat.{t}).homEquiv _ _).symm
    (constantIntRestrictionUnit J K G)

/-- **The canonical comparison `P ℤ_C ⟶ ℤ_D` of constant integer sheaves**: the transpose of the
restriction to `C` of the sheafification unit of the constant presheaf `ℤ` on `D`. -/
def constantIntComparison :
    P.obj ((constantSheaf J AddCommGrpCat.{t}).obj (AddCommGrpCat.of (ULift.{t} ℤ))) ⟶
      (presheafToSheaf K AddCommGrpCat.{t}).obj
        ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))) :=
  (adj.homEquiv ((constantSheaf J AddCommGrpCat.{t}).obj (AddCommGrpCat.of (ULift.{t} ℤ))) _).symm
    (constantIntRestriction J K G)

/-- The comparison of constant integer sheaves, read through the constant sheaf adjunction at a
final object `T` of `C` followed by `P ⊣ G^s`: the constant section `1` over `G T`. -/
theorem comp_homEquiv_constantIntComparison {T : C} (hT : IsTerminal T) :
    ((constantSheafAdj J AddCommGrpCat.{t} hT).comp adj).homEquiv _ _
        (constantIntComparison J K G adj) =
      (constantIntRestrictionUnit J K G).app (op T) := by
  simp only [Adjunction.comp_homEquiv, Equiv.trans_apply, constantIntComparison]
  rw [Equiv.apply_symm_apply, Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply,
    constantIntRestriction]
  have h := ((sheafificationAdjunction J AddCommGrpCat.{t}).homEquiv
    ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)))
    ((G.sheafPushforwardContinuous AddCommGrpCat.{t} J K).obj
      ((presheafToSheaf K AddCommGrpCat.{t}).obj
        ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)))))).apply_symm_apply
    (constantIntRestrictionUnit J K G)
  rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at h
  exact congrArg (fun z => z.app (op T)) h

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] [HasExt.{w} (Sheaf K AddCommGrpCat.{t})]
  [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (HY : Sheaf J AddCommGrpCat.{t}) (HX : Sheaf K AddCommGrpCat.{t}) (c : P.obj HY ⟶ HX)
  (TY : AbelianTorsor HY) (TX : AbelianTorsor HX)
  (α : TY.1.presheaf ⟶ G.op ⋙ TX.1.presheaf)
  (hα : ∀ (U : Cᵒᵖ) (h : HY.obj.obj U) (s : TY.1.presheaf.obj U),
    α.app U (TY.1.act U (Multiplicative.ofAdd h) s) =
      TX.1.act (G.op.obj U)
        (Multiplicative.ofAdd ((adj.homEquiv HY HX c).hom.app U h)) (α.app U s))

/-- The morphism from `P` of the extension of `TY` to the extension of `TX`: `c` on the
subobjects and the comparison of constant sheaves on the quotients. -/
def torsorPushoutComplexMap :
    (torsorPushoutComplex HY TY).map P ⟶ torsorPushoutComplex HX TX := by
  let R := G.sheafPushforwardContinuous AddCommGrpCat.{t} J K
  haveI : R.IsRightAdjoint := adj.isRightAdjoint
  let T := torsorPushoutComplex HX TX
  let A : ShortComplex (Sheaf J AddCommGrpCat.{t}) :=
    ShortComplex.mk ((adj.homEquiv HY HX c) ≫ R.map T.f) (R.map T.g) (by
      rw [Category.assoc, ← R.map_comp, T.zero, R.map_zero, comp_zero])
  let q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ A.X₃.obj :=
    Functor.whiskerLeft G.op (toSheafify K
      ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))))
  let i : TY.1.presheaf ⟶ A.X₂.obj ⋙ forget AddCommGrpCat.{t} :=
    α ≫ Functor.whiskerLeft G.op (torsorPushoutGenerator HX TX)
  have hi : ∀ (U : Cᵒᵖ) (h : HY.obj.obj U) (s : TY.1.presheaf.obj U),
      let iU : TY.1.presheaf.obj U → A.X₂.obj.obj U := i.app U
      iU (TY.1.act U (Multiplicative.ofAdd h) s) = A.f.hom.app U h + iU s := by
    intro U h s
    change (torsorPushoutGenerator HX TX).app _
      (α.app U (TY.1.act U (Multiplicative.ofAdd h) s)) = _
    rw [hα]
    exact torsorPushoutGenerator_act HX TX _ _ _
  have hiFiber : ∀ (U : Cᵒᵖ) (s : TY.1.presheaf.obj U),
      A.g.hom.app U (i.app U s) = q.app U ⟨1⟩ := fun U s =>
    torsorPushoutGenerator_projection HX TX _ _
  let φ := torsorPushoutComparison A q TY i hi hiFiber
  exact
    { τ₁ := c
      τ₂ := (adj.homEquiv _ _).symm φ.τ₂
      τ₃ := (adj.homEquiv _ _).symm φ.τ₃
      comm₁₂ := by
        apply (adj.homEquiv _ _).injective
        dsimp only [ShortComplex.map_f]
        rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
        exact (Category.id_comp A.f).symm.trans φ.comm₁₂
      comm₂₃ := by
        apply (adj.homEquiv _ _).injective
        dsimp only [ShortComplex.map_g]
        rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_left, Equiv.apply_symm_apply,
          Equiv.apply_symm_apply]
        exact φ.comm₂₃ }

omit [PreservesFiniteLimits P] [PreservesFiniteColimits P] in
/-- The component of `torsorPushoutComplexMap` on the subobjects is `c`. -/
theorem torsorPushoutComplexMap_τ₁ :
    (torsorPushoutComplexMap J K G adj HY HX c TY TX α hα).τ₁ = c := rfl

omit [PreservesFiniteLimits P] [PreservesFiniteColimits P] in
/-- The component of `torsorPushoutComplexMap` on the quotients is the comparison
`constantIntComparison J K G adj` of constant sheaves. -/
theorem torsorPushoutComplexMap_τ₃ :
    (torsorPushoutComplexMap J K G adj HY HX c TY TX α hα).τ₃ = constantIntComparison J K G adj :=
  rfl

/-- **The class of a pulled back torsor.** If `α : TY ⟶ G^s TX` is equivariant along the
transpose of `c : P HY ⟶ HX`, then `P` carries the class of `TY` to a class whose image under `c`
is the image of the class of `TX` under the comparison of constant sheaves. -/
theorem extClass_torsorPushoutComplex_map_comp
    (α : TY.1.presheaf ⟶ G.op ⋙ TX.1.presheaf)
    (hα : ∀ (U : Cᵒᵖ) (h : HY.obj.obj U) (s : TY.1.presheaf.obj U),
      α.app U (TY.1.act U (Multiplicative.ofAdd h) s) =
        TX.1.act (G.op.obj U)
          (Multiplicative.ofAdd ((adj.homEquiv HY HX c).hom.app U h)) (α.app U s)) :
    ((torsorIsoClassesEquivH1 HY (Quotient.mk _ TY)).mapExactFunctor P).comp
        (Abelian.Ext.mk₀ c) (add_zero 1) =
      (Abelian.Ext.mk₀ (constantIntComparison J K G adj)).comp
        (torsorIsoClassesEquivH1 HX (Quotient.mk _ TX)) (zero_add 1) := by
  show ((torsorPushoutClass HY TY).mapExactFunctor P).comp _ _ =
    (Abelian.Ext.mk₀ _).comp (torsorPushoutClass HX TX) _
  have hS := torsorPushoutComplex_shortExact HY TY
  refine (congrArg (fun z => z.comp (Abelian.Ext.mk₀ c) (add_zero 1))
    (Abelian.Ext.mapExactFunctor_extClass P hS)).trans ?_
  exact ShortComplex.ShortExact.extClass_naturality (hS.map_of_exact P)
    (torsorPushoutComplex_shortExact HX TX)
    (torsorPushoutComplexMap J K G adj HY HX c TY TX α hα)

end General

section Restriction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{t}]
  (G : C ⥤ D) [G.IsContinuous J K]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] [HasExt.{w} (Sheaf K AddCommGrpCat.{t})]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{t} J K).Additive]
  [PreservesFiniteLimits (G.sheafPushforwardContinuous AddCommGrpCat.{t} J K)]
  [PreservesFiniteColimits (G.sheafPushforwardContinuous AddCommGrpCat.{t} J K)]

/-- **The class of a restricted torsor.** Let `G : (C, J) ⥤ (D, K)` be continuous with exact
restriction `G^s`, let `T` be a torsor under `H` on `D` and `T'` a torsor under `G^s H` on `C`
together with an equivariant bijection `T' ≅ G^s T` of presheaves. Then the class of `T'` is the
restriction of the class of `T`, read out of `ℤ_C` through `ℤ_C ⟶ G^s ℤ_D`. -/
theorem constantIntRestriction_comp_mapExactFunctor_torsorClass
    (H : Sheaf K AddCommGrpCat.{t}) (T : AbelianTorsor H)
    (T' : AbelianTorsor ((G.sheafPushforwardContinuous AddCommGrpCat.{t} J K).obj H))
    (β : T'.1.presheaf ⟶ G.op ⋙ T.1.presheaf) (hβ : ∀ U, Function.Bijective (β.app U))
    (hact : ∀ (U : Cᵒᵖ) (h : H.obj.obj (G.op.obj U)) (s : T'.1.presheaf.obj U),
      β.app U (T'.1.act U (Multiplicative.ofAdd h) s) =
        T.1.act (G.op.obj U) (Multiplicative.ofAdd h) (β.app U s)) :
    (Abelian.Ext.mk₀ (constantIntRestriction J K G)).comp
        ((torsorIsoClassesEquivH1 H (Quotient.mk _ T)).mapExactFunctor
          (G.sheafPushforwardContinuous AddCommGrpCat.{t} J K)) (zero_add 1) =
      torsorIsoClassesEquivH1 _ (Quotient.mk _ T') := by
  let R := G.sheafPushforwardContinuous AddCommGrpCat.{t} J K
  let S := torsorPushoutComplex H T
  have hS : S.ShortExact := torsorPushoutComplex_shortExact H T
  -- the fiber description of `T` inside its own extension
  have h0 : torsorIsoClassesEquivH1 H (Quotient.mk _ T) =
      (Abelian.Ext.mk₀ (((sheafificationAdjunction K AddCommGrpCat.{t}).homEquiv _ _).symm
        (constantUnit (J := K) (C := D)))).comp hS.extClass (zero_add 1) := by
    rw [constantUnit_adj_inverse, Abelian.Ext.mk₀_id_comp]
    rfl
  obtain ⟨i₀, hi₀, hinj₀, hfib₀⟩ :=
    (torsorIsoClassesEquivH1_eq_boundary_iff S hS (constantUnit (J := K) (C := D)) T).1 h0
  have key := (torsorIsoClassesEquivH1_eq_boundary_iff (S.map R) (hS.map_of_exact R)
    (constantIntRestrictionUnit J K G) T').2
    ⟨β ≫ Functor.whiskerLeft G.op i₀, fun U h s =>
        (congrArg (i₀.app (G.op.obj U)) (hact U h s)).trans (hi₀ _ h _),
      fun U => (hinj₀ _).comp (hβ U).injective,
      fun U x => by
        have h1 := hfib₀ (G.op.obj U) x
        rw [constantUnit_app_one] at h1
        refine h1.trans ⟨fun ⟨s, hs⟩ => ?_, fun ⟨s', hs'⟩ => ⟨β.app U s', hs'⟩⟩
        obtain ⟨s', rfl⟩ := (hβ U).surjective s
        exact ⟨s', hs⟩⟩
  refine Eq.trans ?_ key.symm
  exact congrArg (fun z => (Abelian.Ext.mk₀ (constantIntRestriction J K G)).comp z (zero_add 1))
    (Abelian.Ext.mapExactFunctor_extClass R hS)

end Restriction

section DenseSubsite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsDenseSubsite J K]
  [HasWeakSheafify J AddCommGrpCat.{t}] [HasWeakSheafify K AddCommGrpCat.{t}]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{t} J K).IsEquivalence]

/-- **The compatibility of the dense-subsite equivalence with sheafification is compatible with
the sheafification units**: restricting the sheafification unit of a presheaf `P` on `D` to `C`
is the sheafification unit of `G.op ⋙ P` followed by the compatibility. -/
theorem toSheafify_comp_sheafEquivSheafificationCompatibility_hom_app
    (P : Dᵒᵖ ⥤ AddCommGrpCat.{t}) :
    toSheafify J (G.op ⋙ P) ≫
        ((Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility J K G
          AddCommGrpCat.{t}).hom.app P).hom =
      Functor.whiskerLeft G.op (toSheafify K P) := by
  have := Functor.IsDenseSubsite.isCoverDense J K G
  have := Functor.IsDenseSubsite.isLocallyFull J K G
  let adjS := Functor.IsDenseSubsite.sheafifyAdjunctionOfIsEquivalence J K G AddCommGrpCat.{t}
  let lAU := adjS.leftAdjointUniq (sheafificationAdjunction K AddCommGrpCat.{t})
  let S := (Functor.IsDenseSubsite.sheafifyOfIsEquivalence J K G AddCommGrpCat.{t}).obj P
  have hu : adjS.unit.app P ≫ (lAU.hom.app P).hom = toSheafify K P := by
    have := Adjunction.unit_leftAdjointUniq_hom_app adjS
      (sheafificationAdjunction K AddCommGrpCat.{t}) P
    rwa [sheafificationAdjunction_unit_app] at this
  have hunit : (Functor.whiskerLeft G.op (adjS.unit.app P) : G.op ⋙ P ⟶ G.op ⋙ S.obj) =
      (toSheafify J (G.op ⋙ P) ≫
        ((Functor.IsDenseSubsite.sheafifyOfIsEquivalenceCompIso J K G AddCommGrpCat.{t}).inv.app
          P).hom : G.op ⋙ P ⟶ G.op ⋙ S.obj) := by
    simp only [adjS, Functor.IsDenseSubsite.sheafifyAdjunctionOfIsEquivalence,
      Adjunction.mkOfHomEquiv_unit_app, Functor.IsDenseSubsite.sheafifyHomEquivOfIsEquivalence]
    refine ((Functor.IsCoverDense.restrictHomEquivHom (G := G)).left_inv _).trans ?_
    rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app]
    congr 1
  have hsEC : ((Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility J K G
      AddCommGrpCat.{t}).hom.app P).hom =
      (((Functor.IsDenseSubsite.sheafifyOfIsEquivalenceCompIso J K G AddCommGrpCat.{t}).inv.app
          P).hom : _ ⟶ G.op ⋙ S.obj) ≫ Functor.whiskerLeft G.op (lAU.hom.app P).hom := by
    simp [Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility, lAU, adjS]
    rfl
  rw [hsEC]
  refine (Category.assoc _ _ _).symm.trans ((congrArg
    (fun x : G.op ⋙ P ⟶ G.op ⋙ S.obj => x ≫ Functor.whiskerLeft G.op (lAU.hom.app P).hom)
    hunit.symm).trans ?_)
  rw [← Functor.whiskerLeft_comp, hu]

end DenseSubsite

section DenseSubsiteClass


variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsDenseSubsite J K]
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{t}]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{t} J K).IsEquivalence]

/-- The comparison `ℤ_C ≅ G^s ℤ_D` of the dense-subsite cohomology comparison is the map
`Stacks.Cohomology.Torsors.constantIntRestriction`. -/
theorem constantSheafRestrictionIso_inv_app_eq_constantIntRestriction :
    ((Stacks.Cohomology.DenseSubsite.constantSheafRestrictionIso.{t, u₁, v₁, u₂, v₂} J K G).app
      (AddCommGrpCat.of (ULift.{t} ℤ))).inv =
      constantIntRestriction J K G :=
  ((sheafificationAdjunction J AddCommGrpCat.{t}).homEquiv _ _).eq_symm_apply.2
    ((Adjunction.homEquiv_unit _ _ _ _).trans
      (toSheafify_comp_sheafEquivSheafificationCompatibility_hom_app J K G
        ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)))))

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] [HasExt.{w} (Sheaf K AddCommGrpCat.{t})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{t})]

/-- **The dense-subsite comparison of `H¹` sends the class of a torsor to the class of its
restriction** (`Stacks.Cohomology.DenseSubsite.hAddEquiv`, Tag 00XU), given a torsor `T'` on the
subsite with an equivariant bijection `T' ≅ G^s T`. -/
theorem hAddEquiv_torsorClass (H : Sheaf K AddCommGrpCat.{t}) (T : AbelianTorsor H)
    (T' : AbelianTorsor ((G.sheafPushforwardContinuous AddCommGrpCat.{t} J K).obj H))
    (β : T'.1.presheaf ⟶ G.op ⋙ T.1.presheaf) (hβ : ∀ U, Function.Bijective (β.app U))
    (hact : ∀ (U : Cᵒᵖ) (h : H.obj.obj (G.op.obj U)) (s : T'.1.presheaf.obj U),
      β.app U (T'.1.act U (Multiplicative.ofAdd h) s) =
        T.1.act (G.op.obj U) (Multiplicative.ofAdd h) (β.app U s)) :
    Stacks.Cohomology.DenseSubsite.hAddEquiv J K G H 1
        (torsorIsoClassesEquivH1 H (Quotient.mk _ T)) =
      torsorIsoClassesEquivH1 _ (Quotient.mk _ T') := by
  refine Eq.trans ?_
    (constantIntRestriction_comp_mapExactFunctor_torsorClass J K G H T T' β hβ hact)
  show (Abelian.Ext.mk₀
    ((Stacks.Cohomology.DenseSubsite.constantSheafRestrictionIso.{t, u₁, v₁, u₂, v₂}
      J K G).app (AddCommGrpCat.of (ULift.{t} ℤ))).inv).comp
      ((torsorIsoClassesEquivH1 H (Quotient.mk _ T)).mapExactFunctor
        (G.sheafPushforwardContinuous AddCommGrpCat.{t} J K)) (zero_add 1) = _
  rw [constantSheafRestrictionIso_inv_app_eq_constantIntRestriction]
  rfl

end DenseSubsiteClass

end Stacks.Cohomology.Torsors

namespace Stacks.EtaleCohomology

open Stacks.Cohomology.Torsors

variable {X Y : Scheme.{u}} (π : X ⟶ Y)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₁})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₁})]

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₁})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₁})] in
/-- On the small étale sites, the comparison of constant integer sheaves attached to the
inverse image adjunction is the canonical identification `π^{-1} ℤ_Y ≅ ℤ_X`. -/
theorem constantIntComparison_etaleAbelianInverseImageDirectImageAdj :
    ((etaleAbelianInverseImageConstantIso.{u, v₁} π).app
        (AddCommGrpCat.of (ULift.{max (u + 1) v₁} ℤ))).inv ≫
      constantIntComparison (P := etaleAbelianInverseImage.{u, v₁} π)
        Y.smallEtaleTopology X.smallEtaleTopology (smallEtaleBaseChange π)
        (etaleAbelianInverseImageDirectImageAdj.{u, v₁} π) = 𝟙 _ := by
  have h : constantIntComparison (P := etaleAbelianInverseImage.{u, v₁} π)
      Y.smallEtaleTopology X.smallEtaleTopology (smallEtaleBaseChange π)
      (etaleAbelianInverseImageDirectImageAdj.{u, v₁} π) =
      ((etaleAbelianInverseImageConstantIso.{u, v₁} π).app
        (AddCommGrpCat.of (ULift.{max (u + 1) v₁} ℤ))).hom := by
    apply (((constantSheafAdj _ _ (etaleSiteTerminalIsTerminal Y)).comp
      (etaleAbelianInverseImageDirectImageAdj.{u, v₁} π)).homEquiv _ _).injective
    exact (comp_homEquiv_constantIntComparison Y.smallEtaleTopology X.smallEtaleTopology
      (smallEtaleBaseChange π) (etaleAbelianInverseImageDirectImageAdj.{u, v₁} π)
      (etaleSiteTerminalIsTerminal Y)).trans
      (homEquiv_etaleAbelianInverseImageConstantIso.{u, v₁} π
        (AddCommGrpCat.of (ULift.{max (u + 1) v₁} ℤ))).symm
  exact (congrArg (fun z => ((etaleAbelianInverseImageConstantIso.{u, v₁} π).app
    (AddCommGrpCat.of (ULift.{max (u + 1) v₁} ℤ))).inv ≫ z) h).trans (Iso.inv_hom_id _)

/-- **The restriction of the class of a torsor along a morphism of schemes.** Let `π : X ⟶ Y`,
let `TY` be a torsor under an abelian sheaf `HY` on `Y_étale` and `TX` a torsor under `HX` on
`X_étale`, let `c : π^{-1} HY ⟶ HX`, and let `α : TY ⟶ π_* TX` be equivariant along the transpose
`HY ⟶ π_* HX` of `c`. Then the restriction of the class of `TY`, pushed along `c`, is the class
of `TX`: `c_*(π^*[TY]) = [TX]` in `H¹(X_étale, HX)`. -/
theorem sheafHMap_etaleCohomologyRestrictionMap_torsorClass
    (HY : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₁})
    (HX : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v₁})
    (c : (etaleAbelianInverseImage.{u, v₁} π).obj HY ⟶ HX)
    (TY : AbelianTorsor HY) (TX : AbelianTorsor HX)
    (α : TY.1.presheaf ⟶ (smallEtaleBaseChange π).op ⋙ TX.1.presheaf)
    (hα : ∀ (U : (Y.Etale)ᵒᵖ) (h : HY.obj.obj U) (s : TY.1.presheaf.obj U),
      α.app U (TY.1.act U (Multiplicative.ofAdd h) s) =
        TX.1.act ((smallEtaleBaseChange π).op.obj U)
          (Multiplicative.ofAdd
            (((etaleAbelianInverseImageDirectImageAdj.{u, v₁} π).homEquiv HY HX c).hom.app U h))
          (α.app U s)) :
    Sheaf.H.map c 1 (etaleCohomologyRestrictionMap.{u, v₁, w} π HY 1
        (torsorIsoClassesEquivH1 HY (Quotient.mk _ TY))) =
      torsorIsoClassesEquivH1 HX (Quotient.mk _ TX) := by
  rw [Sheaf.H.map_apply, etaleCohomologyRestrictionMap_apply,
    Abelian.Ext.comp_assoc_of_third_deg_zero,
    extClass_torsorPushoutComplex_map_comp Y.smallEtaleTopology X.smallEtaleTopology
      (smallEtaleBaseChange π) (etaleAbelianInverseImageDirectImageAdj.{u, v₁} π)
      HY HX c TY TX α hα]
  refine (Abelian.Ext.mk₀_comp_mk₀_assoc _ _ _).trans ?_
  rw [constantIntComparison_etaleAbelianInverseImageDirectImageAdj]
  exact Abelian.Ext.mk₀_id_comp _

end Stacks.EtaleCohomology

end
